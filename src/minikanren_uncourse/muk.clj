; microKanren in clojure
;
; based on 2013 scheme workshop paper by Jason Hemann and Dan Friedman
; github.com/jasonhemann/microKanren

(ns minikanren-uncourse.muk
  (:refer-clojure :exclude [==])
  (:require [clojure.walk]))


; =====================================================================
; Data structure and accessor definitions
; =====================================================================
;
; jlk: I'm going to use a map with a key that specifies its id
(defn lvar [i] {:lvarid i})
(defn lvar? [l]
  (and (map? l) (= 1 (count (keys l))) (contains? l :lvarid)))

(defn lvar=? [a b]
  (and (lvar? a)
       (lvar? b)
       (= (:lvarid a) (:lvarid b))))

(declare check-constraints)

(defn constraint-store 
  ([] (constraint-store {} [] 0))
  ([s]
   {:substitution s
    :disequalities []
    :counter 0 })
  ([s d]
   {:substitution s
    :disequalities d
    :counter 0 })
  ([s d c]
   {:substitution s
    :disequalities d
    :counter c }))

(defn constraint-store? [c]
  (and (map? c) 
       (contains? c :substitution) 
       (contains? c :disequalities)))

(defn substitution [c] (:substitution c))
(defn disequalities [c] (:disequalities c))
(def counter :counter) ; another way to write the above

(defn add-diseq [c diseq-constraint]
  (constraint-store
    (substitution c)
    (conj (disequalities c) diseq-constraint)))

(defn set-substitution [c s]
  {:pre [(constraint-store? c)]}
  (assoc c :substitution s))

(defn set-disequalities [c d]
  {:pre [(constraint-store? c)]}
  (assoc c :disequalities d))

(defn increment-counter [c]
  {:pre [(constraint-store? c)]}
  (assoc c :counter (inc (:counter c))))


(defn add-predicate-constraint [c k x]
  {:pre [(constraint-store? c) (lvar? x)]}
  (assoc c k (conj (get c k) x)))

(defn remove-predicate-constraint [c k x]
  {:pre [(constraint-store? c) (lvar? x)]}
  (let [new-sc (filter #(not (lvar=? % x)) (k c))]
    (assoc c k new-sc)))

(defn conso-constraint? [x]
  (and (map? x) (contains? x :h) (contains? x :t) (contains? x :l)))

(defn add-conso-constraint [c h t l]
  {:pre [(constraint-store? c)]}
  (assoc c :consos (conj (:consos c) {:h h :t t :l l})))

(defn remove-conso-constraint [c h t l]
  (assoc c :consos (filter #(or (not (= (:h %) h))
                                (not (= (:t %) t))
                                (not (= (:l %) l))) 
                           (:consos c))))

(defn consos
  [c]
  {:pre [(constraint-store? c)]}
  (:consos c))

(defn ext-s 
  "extend a substitution with the pair (u . v) if it doesn't violate any
  other constraints"
  [u v c]
  (let [new-c (assoc-in c [:substitution u] v)]
    ; we can shut off disequality specific functionality by just returning new-c here
    (check-constraints new-c)))

;; ---------------------------------------------
;; Stream definition handling utilities
;; ---------------------------------------------
;; ================================================================
; **** mplus and bind control the search strategy used in minikanren
; - depth first, interleaving breadth first, etc.
; - miniKanren paper talks about these trade offs and how to get 
;   different search strategies
; ================================================================
; Stream:
;   ()              mature / empty stream
;   (s/c . stream)  mature stream
;   procedure       immature stream (λ () body) i.e. thunk
;                     - this delays evaluation of the body and introduces laziness

; 
; since clojure doesn't support improper tails in cons cells, we require a little
; finagling to make this work 

; unify deals with substitutions or false
; our logic programming deals with streams of answers, so failure is
; represented as an empty list (instead of false)
(def mzero []) 

; constructs a stream with a single element - take our constraint into our
; "stream of answers" monad
(defn unit [c] [c])

(defn cons-stream [h t]
  (if (fn? t) (cons h [t]) (cons h t)))

(defn car-stream [s]
  (first s))

(defn cdr-stream [s]
  (let [res (rest s)]
    (if (and (= (count res) 1) 
             (fn? (first res)))
      (first res)
      res)))

(defn nil-stream? [s]
  (and (not (fn? s)) (empty? s)))

(defn pull [s]
  (if (fn? s) (pull (s)) s))

(defn take-n [n s]
  (if (zero? n) mzero
    (let [s (pull s)]
      (if (nil-stream? s) mzero
        (cons-stream (car-stream s) (take-n (dec n) (cdr-stream s)))))))

(defn take-all [s]
  (let [s (pull s)]
    (if (nil-stream? s) mzero
        (cons-stream (car-stream s) (take-all (cdr-stream s))))))

(defn mplus
  [s1 s2] ; two stream monads
  (cond
    (nil-stream? s1) s2
    (fn? s1) (fn [] (mplus s2 (s1)))
    :else (cons-stream (car-stream s1) (mplus (cdr-stream s1) s2))))

(defn bind 
  "flatmap/mapcat the goal g over the stream s"
  [s g] ; stream and a goal
  (cond
    (nil-stream? s) mzero
    (fn? s) (fn [] (bind (s) g))
    :else (mplus (g (car-stream s)) (bind (cdr-stream s) g))))


;; ---------------------------------------------
;; Unification implementation
;; ---------------------------------------------
; (walk 5 `((,x . 7))) => 5
; (walk y `((,x . 7))) => y
; (walk `(,x ,y) `((,x . 7) (,y . 6))) => `(,x . ,y)
(defn walk 
  "walk term t in substitution s"
  [t c]
  {:pre [(constraint-store? c)]}
  (let [s (substitution c)]
    (cond
      (lvar? t) 
        (let [pr (get s t)] ; note - using clojure map instead of association list
          (if pr
            (recur pr c)
            t)) ; not found, return the term
      :else t))); if the term is not a variable just return the term

(defn unifiable-collection?
  [s]
  (or (seq? s) (list? s) (vector? s))) ; TODO: worry about strings?


; if unification succeeds, it returns a substitution (map) that would make the
; two terms equal
; this unifier only handles lvars, pairs, and things that are comparable with ==,
;   using a  typeclass/protocol based approach for the final comparison allows
;   for an extensible unifier
(defn unify 
  [u v c]
  {:pre [(constraint-store? c)]}
  (let [u (walk u c) ; note shadowing
        v (walk v c)]
    (cond
      ; both u and v walk to the same variable, just return s without changes
      (and (lvar? u) (lvar? v) (lvar=? u v)) 
        c
      (lvar? u) ; either v is not a variable, or it is but isn't the same as u
        (ext-s u v c) ; we're missing the occurs? check to make sure that you're not unifying a variable with a term that contains that same variable
      (lvar? v) ; we know that u is not a variable
        (ext-s v u c)
      (and (unifiable-collection? u) (unifiable-collection? v)) ; pairwise unification on the cars and cdrs
        (let [c (unify (first u) (first v) c)]
          (and c (unify (next u) (next v) c))) ; note - using and as an if statement
      :else 
      (and (= u v) c)))) ; use host language equivalence to test if these values are the same


;; ---------------------------------------------
;; Disequality handling
;; ---------------------------------------------
(defn diff-substitutions
  "returns any constraints that have been added in b that are not in a"
  [a b]
  {:pre [(constraint-store? a) (constraint-store? b)]}
  (apply dissoc (substitution b) (keys (substitution a))))

(defn reconstitute-disequality
  [constraint]
  {:pre [(map? constraint)]}
  [(keys constraint) (vals constraint)])

(defn check-diseq
  "validate, and possibly modify, a single disequality constraint against the specified substitution"
  [s de]
  (let [[u v] (reconstitute-disequality de)
        res (unify u v (constraint-store s))]
    (cond 
      (= res false) de
      (= res (constraint-store s)) false
      :else (diff-substitutions (constraint-store s) res))))


(defn check-disequalities
  "Validate, and possibly modify, the disequalities in the constraint store based on the substitution"
  [c]
  {:pre [(constraint-store? c)]}
  (let [new-d (reduce 
                #(if (not %2) 
                   (reduced false) ; as soon as any disequality constraint fails (maps to false), the whole thing fails
                   (conj %1 %2)) ; otherwise add the (potentially) updated disequality constraint to the list
                [] 
                ; check each disequality against the new substitution to make sure they aren't violated
                (map #(check-diseq (substitution c) %) (disequalities c)))]
    (if new-d
      (set-disequalities c new-d)
      false ))) ; disequality constraints failed with this unification


; try to implement disequality in micro-kanren as described below
(defn diseq
  [u v c]
  {:pre [(constraint-store? c)]}
  (let [unify-result (unify u v c)]
    (cond 
        ; since unification fails, these two values cannot be equal, 
        ; so this disequality is always true and no new constraint is required
      (= unify-result false) c 
        ; since the unification succeeds without extending the substitution, 
        ; we know the values are already equal, and therefore this disequality
        ; constraint cannot be met
      (= unify-result c) false 
        ; unification succeeds, but the substitution has been extended, 
        ; revealing the disequality constraints we need to add.
        ; Take out all keys from unify-result that were already in the substitution, getting
        ; only those extentions added during this unification
        ; TODO: faster implementation?
      :else 
        (add-diseq c (diff-substitutions c unify-result)))))

;
;; ---------------------------------------------
;; Core Constraint implementations
;; ---------------------------------------------

; this is a constructor function that returns a function
; delaying unification - we don't know which substitution to unify
; them in at the point the constraint is defined.
; the s/c that is provided to the function that is returned is the
; substitution to be used in unifying the arguments.
; In some sense == is the interface between unify and the rest of minikanren
(defn == 
  "definition of the goal constructor for using unification"
  [u v]
  (fn [c] ; s/c in the paper - substitution and a counter
    (let [c (unify u v c)]
      (if c (unit c) mzero)))) ; if it succeeded, return the new constraint, otherwise fail

(defn != 
  "goal constructor for disequality constriants"
  [u v]
  (fn [c]
    (let [c (diseq u v c)]
      (if c (unit c) mzero))))

(defn call-fresh 
  "goal constructor that creates a new logic variable and passes it to another goal constructor"
  [f]
  (fn [c] ; s/c in paper - 
    (let [ix (counter c)]
      ; invoke f with a new variable (this is the fresh)
      ; f returns a goal (see above)
      ; then invoke that goal with the constraint-store after incrementing its counter
      ((f (lvar ix)) (increment-counter c)))))

(defn predicate-constraint [cs-key pred]
  (fn [x] ; goal constructor
    (fn [c] ; goal
      (let [x (walk x c)]
        (cond 
          (lvar? x) (unit (add-predicate-constraint c cs-key x))
          (pred x) (unit c)
          :else mzero)))))

(defn check-predicate-constraint [cs-key pred]
  (fn [c]
  (reduce
    (fn [res v]
      (let [v* (walk v c)] ; we need the var in the second case below so we don't want to shadow the variable name
        (cond 
          (lvar? v*) c ; still not bound, nothing changes
          (pred v*) (remove-predicate-constraint c cs-key v)
          :else (reduced false))))
    c
    (get c cs-key))))

(def symbolo (predicate-constraint :symbols symbol?))
(def check-symbol-constraints (check-predicate-constraint :symbols symbol?))
;
; TODO: symbolo interaction?
(def numbero (predicate-constraint :numbers number?))
(def check-number-constraints (check-predicate-constraint :numbers number?))

; no idea what I'm doing - just plunging ahead and seeing what happens
(defn conso
  "goal constructor that yields a goal that constrains three logic variables to forming a cons-cell"
  [h t x]
  (fn [c] ; goal function
    (let [h (walk h c)
          t (walk t c)
          x (walk x c)]
      (cond
        ; case 0 - x or t is bound but not a collection - fail
        (or (and (not (lvar? t)) (not (unifiable-collection? t)))
            (and (not (lvar? x)) (not (unifiable-collection? x))))
          mzero

        ; case 1 - all variables are bound, does the cons hold?
        (and (not (lvar? h)) (not (lvar? t)) (not (lvar? x)) (unifiable-collection? t) (unifiable-collection? x))
          (if (= x (cons h t)) (unit c) mzero)
          

        ; case 2 - only head is not bound, so we can bind it now (or fail)
        (and (lvar? h) (not (lvar? t)) (not (lvar? x)) (unifiable-collection? t) (unifiable-collection? x))
          (if (= (rest x) t) 
            (unit (ext-s h (first x) c))
            mzero)

        ; case 3 - only tails is not bound, so we can bind it
         (and (not (lvar? h)) (lvar? t) (not (lvar? x)) (unifiable-collection? x))
          (if (= (first x) h) 
            (unit (ext-s t (rest x) c))
            mzero)

        ; case 4 - only the output list is not bound, so bind it
        (and (not (lvar? h)) (not (lvar? t)) (lvar? x) (unifiable-collection? t))
            (unit (ext-s x (cons h t) c))

        ; case 5 - at least two are unbound so we need to add a new constraint to the store
        :else 
          (unit (add-conso-constraint c h t x))))))

; TODO: absento
; TODO: support lists (conso, resto)
; TODO: run relational interpreter on top of this microkanren implementation

(defn validate-conso-constraint
  "validates that this single conso constraint is valid with respect to the specified constraint store's substitution"
  [c constraint]
  {:pre [(constraint-store? c) (conso-constraint? constraint)]}
  (let [{h :h t :t l :l} constraint
        res (first ((conso h t l) c))] ; am I always guaranteed to get 1 result here?  I think I am
    (if (nil? res) false ; in this case the conso failed and therefore first returned nil
      (cond
        ; case 1 - failed to unify with these substitutions, so it is not valid
        (= mzero res) false
        ; case 2 - constraint store is unchanged - still valid
        (= c res) c
        ; case 3 - substitution is extended - still valid, but we have more information and things can be updated
        (> (count (substitution res)) (count (substitution c)))
          ; now we can use the new substitution and remove this constraint
          (remove-conso-constraint res h t l)
        ; case 4 - conso-constraint added - nothing has changed, return the original c
        (> (count (consos res)) (count (consos c)))
          c))))

(defn check-conso-constraints [c]
  {:pre [(constraint-store? c)]}
  (reduce 
    (fn [cs constraint]
      (or (validate-conso-constraint cs constraint) (reduced false)))
    c
    (consos c)))

(defn check-wrapper 
  [c f]
  (if (= false c) c (f c)))

(defn check-constraints 
  "validate that the substitution in the specified constraint store don't violate any of the
  additional constraints"
  [c]
  {:pre [(constraint-store? c)]}
  (if (not c) c ; don't need to check more constraints if we've already failed
    ; TODO: note this is now a kind of reduce with early escape on false
    (-> c
        ; TODO: are all of these them same shape? reduces until a false is found?  Should I move that into this controller function?
        (check-wrapper check-disequalities)
        (check-wrapper check-symbol-constraints)
        (check-wrapper check-number-constraints)
        (check-wrapper check-conso-constraints)
        )))

;; ---------------------------------------------
;; goal combinators - conjunction, disjunction
;; ---------------------------------------------
; disj and conj basically manipulate multiple streams
; pre-pending the "mu" to prevent name collision with clojure's disj and conj
; we don't change the definition of conj/disj,
; if we want to change the way the search works, we change the definition of
; our stream monad in mplus and bind
(defn μdisj [g1 g2]
  "goal constructor whose goal will succeed if either supplied goal succeeds"
  (fn [c]
    (mplus (g1 c) (g2 c))))

(defn μconj [g1 g2]
  "goal constructor whose goal will succeed if both goals succeed"
  (fn [c]
    (bind (g1 c) g2)))
 
;; ---------------------------------------------
;; Macros to recover miniKanren functionality
;; ---------------------------------------------
; inverse eta-delay macro
(defmacro zzz [g]
  `(fn [c#] (fn [] (~g c#))))


(defmacro μdisj+ [& goals]
  (cond 
    (= (count goals) 1) (first goals)
    (= (count goals) 2) `(μdisj ~(first goals) ~(second goals))
    :else `(μdisj ~(first goals) (μdisj+ ~@(rest goals)))))

(defmacro μconj+ [& goals]
  (cond 
    (= (count goals) 1) (first goals)
    (= (count goals) 2) `(μconj ~(first goals) ~(second goals))
    :else `(μconj ~(first goals) (μconj+ ~@(rest goals)))))


(defmacro conde [& lists-of-goals]
  (concat `(μdisj+)
     (map (fn [list-of-goals]
             `(μconj+ ~@list-of-goals))
           lists-of-goals)) )

(defmacro fresh+
  "introduces multiple variables to a single goal"
  [vs g]
  `(call-fresh 
    (fn [~(first vs)]
      ~(if (empty? (rest vs)) g `(fresh+ ~(rest vs) ~g)))))

(defmacro fresh
  "introduce multiple freshes and a conjunction of multiple clauses as in minikanren"
  [vs & goals]
  `(fresh+ ~vs 
           (μconj+ ~@goals)))

(defn call-goal 
  "simple run - not full reification, just taking away need for constraint-store etc."
  [g]
  (g (constraint-store)))

;; ---------------------------------------------
;; Reification
;; ---------------------------------------------
(defn reify-name
  "returns the display name for the logic variable with counter n"
  [n]
  (symbol (str "_." n)))

(defn reify-s 
  "bind any unbound lvars to a descriptive value,
  or recurse into its values if it is a collection"
  [v c]
  (let [v (walk v c)]
    (cond
      (lvar? v) 
        (ext-s v (reify-name (count (substitution c))) c) ; TODO: I think ext-s is safe here
      (unifiable-collection? v) 
        (reify-s (rest v) ; reify the rest of the collection against the updated substitution
                 (reify-s (first v) c)) ; returns a substitution with v in it
      :else c)))

(defn walk*
  "deeply walk the substitution - including the members of any collection that is the value of an lvar"
  [v c]
  (let [v (walk v c)] 
    (cond
      (lvar? v) v
      (unifiable-collection? v)
        (cons (walk* (first v) c) 
              (walk* (rest v) c))
      :else v)))

(defn μreify
  "reify the value v with respect to c"
  [v c]
  {:pre [(constraint-store? c)]}
  (let [v (walk v c)] ; lookup the value of the first lvar in the substitution
    (walk* v (reify-s v (constraint-store)))))

(defn reify-1st
  [c]
  (μreify (lvar 0) c))

(defn reify-all
  [c]
  (map #(μreify (lvar %) c) (range (:counter c))))


;(map reify-1st (take 2 (call-goal (fresh [x y] (μdisj+ (== x 5) (== x 6) (== x y) (== y 7))))))
;(print (map reify-all (take 1 (call-goal (fresh [x y z] (== [x y z] [y z x]))))))
