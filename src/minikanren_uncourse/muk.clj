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

(declare check-disequalities)

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
  (and (map? c) (contains? c :substitution) (contains? c :disequalities)))

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


(defn ext-s 
  "extend a substitution with the pair (u . v) if it doesn't violate any
  other constraints"
  [u v c]
  (let [new-c (assoc-in c [:substitution u] v)]
    ; we can shut off disequality specific functionality by just returning new-c here
    (check-disequalities new-c)))

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

; TODO: can I only ever have disequality constraints that are either one term (directly) or two terms (pair comparison)?
; I think so since these are the only things we can unify with logic variables
; but note that any extension to unification/disequality constraints will need to be reflected here
(defn reconstitute-disequality
  [constraint]
  (condp = (count constraint) ; need to determine if this represents a unified pair, or a just a single logic variable
    1 (first constraint) ; not a pair, just returning two results
    2 (let [[k1 v1] (first constraint)
            [k2 v2] (second constraint)]
              [[k1 k2] [v1 v2]])
    (throw (IllegalArgumentException. "Only supports disequalities with 1 or two terms"))))

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

; TODO: symbolo
; TODO: numbero

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

(defn srun 
  "simple run - not full reification, just taking away need for constraint-store etc."
  [g]
  (g (constraint-store)))

;; ---------------------------------------------
;; Reification
;; ---------------------------------------------
; TODO: reificiation

; "The scarier sounding the term, the easier it is to understand" - Dan Friedman
; inverse-eta delay
;   ex: (add1 5) => 6
;   add1 is equivalent to (fn [n] (add1 n))
;   add1 -> (fn [n] (add1 n)) is an "inverse-eta" expansion
;   (fn [n] (add1 n)) -> add1 is an "eta" reduction (there are some restrictions)

(comment

  (defn fives [x] ; goal constructor
    (μdisj ; goal constructor takes two goals
      (== x 5)
      (fn [c] ; goal - returns a lazy sequence of solutions
        (fn [] ((fives x) c)))))

  (defn fives [x]
    (μdisj
      (== x 5)
      (zzz (fives x))))

  (defn sixes [x] ; goal constructor
    (μdisj ; goal constructor takes two goals
      (== x 6)
      (fn [c] ; goal - returns a lazy sequence of solutions
        (fn [] ((sixes x) c)))))

  ; lift version, still fair
  (defn fives [x]
    (fn [c] ; goal constructor
      (fn [] ; immature stream
        ((μdisj ; disj goal constructor returns goal we execute in c
           (== x 5)
           (fives x)) c))))

  (defn sixes [x]
    (μdisj 
      (== x 6)
      (zzz (sixes x))))

  (defn fives-and-sixes
    [x]
    (μdisj (fives x) (sixes x)))

  (take-n 3 ((call-fresh fives) (constraint-store)))
  (take-n 3 ((call-fresh sixes) (constraint-store)))
  (doseq [i (take-n 10 ((call-fresh fives-and-sixes) (constraint-store)))]
    (println i))
)
  
