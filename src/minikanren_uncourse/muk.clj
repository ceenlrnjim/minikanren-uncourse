; microKanren in clojure
;
; based on 2013 scheme workshop paper by Jason Hemann and Dan Friedman
; github.com/jasonhemann/microKanren

(ns minikanren-uncourse.muk
  (:refer-clojure :exclude [==])
  (:require [clojure.walk])
  )

; minikanren uncourse #7 - 
;
; concepts in mini-kanren like implementation
; 1) logic variables 
;    ability to introduce (lexically scoped) fresh logic variables (fresh)
; 2) unify terms (==)
; 3) Ability to create terms (numbers, pairs, etc.)
; 4) conjuntion (and)  (fresh/conde/run) & disjunction (or) (between conde clauses)
; 5) interface operator for the host language (run*)
; 6) display answers nicely (reification)
;
; Simplifying the language/implementation
;   - miniKanren was designed to look like scheme
;   - conde is a disjunction (or) of conjunctions (ands) - each goal in a conde clause must pass
;   - under the hood each conde conjunction is actually a (fresh () g1 g2 g3) so conde is really an or of a bunch of fresh-es
;   - fresh also conflates two things - introducing logic values and conjunction
;   - run also combines both interface and fresh

; binary conjunction (and)
; binary disjunction (or)
; creation of a single fresh logic variables
; scoping of a single logic variables (use lambda to handle scoping - pass a fresh logic variable (anonymous) to a lambda to bind it to the variable name)
;   ((λ (x) (== x 5)) (make-logic-var 1)) - counter variable used so we can tell the difference between different logic variables
; unification
; ==
;
; defer:
; --------------------------------------------
; interface/query operator
; reifying answers
;
; We're aiming for a very simple language to implement, even if it means the language is less friendly to read/write
;
; (fresh (x y)
;   (== 6 x)
;   (== 5 x))
;
;   substitution (unification)
;     start out with the empty substitution (empty list)
;     after successful unification (== 6 x), extend the substitution ((x . 6)) (using association list) - similar to an environment
;     when we get to (== 5 x), lookup up 6 in substitution - we see that it is set to 6, which is equivalent to (== 5 6) which fails
;     LHS of substitution is always a logic variable
;     Substitution is different from an environment because we can map variables to other variables (== x y) -> ((x . y)) or ((y . x)), or to lists of variables = we can have variables on the RHS
;     Substitution maps logic variables to terms
; 
;     This representation is caused a Triangular Substitution
;       (fresh (x y z)
;           ; empty substitution here ()
;         (== x y)          
;           ; now ((x . y))
;         (== x 6)
;           ; now ((y . 6) (x . y)) - see property below
;            
;     Property of our subsitution is that a logic variable appears on the left hand side of a substitution at most once
;       This is an important assumption our code will make
;
;     So our lookups can require multiple steps - if x maps to a variable, look up that variable again to see if it is mapped to another value, but this makes
;       extending the substitution very cheap, though lookups are more expensive
;         
;
;   constraint store (more general notion) and substitution representations drive a lot of the design and constraints of the system
;
;   Triangular vs. idempotent substitution - apply-subst

; =====================================================================
; Data structure and accessor definitions
; =====================================================================
; variable interface
; (lvar 0) - constructor, makes a new variable
; (lvar? t) - true or false
; (lvar=? v1 v2) - true or false
(declare lvar)
(declare lvar?)
(declare lvar=?)
(declare check-disequalities)


(defn constraint-store 
  ( [] (constraint-store {} [] 0))
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
    :counter c })
  
  )

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

; =====================================================================


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
  (or (seq? s) (list? s) (vector? s)) ; TODO: worry about strings?
  )


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

(comment
  (unify [(lvar 0) (lvar 1)] [5 6] (constraint-store))
  (unify [(lvar 0)] [5] (constraint-store))
  (unify (list (lvar 1)) (list 6) (unify [(lvar 0)] [5] (constraint-store)))
  )


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

;   ------------------------------------------------------------------
;   Implementing disequality in terms of unify
;   ------------------------------------------------------------------
; unify can return one of three values
;   1) false - failure to unify => there is no way to make u and v equal
;   2) s - the same s we passed in, u and v are already equal so we're not extending the substitution
;   3) s^ - updated subsitution - non-empty extension to s, we've added a new association; u & v are not equal but can be made equal

; == is the goal constructor, unify is the core
; =/= (disequality constraints) are dual to ==
; (=/= 5 5) fails
; (=/= 5 6) succeeds and can never be violated
; (=/= 5 x) succeeds, but x can not be instantiated to 5 later on
; (=/= `(5 . ,x) `(5 . ,y)) succeeds, but x and y can never be equal
; (=/= `(5 . ,x) `(6 . ,y)) succeeds and the constraint can never be violated
;
; when a constraint cannot be violated, we can throw it away - never need to worry about it
;
; Comparing with unification - lots of symmetry
; (== 5 5) (case 2) succeed, no need to extend substitution (throw away the constraint)
; (== 5 6) (case 1) fails
; (== 5 x) (3) succeeds, need to add constraint that x is 5 (extend substitution)
; (== `(5 . ,x) `(5 . ,y)) (3) succeeds, simplify constraint that x == y
; (== `(5 . ,x) `(6 . ,y)) (1) fails
;
; as it turns out == can be implemented in terms of unify, so can disunify

; See Hubert Comon - solving disequations
;
; Note: we now need a constraint store which includes both a substitution 's' and a disequality constraint store 'd'
; Note: Disequality store is a list of association lists (or a list of substitutions) - need the multiple pairs per disequality constraint
; c = `(,s . ,d) 
;   (could also use single store with constraints tagged by type)
;   This is another place we could add extensibility by allowing different constraint types (symbolic, numeric, etc.)
;
; turn disequality constraints into equivalent equality constraint and look at the result
; (=/= 5 5) => (== 5 5) and we get case (2) so we know we can fail since we get the same subsitution back from unify
; (=/= 5 6) => (== 5 6) and we get back false (case 1), so we know these things can never be equal, so we can throw away this disequality constraint since it can never be violated, just return the original s
; (=/= 5 x) => (== 5 x) and unification succeeds and returns s^ = ((x . 5) . s) (case 3)
;                       prefix of s^ = ((x . 5)) <- mini-substitution
;                       This mini-substitution is the normalized form of the disequality constraint and can be added to our 'd' part of the constraint store
;                       This mini-substitution could contain multiple bindings, it doesn't have to be just one
;
; (=/= `(5 . ,x) `(5 . ,y)) => unification succeeds, returns a modified substitution, we take the prefix and add it to our 'd' part of the constraint store
; (== `(5 . ,x) `(6 . ,y)) => unification fails (case 1), so we can throw away the constraint since as a disequality it can never be violated
;
; (fresh (x y z)
;   (=/= `(,x . ,y) `(,z . 5)
;   ; d = (((x . z) (y . 5)))    c = (s . d) <- note list of substitutions/association-lists as mentioned above
;   (== y 5)))
;   ; c = ( ((y.5) . s) ; <- new s
;   ;       (((x . z) (y . 5))) ) <- d
;
;   think about this constraint in terms of the unification equivalent (==) which calls unify
;   The unification succeeds and ends up with s^ = ((x . z) (y . 5) . s)
;   Thus the prefix is the mini-substitution ((x . z) (y . 5)) and this is what goes in our 'd' (disequality part of the constraint store)
;   Note: that these two conditions are a conjuction, we must violate both of them to violate the disequlaity constraint
;
;   ------------------------------------------------------------------
;   Checking Disequality when extending the substitution
;   ------------------------------------------------------------------
;   But we need to make sure that we check to see that our other constraints don't violate our disequality constraints
;   When we extend the substitution s with y == 5 to create s1, 
;     how do we solve the disequality constraint (((x . z) (y . 5))) with respect to s1?
;   Unify two terms in s1 and interpret the results as we did in interpreting the disequality constraint
;     (failure means nothing changes in the constraint store,
;      unchanged substitution means equality is satisfied so disequality should fail
;      substitution is extended, we can use the prefix as additional disequality constraints)
;
;   (unify u v `((,y . 5) . ,s)) -> what values of u and v do we give?  Our disequality constraint already has a representation of the constraint
;   (unify `(,x . ,y) `(,z . 5) `((,y . 5) . ,s))  -> mapping over car/cdr, to undo the pairwise disequality we applied earlier
;
;   this causes 
;     walking y will now result in 5, so this is equivalent to
;
;   (unify `(,x . ,5) `(,z . 5) `((,y . 5) . ,s))
;   => (unify x z `((,y . 5) . ,s))
;   => s^ = ((,x . ,z) . (,y . 5) . ,s) ; note that this substitution is only used to get the prefix which will be the new 'd', the rest is thrown away
;   => prefix of s^ =  ((x . z))
;   => now we only have to make x and z the same to violate the constraint (since y is already == to 5)
;   => c = ( ((,y . 5) . ,s)
;            (((x . y))) )
;
;   After extending the substitution, we use this algorithm to re-solve the disequality constraints to get the new 'd'
;   If we tried to then unify (== x z)
;   we would get a new subsitution s2 which would have (( x . z) (y . 5) . s),
;     (unify x z s2) => x2, which means the disequality constraint fails since the equality constraint has already been realized
;
; Key idea -> we can use unification to solve both equality and disequality constraints.
; We need to recheck the disequality constraints after any successfull unification that extends the substitution
;
; another couple examples
; (fresh (x y)
;   ; c = (s . d)
;   (=/= x 5)
;   ; c1 = (s (((x . 5)) . d)) (since x unifies with 5 creating a new mini-substitution)
;   (=/= x 6)
;   ; c2 = (s (((x . 6)) (since x unifies with 6)
;   ;          ((x . 5)) 
;   ;          . d))
;   (=/= x y)
;   ; c3 = (s (((x . y)) (since x unifies with y)
;   ;          ((x . 6))
;   ;          ((x . 5))
;   ;          . d))
;
; (fresh (x y)
;   ; c = (s . d)
;   (=/= x y)
;   ; c1 = (s (((x . y) . d)))
;   (== x 5)
;   ; c2 = ( ((x . 5) . s)
;   ;        (((y . 5)) . d) )
;   (== y 6))
;   ; c3 = ( ((y . 6) (x . 5) . s)
;   ;        d )

; Subsumption - violating one constraint necessarily violates another constraint - so keeping both around is redundant
; (fresh (x y z)
;   ;; c= (s . d)
;   (=/= x 5)
;   ;; c1 = ( s  (((x . 5)) . d) )
;   (=/= `(,x . ,y) `(5 . ,z)))
;   ;; c2  ( s
;   ;;       (((x . 5) (y . z))
;   ;;        ((x . 5)) <- mini substitution for constraint x != 5
;   ;;        . d)
;
;   Anytime we violate the second constraint, we would have violated the first constraint.
;   So, the second constraint is redundant and we can throw it away.  It is "subsumed" by the first constraint.
;   c2 = c1
;
;   We can use unification to perform the subsumption test (TODO: figure out how, to talk about next time -> answer is in the dissertation)
;   "Essentials of Logic Programming" - Christopher Hogger - accessible, theory and foundations
;
;
; :::::::::::::::::::::::::::  Uncourse #9 :::::::::::::::::::::::::::::::::::
;
; How do we want to represent logic variables?
; miniKanren uses vectors for simplicity and compatibility with old schemes
; - this means you can't do unification over vectors
; - vector has one variable which is the symbol used when introducing the variable
; microKanren uses a vector with a numeric counter to differentiate them
; - don't need to rely on specific notions of equality (eq? vs. eqv? vs equal?)
; - just numeric equality
; - but my x and y variables get converted to 0, 1, etc.
; - also need some way of incrementing the counter (global counter w/set!, atom here in clojure)
;
; jlk: I'm going to use a map with a key that specifies its id
(defn lvar [i] {:lvarid i})
(defn lvar? [l]
  (and (map? l) (= 1 (count (keys l))) (contains? l :lvarid)))

(defn lvar=? [a b]
  (and (lvar? a)
       (lvar? b)
       (= (:lvarid a) (:lvarid b))))

; unify deals with substitutions or false
; our logic programming deals with streams of answers, so failure is
; represented as an empty list (instead of false)
(def mzero []) 

; constructs a stream with a single element - take our constraint into our
; "stream of answers" monad
(defn unit [c] [c])

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

; 2 continuation-version of ==
; Dale Vaillancourt and Mitch Wand paper - equivalence of streams and continuations
; "relating models of backtracking" ICFP 2004
;
;(defn == 
  ;"definition of the goal constructor for using unification"
  ;[u v]
  ;(fn [c sc fc] ; sc/fc success and failure continutations
    ;(let [c (unify u v c)]
      ;(if c (sc c fc) (fc))))) ; if it succeeded, return the new constraint, otherwise fail


;====================================================
;* goal - takes an s/c and returns a stream of s/c
;* goal constructor is a function that returns a goal
;=====================================================

; (call-fresh
;   (fn [x]
;     (== x 5)))
;
(defn call-fresh 
  "goal constructor that creates a new logic variable and passes it to another goal constructor"
  [f]
  (fn [c] ; s/c in paper - 
    (let [ix (counter c)]
      ; invoke f with a new variable (this is the fresh)
      ; f returns a goal (see above)
      ; then invoke that goal with the constraint-store after incrementing its counter
      ((f (lvar ix)) (increment-counter c)))))

; TODO: add tests
(comment
  (call-fresh (fn [x] (== x 5)))
  ((call-fresh (fn [x] (== x 5))) (constraint-store))
  ((call-fresh
     (fn [x] 
       (call-fresh 
         (fn [y]
           (== x y)))))
   (constraint-store)))

; mplus and bind are stream operators (defining monad operations for our stream of answers)
; mplus is basically appending two streams together
; bind is the usual mapcat
;
; ================================================================
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
 
(defn pull [s]
  (if (fn? s) (pull (s)) s))

(defn take-n [n s]
  (if (zero? n) mzero
    (let [s (pull s)]
      (if (nil-stream? s) mzero
        (cons-stream (car-stream s) (take-n (dec n) (cdr-stream s)))))))

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

  ; TODO: tests
  (comment
     ((call-fresh (fn [x]
                   (μdisj+
                     (== x 5)
                     (== x 6)
                     (== x 7))
                   )) (constraint-store))

     ((call-fresh (fn [x]
                   (μconj+
                     (!= x 5)
                     (!= x 6)
                     (!= x 7))
                   )) (constraint-store))

    (macroexpand
      '(μdisj+
         (== x 5)
         (== x 6)
         (== x 7)))
   
    )
  

(defmacro conde [& lists-of-goals]
  (concat `(μdisj+)
     (map (fn [list-of-goals]
             `(μconj+ ~@list-of-goals))
           lists-of-goals)) )

  ; TODO: tests
  (comment

    (macroexpand
            '(conde
                 [(== x 5) (== x y)]
                 [(== x 6) (== x y)]
                 [(== y 7) (!= x y)]))

    (clojure.walk/macroexpand-all
            '(conde
                 [(== x 5) (== x y)]
                 [(== x 6) (== x y)]
                 [(== y 7) (!= x y)]))


    ((call-fresh
       (fn [x]
         (call-fresh
           (fn [y]
             (conde
               [(== x 5) (== x y)]
               [(== x 6) (== x y)]
               [(== y 7) (!= x y)])))))
     (constraint-store))

    )   


(defmacro fresh+
  "introduces multiple variables to a single goal"
  [vs g]
  `(call-fresh 
    (fn [~(first vs)]
      ~(if (empty? (rest vs)) g `(fresh+ ~(rest vs) ~g))
      )
    )
  )

(comment
  (macroexpand '(fresh+ [x y z] (μconj+ (== x y) (== y z))))
  (clojure.walk/macroexpand-all '(fresh+ [x y z] (μconj+ (== x y) (== y z))))

  ((fresh+ [x y]
           (== x y)
           ) (constraint-store))
  )

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
      (zzz (fives x))
      )
    )

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
    (fn [c]
      (fn []
        ((μdisj
           (== x 6)
           (sixes x)) c))))

  (defn fives-and-sixes
    [x]
    (μdisj (fives x) (sixes x)))

  (take-n 3 ((call-fresh fives) (constraint-store)))
  (take-n 3 ((call-fresh sixes) (constraint-store)))
  (doseq [i (take-n 10 ((call-fresh fives-and-sixes) (constraint-store)))]
    (println i))
)
  

