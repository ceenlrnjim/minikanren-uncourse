; microKanren in clojure
;
; based on 2013 scheme workshop paper by Jason Hemann and Dan Friedman
; github.com/jasonhemann/microKanren

(ns minikanren-uncourse.muk)

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


(defn constraint-store []
  {:substitution {}
   :disequalities [] })

(defn substitution [c] (:substitution c))
(defn disequalities [c] (:disequalities c))

(defn pair? [t]
  (and (vector? t) (= (count t) 2)))

(defn ext-s 
  "extend a substitution with the pair (u . v) if it doesn't violate any
  other constraints"
  [u v c]
  ; I'm using maps instead of association lists
  (assoc-in c [:substitution u] v))
; =====================================================================


; (walk 5 `((,x . 7))) => 5
; (walk y `((,x . 7))) => y
; (walk `(,x ,y) `((,x . 7) (,y . 6))) => `(,x . ,y)
(defn walk 
  "walk term t in substitution s"
  [t c]
  (let [s (substitution c)]
    (cond
      (lvar? t) 
        (let [pr (get s t)] ; note - using clojure map instead of association list
          (if pr
            (recur pr c)
            t)) ; not found, return the term
      :else t))); if the term is not a variable just return the term

(comment
  (walk (lvar 0) (ext-s (lvar 0) 5 (constraint-store)))
  (walk (lvar 0) (ext-s (lvar 1) (lvar 0) (constraint-store)))
  (walk (lvar 1) (ext-s (lvar 1) (lvar 0) (constraint-store)))
  (walk (lvar 1) (ext-s (lvar 1) (lvar 0) (ext-s (lvar 0) 5 (constraint-store))))
)


; if unification succeeds, it returns a substitution (map) that would make the
; two terms equal
; this unifier only handles lvars, pairs, and things that are comparable with ==,
;   using a  typeclass/protocol based approach for the final comparison allows
;   for an extensible unifier
(defn unify 
  [u v c]
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
      (and (pair? u) (pair? v)) ; pairwise unification on the cars and cdrs
        (let [c (unify (first u) (first v) c)]
          (and c (unify (second u) (second v) c))) ; note - using and as an if statement
      :else (and (= u v) c)))) ; use host language equivalence to test if these values are the same

(comment
  (unify 5 5 (constraint-store))
  (unify 5 6 (constraint-store))
  (unify (lvar 0) 6 (constraint-store))
  (unify (lvar 0) 6 (assoc-in (constraint-store) [:substitution (lvar 0)] 5))
)

; TODO: try to implement disequality in micro-kanren as described below
(defn diseq
  [u v c]
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
        ; TODO: add accessor/mutators to clean this up
        (assoc c :disequalities 
               (conj  (:disequalities c) (apply dissoc (substitution unify-result) (keys (substitution c))))))))

(comment
  (diseq 5 5 (constraint-store))
  (diseq 5 6 (constraint-store))
  (diseq (lvar 0) 6 (constraint-store))
  (diseq (lvar 0) 6 {:substitution {(lvar 0) 6} :disequalities []})
  (diseq [(lvar 0) (lvar 2)] [(lvar 1) 5] (constraint-store))
  )

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

