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

; variable interface
; (lvar 0) - constructor, makes a new variable
; (lvar? t) - true or false
; (lvar-eq? v1 v2) - true or false

(defn lvar [i] {:lvarid i})
(defn lvar? [l]
  (and (map? l) (contains? l :lvarid)))

(defn lvar-eq? [a b]
  (and (lvar? a)
       (lvar? b)
       (= (:lvarid a) (:lvarid b)))  )

; (walk 5 `((,x . 7))) => 5
; (walk y `((,x . 7))) => y
; (walk `(,x ,y) `((,x . 7) (,y . 6))) => `(,x . ,y)
(defn walk 
  "walk term t in substitution s"
  [t s]
  (cond
    (lvar? t) 
      (let [pr (get s t)]
        (if pr
          (recur pr s)
          t)) ; not found, return the term
    :else t)); if the term is not a variable just return the term

(defn ext-s [u v s]
  ; I'm using maps instead of association lists
  (assoc s u v))

(defn pair? [t]
  (and (vector? t) (= (count t) 2)))

; if unification succeeds, it returns a substitution (map) that would make the
; two terms equal
(defn unify 
  [u v s]
  (let [u (walk u s) ; note shadowing
        v (walk v s)]
    (cond
      ; both u and v walk to the same variable, just return s without changes
      (and (lvar? u) (lvar? v) (lvar-eq? u v)) 
        s
      (lvar? u) ; either v is not a variable, or it is but isn't the same as u
        (ext-s u v s) ; we're missing the occurs? check to make sure that you're not unifying a variable with a term that contains that same variable
      (lvar? v) ; we know that u is not a variable
        (ext-s v u s)
      (and (pair? u) (pair? v)) ; pairwise unification on the cars and cdrs
        (let [s (unify (first u) (first v) s)]
          (and s (unify (second u) (second v) s))) ; note - using and as an if statement
      :else (and (== u v) s)))) ; use host language equivalence to test if these values are the same
