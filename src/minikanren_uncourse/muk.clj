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
;
;   constraint store (more general notion)
