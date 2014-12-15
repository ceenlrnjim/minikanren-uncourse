
; -----------------------------------------------------------------
; uncourse #4 - relational interpreters
; write an interpreter for subset of scheme in relational style
;
; call-by-value, environment passing, lambda calculus in scheme
; -----------------------------------------------------------------
(ns minikanren-uncourse.core
  (:use [clojure.core.match :only (match)])
  (:use clojure.core.logic))

; interpreter for call-by-value lambda calculus that scheme is based on
; call-by-value since we have to evaluate all the arguments before we can pass them to 
;   a function invocation.  As opposed to call-by-name or call-by-need lazy evaluation (like Haskell)
; 3 types of fundamental expressions
; - 1: variables
; - 2: lambdas / anonymous functions - abstraction
; - 3: function application


; example of sequence matching
; Note that list matching is not supported by core.match, using seq
;  which would technically match vectors etc. as well
(match [(list 1 2 3 4 5)]
       [([_ _ 3 4 a] :seq)] [a])

; example of matching against function definition
(match ['(fn [x] (+ x 2))]
       [(['fn [arg] body] :seq)] [arg body])

(defn lookup [sym env]
  (match [env]
         ; match the empty sequence - break recursion
         [([] :seq)] (throw (IllegalArgumentException. (str "unbound variable: " sym)))
         ; first symbol in the list of pairs matches - we've found what we're looking for
         [([[sym v] & r] :seq)] v
         ; first symbol doesn't match, recur over the rest of the pairs
         [([[k v] & r] :seq)] (lookup sym r)))

(defn extend-env [env k v]
  (cons [k v] env))

(defn eval-exp [expr env]
  (match [expr]
          
    ; Handle variable expansion
    [(x :guard symbol?)] (lookup x env)

    ; numbers? (JLK extension)
    [(x :guard number?)] x

    ; add bindings to env (JLK extension)
    [(['with [(k :guard symbol?) v] body] :seq)]
      (eval-exp body (extend-env env k (eval-exp v env)))

    ; TODO: add quote and list after implementing miniKanren version
          
    ; Handle abstraction - defining functions
         ; Using a tagged vector to represent functions
    [(['λ [arg] body] :seq)] [:closure arg body env] ; storing the environment is what give us lexical scope, shadowing, etc.
          
    ; Handle function application
       ; note that we're only supporting functions of one argument 
       ; everything should be curried
    [([e1 e2] :seq)]
      ; Note that in scheme order of evaluation between e1 and e2 is unspecified
      ; eval e1 - better eval to a closure, call it 'proc'
      ; eval e2 to some value
      ; apply proc to value
      (let [proc (eval-exp e1 env)
            value (eval-exp e2 env)]
        ; note vector matching here, not seq since I create the closure data structure
        ; as a vector
        (match [proc]
               [[:closure arg body proc-env]] 
                  ; evaluate the body in an extended environment in which
                  ; the environment of the closure is extended with a binding between
                  ; x and value
                  (eval-exp body (extend-env proc-env arg value)) ; using env here instead of proc-env would give dynamic instead of lexical scope
               [_] (throw (IllegalArgumentException. (str "e1 does not evaluate to a procedure" proc)))))
      
    ; Error - not a valid expression
    [_] (throw (IllegalArgumentException. (str "Invalid expression: " expr)))))


; examples of variable lookup
(eval-exp 'x [['z 1] ['y 2] ['x 3]])
(eval-exp 'y [['z 1] ['y 2] ['x 3]])
(eval-exp 'a [['z 1] ['y 2] ['x 3]])

; example of abstraction
(eval-exp '(λ [a] (+ a 2)) [['z 1] ['y 2] ['x 3]])

; examples of (successful and failed) application
(eval-exp '((λ [z] z) y) [['y 5]])
(eval-exp '(foo 2) [])
(eval-exp '(foo 2) [['foo [:closure 'x 'x []]]])
(eval-exp '(foo 2) [['foo (eval-exp '(λ [x] x) [])]])

; example of number extension
(eval-exp '((λ [x] 42) y) [['y 5]])

;example of binding variables
(eval-exp '(with [y 42] 
            ((λ [x] y) z)) 
          [['y 100] ['z 2]])

(eval-exp '(with [foo (λ [x] x)] (foo 100)) [])

; -----------------------------------------------------------------
; minikanren version
;
; call-by-value, environment passing, lambda calculus interpreter in miniKanren
; -----------------------------------------------------------------

(defn lookupo [sym env out]
  ; could use matche - start with conde and if you want to really shorten it up switch to matche
  (conde
    ; match the empty sequence - break recursion - don't need this clause since
    ; a failed lookup is just a failure to unify with a value
    ; (unless we want to keep track of error cases)
     
    ; first symbol in the list of pairs matches - we've found what we're looking for
    [(fresh [pair r v] 
            (conso pair r env)
            (conso sym v pair) 
            (conso out '() v) )]
    ; first symbol doesn't match, recur over the rest of the pairs
    [(fresh [pair r k v]
            (conso pair r env)
            (conso k v pair)
            (!= sym k)
            (lookupo sym r out))]
    ))

(run 1 [out] (lookupo :a [[:a 1] [:b 2]] out))
(run 1 [out] (lookupo :b [[:a 1] [:b 2]] out))
(run 1 [out] (lookupo out [[:a 1] [:b 2]] 2))
