
; -----------------------------------------------------------------
; uncourse #4 - relational interpreters
; write an interpreter for subset of scheme in relational style
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
(match [(list 1 2 3 4 5)]
       [([_ _ 3 4 a] :seq)] [a]
       )

; example of matching against function definition
(match ['(fn [x] (+ x 2))]
       [([fn [arg] body] :seq)] [arg body]
       )

(defn eval-exp [expr env]
  (match [expr]
    [(x :guard symbol?)] :symbol
    [(['λ [arg] body] :seq)] :lambda
     ; note that we're only supporting functions of one argument 
     ; everything should be curried
    [([func arg] :seq)] :application
    [_] :other-error))

(eval-exp '(λ [a] (+ a 2)) [])
(eval-exp '(boo [a] (+ a 2)) [])
(eval-exp 'x [])
(eval-exp '(foo 2) [])
(eval-exp '((λ [a] (+ a 2)) 3) [])

