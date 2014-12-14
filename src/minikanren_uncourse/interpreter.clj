
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

(defn eval-exp [expr env]
  (match [expr]
    [(x :guard symbol?)] :symbol
    [([lambda [arg] body] :seq)] :lambda
    [([func arg] :seq)] :application
         )  
  )

(eval-exp `(lambda [a] (+ a 2)) [])
(eval-exp 'x [])
(eval-exp '(foo 2) [])

; example of sequence matching
(match [(list 1 2 3 4 5)]
       [([_ _ 3 4 a] :seq)] [a]
       )

; example of matching against function definition
(match ['(fn [x] (+ x 2))]
       [([fn [arg] body] :seq)] [arg body]
       )

(match [5])
