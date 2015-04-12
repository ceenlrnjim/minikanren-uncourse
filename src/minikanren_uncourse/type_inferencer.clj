; Hangout 16 simply typed lambda calculus type inferencer
(ns minikanren-uncourse.type-inferencer
  (:refer-clojure :exclude [==])
  (:require [symbolo.core :as symbolo])
  (:use clojure.core.logic))

; Simply-typed lambda calculus
; 3 types of expressions
; - vars: lookup a variable value
; - abstraction: define a lambda/function
; - application: apply a function
;
; Reading math symbols
; <expr> : <type>
; sort of like pattern matching against <expr>
; |- turnstyle: means "infers"
; Γ- environment that maps some expression to a type
;
; Γ,(x:T1) says that we're extending the environment with the idea that
; x is bound to some type T1, even though we don't know what that type is
; until the procedure is applied

(defn lookupo [expr gamma type]
  (fresh [y t rest]
         (conso [y t] rest gamma)
         (conde
           [(== y expr) (== type t)]
           [(!= y expr) (lookupo expr rest type)])))

(defn !- 
  "This is the 'turnstyle' or infers operator.
  Gamma is the environment"
  [gamma expr type]
  (conde
    ; variable case
    [(symbolo/symbolo expr) (lookupo expr gamma type)]
    
    ; abstraction/lambda
    [(fresh [x e T1 T2 gamma_] 
            (== `(λ (~x) ~e) expr)
            (== [T1 :-> T2] type) ; assign a function type (below the line in the inference rule)
            (conso [x T1] gamma gamma_) ; extend the environment with the requirement that x is of type T1
            (!- gamma_ e T2) ; need (x:T1) to infer that e:T2 (otherwise this lambda can't have type T1->T2)
            )]

    ; application
    [(fresh [e1 e2 T1]
            (== `(~e1 ~e2) expr)
            (!- gamma e1 [T1 :-> type])
            (!- gamma e2 T1)
            )
     ]))

(comment
  (run* [q] (!- [] `(λ (z) z) q))
  (run* [q] (!- [] `z q))
  (run* [q] (!- [[`zero [:int :-> :bool]]] `zero q))
  (run* [q] (!- [[`y :bool]] `y q))
  (run* [q] (!- [[`y :bool]] `((λ (z) z) y) q))
  (run* [q] (!- [] `((λ (z) z) (λ (y) y)) q))

  )
