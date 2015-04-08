; Uncourse #14 - live coding a type inferencer for typed racket like language
(ns minikanren-uncourse.typed-racket-inferencer
  (:refer-clojure :exclude [==])
  (:require [symbolo.core :as symbolo])
  (:use clojure.core.logic))

(defn infer-true-false-types [term then-prop else-prop]
  (conde 
    [(== false term) (== then-prop :impossible) (== else-prop :trivial)]
    [(== true term) (== then-prop :trivial) (== else-prop :impossible)]))

(defn proposition [term type]
  [:proposition term type])

(defn extend-env
  [env prop]
  (cons prop env))

(defn proveo [prop-env prop]
  )

(defn infer [term prop-env type]
  (conde
    [(== term true) (== type :bool)]
    [(== term false) (== type :bool)]
    [(fresh [condition then else then-prop else-prop]
            (== term `(if ~condition ~then ~else))
            (infer condition prop-env :bool)

            (infer-true-false-types condition then-prop else-prop)

            (infer then (extend-env prop-env then-prop) type)
            (infer else (extend-env prop-env else-prop) type))]
    [(fresh [arg argtype body body-type new-prop-env]
            ; Match the lambda expression
            (== term `(lambda (~arg :> ~argtype) ~body))
            ; We know the type of the argument since it is given, so extend the environment with it
            (== new-prop-env (extend-env prop-env (proposition arg argtype)))
            ; With this updated environment, infer the type of the body
            (infer body new-prop-env body-type)
            ; return the type of the body is a function type from
            ; argtype to body-type (as represented by [a :-> b]
            (== type [argtype :-> body-type])
            )]
      [(fresh []
            (symbolo/symbolo term)
            (proveo prop-env (proposition term type)))]
     
))

(comment
  (run 1 [q] (infer `(if true true true) [] q))
  (run*  [q] (infer `(if true true true) [] q))
  )
