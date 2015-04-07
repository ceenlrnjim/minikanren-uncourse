; Uncourse #14 - live coding a type inferencer for typed racket like language
(ns minikanren-uncourse.typed-racket-inferencer
  (:refer-clojure :exclude [==])
  (:require [symbolo.core :as symbolo])
  (:use clojure.core.logic))

(defn infer-true-false-types [term true-type false-type]
  (conde 
    [(== true term)]
    [(== false term)]
    )
  )

(defn extend-env
  [env type term]
  (cons [type term] env))

(defn infer [term prop-env type]
  (conde
    [(== term true)(== term false) (== type bool)]
    [(fresh [pred then else] 
            (== term `(if ~pred ~then ~else))
            (== infer pref :bool)
            (infer then prop-env type)
            (infer else prop-env type))]
    [(fresh [arg argtype body body-type new-prop-env]
            ; Match the lambda expression
            (== term `(lambda (~arg :> ~argtype) ~body))
            ; We know the type of the argument since it is given, so extend the environment with it
            (== new-prop-env (extend-env prop-arg argtype arg))
            ; With this updated environment, infer the type of the body
            (infer body new-prop-env body-type)
            ; return the type of the body is a function type from
            ; argtype to body-type (as represented by [a :-> b]
            (== type [argtype :-> body-type])
            )]
    )
  )
