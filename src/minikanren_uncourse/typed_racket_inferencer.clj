; Uncourse #14 - live coding a type inferencer for typed racket like language
(ns minikanren-uncourse.typed-racket-inferencer
  (:refer-clojure :exclude [==])
  (:require [symbolo.core :as symbolo])
  (:use clojure.core.logic))

(defn infer-true-false-types [term then-prop else-prop]
  (conde 
    [(== false term) (== then-prop :impossible) (== else-prop :trivial)]
    [(conde
       [(== true term)]
       [(symbolo/numbero term)])  
     (== then-prop :trivial) (== else-prop :impossible)]))

(defn proposition [term type]
  [:proposition term type])

(defn extend-env
  [env prop]
  (cons prop env))

(defn proveo [prop-env prop]
  )

(defn booleano [v]
  (conde 
    [(== v true)]
    [(== v false)]))

(defn subtypeo [child-type parent-type]
  (conde
    [(== child-type parent-type)]
    [(fresh [b] 
        (== [:val b] child-type) 
        (conde 
          [(booleano b) (== parent-type :bool)]
          [(symbolo/numbero b) (== parent-type :num)]))]
    [(fresh [t1 t2]
        (== [:union t1 t2] child-type)
        (subtypeo t1 parent-type)
        (subtypeo t2 parent-type))]
    ))

(defn uniono [t1 t2 union-type]
  (conde
    [(== t1 t2) (== union-type t1)]
    [(!= t1 t2) (== [:union t1 t2] union-type)]
    )
  )


(defn infer [term prop-env type]
  (conde
    ; Boolean
    ; Note that in our language, true and false have different, more specific
    ; types, than bool.  They're both sub-types of bool, but they are
    ; different types (unlike classic Hilney Milner languages)
    ; these things will only unify because we have the subtypes and unions
    [(== term true) (subtypeo [:val true] type)]
    [(== term false) (subtypeo [:val false] type)]

    ; numbers
    ; - note that we;re saying the type is [:val term] so type can be any supertype of that
    [(symbolo/numbero term) (subtypeo [:val term] type)]

    ; if conditions
    [(fresh [condition then else then-prop else-prop cond-type t1 t2]
            ; detect that this is an if condition
            (== term `(if ~condition ~then ~else))
            ; infer the type of the condition
            (infer condition prop-env cond-type)
            ; confirm that the condition type is boolean (required for if)
            (subtypeo cond-type :bool)
            ; based on the condition type, figure out the types of the two branches
            (infer-true-false-types condition then-prop else-prop)
            ; now that we know the type proposition for the then branch, determine the type of the then expression
            (infer then (extend-env prop-env then-prop) t1)
            ; now that we know the type proposition for the else branch, determine the type of the else expression
            ; we need separate "output" type variables so that they don't get unified together - this would be ok
            ; in type systems where both branches of the if must have the same type (e.g. Hindley Milner (sp?))
            ; but in typed racket we want to establish a union of these two types
            (infer else (extend-env prop-env else-prop) t2)
            (uniono t1 t2 type))
     ]

    ; lambda expressions
    [(fresh [arg argtype body body-type new-prop-env]
            ; Match the lambda expression
            (== term `(lambda (~arg :> ~argtype) ~body))
            ; We know the type of the argument since it is given, so extend the environment with it
            (== new-prop-env (extend-env prop-env (proposition arg argtype)))
            ; With this updated environment, infer the type of the body
            (infer body new-prop-env body-type)
            ; return the type of the body is a function type from
            ; argtype to body-type (as represented by [a :-> b]
            (subtypeo [argtype :-> body-type] type)
            )]

    ; symbols
    [(fresh []
          (symbolo/symbolo term)
          (proveo prop-env (proposition term type)))]

     
))

(comment
  (run* [concrete-type] 
        (infer true [] concrete-type)
        (subtypeo concrete-type :bool))

  (run* [q] (infer true [] q))
  (run* [q] (infer 1 [] :num))
  (run* [q] (infer 1 [] q))
  (run*  [q] (infer `(if true true true) [] q))
  (run*  [q] (infer `(if false true true) [] q))
  ; this was failing because the same type variable was used for the then and else
  ; now w
  (run*  [q] (infer `(if true true false) [] q)) 
  ; can't run backwards yet since proveo isn't implemented
  (print  (run 1 [q] (infer q [] [:union [:val true] [:val false]])))

  (run* [q] (infer `(if true 1 1) [] q))
  )


