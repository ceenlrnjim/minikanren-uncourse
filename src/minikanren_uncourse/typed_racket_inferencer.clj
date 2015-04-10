; Uncourse #14 - live coding a type inferencer for typed racket like language
(ns minikanren-uncourse.typed-racket-inferencer
  (:refer-clojure :exclude [==])
  (:require [symbolo.core :as symbolo])
  (:use clojure.core.logic))

(defn infer-if-branch-props [term then-prop else-prop]
  (conde 
    [(== false term) (== then-prop :impossible) (== else-prop :trivial)]
    [(conde
       [(== true term)]
       [(symbolo/numbero term)])  
     (== then-prop :trivial) (== else-prop :impossible)]
    [(symbolo/symbolo term) 
     (== [:proposition term [:not [:val false]]] then-prop)
     (== [:proposition term [:val false]] else-prop)]))

(defn proposition [term type]
  [:proposition term type])


(defn lookupo [variable env res]
  (conde
    [(fresh [d]
            (conso [:proposition variable res] d env))]
    [(fresh [prop-term prop-type d]
            (!= prop-term variable)
            (conso [:proposition prop-term prop-type] d env)
            (lookupo variable d res))]))

(defn proveo [prop-env variable type]
  (conde
    [(fresh [t1]
            (lookupo variable prop-env t1)
            (subtypeo t1 type))]))

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
    [(== term true) (== [:val true] type)]
    [(== term false) (== [:val false] type)]

    ; numbers
    ; - note that we;re saying the type is [:val term] so type can be any supertype of that
    [(symbolo/numbero term) (== [:val term] type)]

    ; if conditions
    [(fresh [condition then else then-prop then-env else-prop else-env cond-type t1 t2]
            ; detect that this is an if condition
            (== term `(if ~condition ~then ~else))
            ; infer the type of the condition
            (infer condition prop-env cond-type)
            ; confirm that the condition type is boolean (required for if)
            (subtypeo cond-type :bool)
            ; based on the condition type, figure out the types of the two branches
            (infer-if-branch-props condition then-prop else-prop)
            ; now that we know the type proposition for the then branch, determine the type of the then expression
            ; - extend the environment
            (conso then-prop prop-env then-env)
            (infer then then-env t1)
            ; now that we know the type proposition for the else branch, determine the type of the else expression
            ; we need separate "output" type variables so that they don't get unified together - this would be ok
            ; in type systems where both branches of the if must have the same type (e.g. Hindley Milner (sp?))
            ; but in typed racket we want to establish a union of these two types
            ; - extend the environment
            (conso else-prop prop-env else-env)
            (infer else else-env t2)
            (uniono t1 t2 type))
     ]

    ; lambda expressions
    [(fresh [arg argtype body body-type new-prop-env]
            ; Match the lambda expression
            (== term `(lambda (~arg :> ~argtype) ~body))
            ; We know the type of the argument since it is given, so extend the environment with it
            ; - extend the environment
            (conso (proposition arg argtype) prop-env new-prop-env)
            ; With this updated environment, infer the type of the body
            (infer body new-prop-env body-type)
            ; return the type of the body is a function type from
            ; argtype to body-type (as represented by [a :-> b]
            (subtypeo [argtype :-> body-type] type)
            )]

    ; inc - special case so we have something that can fail a type check
    [(fresh [expr expr-type]
            (== `(inc ~expr) term)
            (infer expr prop-env expr-type) ; I think num still works here since we have all types returned
            (subtypeo expr-type :num)
            (== :num type)
            )]

    ; symbols
    [(fresh []
          (symbolo/symbolo term)
          (proveo prop-env term type))]
))

(comment
  (run* [q] (infer true [] q))
  (run* [q] 
        (fresh [concrete-type]
          (infer true [] concrete-type)
          (subtypeo concrete-type :bool)))

  (run* [q] (infer 1 [] q))
  (run* [q concrete-type] 
        (infer 1 [] concrete-type)
        (subtypeo concrete-type :num))

  (run*  [q] (infer `(if true true true) [] q))
  (run*  [q] (infer `(if false true true) [] q))
  ; this was failing because the same type variable was used for the then and else
  ; now w
  (run*  [q] (infer `(if true true false) [] q)) 
  ; can't run backwards yet since proveo isn't implemented
  (print  (run 1 [q] (infer q [] [:union [:val true] [:val false]])))

  (run* [q] (infer `(if true 1 1) [] q))

  (run* [q] (infer `(inc 1) [] q))
  (run* [q] (infer `(inc false) [] q))

  (run* [q] (infer `(lambda (x :> :num) (inc x)) [] q))
  (run* [q] (infer `(lambda (x :> :num) (inc false)) [] q))
  (run* [q] (infer `(lambda (x :> [:val false]) (inc arg)) [] q))
  (run* [q] (infer `(lambda (x :> [:union [:val false] :num]) x) [] q))
  (run* [q] (infer `(lambda (x :> [:union [:val false] :num]) (inc x)) [] q))

  ; TODO: next steps ->
  ; prop-env at if: [[:proposition arg [:union [:val false] :num]]]
  ; prop-env at (inc arg)
  ;   [ [:proposition arg [:union [:val false] :num]]
  ;     [:proposition arg [:not [:val false]]]
  ;   ]
  ;   from this we should be able to deduce that [:proposition arg [:val true]
  (run* [q] (infer `(lambda (x :> [:union [:val f] :num]) (if arg (inc arg) 0)) [] q))
  )



