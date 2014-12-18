
; -----------------------------------------------------------------
; minikanren version
;
; call-by-value, environment passing, lambda calculus interpreter in miniKanren
; -----------------------------------------------------------------
(ns minikanren-uncourse.relinterp
  (:require [symbolo.core :as symbolo])
  (:use clojure.core.logic))


(defn lookupo [sym env out]
  ; could use matche - start with conde and if you want to really shorten it up switch to matche
  ; matche will introduce logic values for you
  ; a failed lookup is just a failure to unify with a value
  ; (unless we want to keep track of error cases)
  (fresh [k v r]
    (conso [k v] r env)
    (conde
      [(== k sym) (== v out)]
      [(!= k sym) (lookupo sym r out)])))

(defn extendo [env k v out]
  (conso [k v] env out))

(comment 
(run 2 [out] (lookupo :a [[:a 1] [:b 2] [:a 3]] out))
(run 1 [out] (lookupo :b [[:a 1] [:b 2]] out))
(run 1 [out] (lookupo :c [[:a 1] [:b 2]] out))
(run 1 [out] (lookupo out [[:a 1] [:b 2]] 2))
(run 1 [out] (lookupo out [[:a 1] [:b 2]] 3))
(run 2 [out] (lookupo :a out 3))

(run 1 [out] (extendo [[:a 1] [:b 2] [:c 3]] :d 4 out))
(run 1 [out] (extendo [[:a 1] [:b 2] [:c 3]] out 4 [[:d 4] [:a 1] [:b 2] [:c 3]]))
)

(defn eval-expo [expr env out]
  (conde

    ; symbols
    [(symbolo/symbolo expr) (lookupo expr env out) (!= expr ':t) (!= expr ':f)]

    ; numbers
    [(symbolo/numbero expr) (== out expr)]

    ; booleans
    [(conde [(== expr ':t) (== out true)]
            [(== expr ':f) (== out false)])]

    ; conditional if
    [(fresh [pred te fe pred-value]
            (== expr (list 'if pred te fe))
            (eval-expo pred env pred-value)
            (conde
              [(== pred-value ':t) (eval-expo te env out)]
              [(== pred-value ':f) (eval-expo fe env out)]))]

    ; cons
    [(fresh [h t]
            ; TODO: check that t is a list?
            (== expr (list 'cons h t))
            (== out (list h t)))]
     
    ; car
    [(fresh [t]
            (== expr (list 'car (list out t))))]
     
    ; cdr
    [(fresh [h]
            (== expr (list 'cdr (list h out))))]
    
    ; TODO: bool? zero?
    ; TODO: quote list
    ; TODO: tagged numbers and arithmatic
    
    ; let - introduce bindings
    [(fresh [k v body extended-env]
            (== expr (list 'let (list k v) body))
            (extendo env k v extended-env)
            (eval-expo body extended-env out))]

    ; abstractions - lambda definitions
    [(fresh [arg body] 
       ; TODO: why doesn't quoting a list work here?
       ;(== expr '(λ (arg) body))
       (== expr (list 'λ (list arg) body)) 
       (== out [:closure arg body env]))]

    ; function application
    [(fresh [e1 e2 body arg value extended-env closure-env]
            (== expr (list e1 e2))
            (eval-expo e1 env [:closure arg body closure-env])
            (eval-expo e2 env value)
            (extendo closure-env arg value extended-env)
            (eval-expo body extended-env out))]))

(comment
(run 1 [out] (eval-expo 'a [['a 1]] out))
(run 1 [out] (eval-expo '(λ (x) x) [['y 42]] out))
(run 1 [out] (eval-expo '((λ (x) x) y) [['y 42]] out))
(run 1 [out] (eval-expo '((λ (x) x) y) out 42))
(run 1 [out] (eval-expo 234 [] out))
(run 1 [out] (eval-expo '((λ (x) x) 42) [] out))
(run 1 [out] (eval-expo '(let (y 42) y) [] out))
(run 1 [out] (eval-expo '(let (y 42) ((λ (x) x) y)) [] out))
  (run 1 [out] (eval-expo '(if x y z) [['x :f] ['y 1] ['z 2]] out))
  (run 1 [out] (eval-expo '(cons 4 ()) [] out))
  (run 1 [out] (eval-expo '(cons 4 (2 ())) [] out))
  (run 1 [out] (eval-expo '(car (4 (2 ()))) [] out))
  (run 1 [out] (eval-expo '(cdr (4 (2 ()))) [] out))
)
