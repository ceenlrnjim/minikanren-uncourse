
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
    (symbolo/symbolo k)
    (symbolo/symbolo sym)
    (conde
      [(== k sym) (== v out)]
      [(!= k sym) (lookupo sym r out)])))

(defn extendo [env k v out]
  (symbolo/symbolo k)
  (conso [k v] env out))

(comment 
(run 2 [out] (lookupo `a [[`a 1] [`b 2] [`a 3]] out))
(run 1 [out] (lookupo `b [[`a 1] [`b 2]] out))
(run 1 [out] (lookupo `c [[`a 1] [`b 2]] out))
(run 1 [out] (lookupo out [[`a 1] [`b 2]] 2))
(run 1 [out] (lookupo out [[`a 1] [`b 2]] 3))
(run 1 [out] (lookupo `a out 3))

(run 1 [out] (extendo [['a 1] ['b 2] ['c 3]] 'd 4 out))
(run 1 [out] (extendo [['a 1] ['b 2] ['c 3]] out 4 [['d 4] ['a 1] ['b 2] ['c 3]]))
)

; recursive "maping" function that applies eval to all the exprs
(defn eval-exp*o [exprs env out]
  (conde
    [(== exprs []) (== out '())]
    [(fresh [h t hv tv] 
            (conso h t exprs)
            (eval-expo h env hv)
            (conso hv tv out)
            (eval-exp*o t env tv)
            )]))

(comment
  (run 1 [h t] (conso h t '(z)))
  (run 1 [q] (resto '(z) q))
  (run 1 [q] (eval-exp*o '(1 z) [['y 1] ['z 5]] q))
  (run 1 [q] (eval-exp*o '(y 2 3 4 z) [['y 1] ['z 5]] q))
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
            (== expr [`if pred te fe])
            (eval-expo pred env pred-value)
            (conde
              [(== pred-value ':t) (eval-expo te env out)]
              [(== pred-value ':f) (eval-expo fe env out)]))]

    ; empty list
    ;[(== expr '()) (== out '())]

    ; quote
    [(== expr ['quote out])]

    ; list
    [(fresh [args] 
            (conso `list args expr)
            (eval-exp*o args env out)
            )]

    ; cons
    [(fresh [he te hv tv]
            ; TODO: check that t is a list?
            (== expr [`cons he te])
            (eval-expo he env hv)
            (eval-expo te env tv)
            (== out (list hv tv)))]
     
    ; car
    [(fresh [le t]
            (== expr [`car le])
            (eval-expo le env [out t]))]
     
    ; cdr
    [(fresh [h le]
            (== expr [`cdr le])
            (eval-expo le env [h out]))]
    
    ; TODO: bool? zero?
    ; TODO: tagged numbers and arithmatic
    ; TODO: mapo that simulates map (as used in list)
    
    ; let - introduce bindings
    [(fresh [k v body extended-env]
            (== expr [`let [k v] body])
            (extendo env k v extended-env)
            (eval-expo body extended-env out))]

    ; abstractions - lambda definitions
    [(fresh [arg body] 
       (== expr [`λ [arg] body] )
       (symbolo/symbolo arg)
       (== out [:closure arg body env]))]

    ; function application
    [(fresh [e1 e2 body arg value extended-env closure-env]
            (== expr [e1 e2])
            ; TODO: this will collide with (quote x)
            (eval-expo e1 env [:closure arg body closure-env])
            (eval-expo e2 env value)
            (extendo closure-env arg value extended-env)
            (eval-expo body extended-env out))]))

(comment
  (run 1 [out] (eval-expo `a [[`a 1]] out))

  (run 1 [out] (eval-expo `(λ (x) x) [[`y 42]] out))
  (run 1 [out] (eval-expo `((λ (x) x) y) [[`y 42]] out))
  (run 1 [out] (eval-expo `((λ (x) x) y) out 42))

  (run 1 [out] (eval-expo 234 [] out))
  (run 1 [out] (eval-expo `((λ (x) x) 42) [] out))
  (run 1 [out] (eval-expo `((λ (x) x) ~out) [] 42))

  (run 1 [out] (eval-expo `(let (y 42) y) [] out))
  (run 1 [out] (eval-expo `(let (y 42) ((λ (x) x) y)) [] out))

  (run 1 [out] (eval-expo `(if x y z) [[`x :t] [`y 1] [`z 2]] out))
  (run 1 [out] (eval-expo `(if ~out y z) [['x :t] ['y 1] ['z 2]] 1))

  (run 1 [out] (eval-expo `(cons 4 (quote ())) [] out))
  (run 1 [out] (eval-expo `(cons 4 (quote (2 ()))) [] out))
  (run 1 [out] (eval-expo `(car (quote (4 (2 ())))) [] out))
  (run 1 [out] (eval-expo `(cdr (quote (4 (2 ())))) [] out))
  (run 1 [out] (eval-expo `(car (quote (42 ()))) [] out))
  (run 1 [out] (eval-expo `(car (quote (x ()))) [[`x 5]] out))
  (run 1 [out] (eval-expo `(cons ((λ (x) x) y) (quote ())) [[`y 42]] out))

  (run 1 [out] (eval-expo `(car (cons ((λ (x) x) y) (quote ()))) [[`y 42]] out))

  (run 1 [out] (eval-expo `() [] out))

  (run 1 [out] (eval-expo '(quote (car (cons ((λ (x) x) y) (quote ())))) [['y 42]] out))

  ; TODO: need to decide on quote type = I think syntax quote will be required if I want to run backwards
  (run 1 [out] (eval-expo `(car ~out) [] 4))

  ; list
  (run 2 [out] (eval-expo `(list a b c d e) [[`a 1] [`b 2] [`c 3] [`d 4] [`e 5]] out))

)



