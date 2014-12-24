
; -----------------------------------------------------------------
; minikanren version
;
; call-by-value, environment passing, lambda calculus interpreter in miniKanren
; -----------------------------------------------------------------
(ns minikanren-uncourse.relinterp
  (:require [symbolo.core :as symbolo])
  (:use clojure.core.logic))


;; call-by-value environment-passing lambda-calculus interpreter in miniKanren

;; env : mapping from symbol (variable) to value
;;
;; (lookupo 'y '((x . 5) (y . (#t foo))) '(#t foo))

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

(defn unboundo [v env]
  (fresh []
    (symbolo/symbolo v)
    (conde
      [(== env '())]
      [(fresh [h t r]
              (conso [h t] r env)
              (!= h v)
              (unboundo v r))])))

(declare eval-expo)

(defn eval-exp*o [exprs env out]
  (conde
    [(== exprs []) (== out '())]
    [(fresh [h t hv tv] ; (h)ead (t)ail (h)ead-(v)alue (t)ail-(v)alue
            (conso h t exprs)
            (conso hv tv out)
            ; we want our simpler conditions before "serious" recursive calls
            (eval-expo h env hv)
            (eval-exp*o t env tv))]))

; can I build a cheesy version of absento that will hopefully work well
; enough to keep up with the class?
(defn absento [x l]
  (fresh [h t]
    ; TODO: this will probably break running backwards 
         ; and I probably don't understand the implications of using this
    (conda
      ; empty list
      [(== l [])]
      [(== x l) (== :t :f)]
      [(conso x t l) (== :t :f)] ;fail where x is in the head of the list
      ; non- empty list
      [(conso h t l) (absento x h) (absento x t)] ; TODO: do I want (absento x h) as well?
      [(!= x l)])))

(comment
  (run 1 [q] (absento 'x 'x))
  (run 1 [q] (absento 'x 'y))
  (run 1 [q] (absento 'x '()))
  (run 1 [q] (absento 'x '(x)))
  (run 1 [q] (absento 'x '((x))))
  (run 1 [q] (absento 'x '(y)))
  (run 1 [q] (absento 'x '((y))))
  (run 1 [q] (absento 'x '(1 2 3 4 y 5 6)))
  (run 1 [q] (absento 'x '(1 2 3 4 x 5 6)))
  (run 1 [q] (absento :closure '(1 2 3 4 :closure 5 6)))
  (run 1 [q] (absento :closure '(1 2 3 4 :not-closure 5 6)))
  (run 1 [q] (absento :closure '(1 2 3 4 [:closure] 5 6)))
  (run 1 [q] (absento :closure '(1 2 3 4 [:not-closure] 5 6)))
  )

(defn eval-expo [expr env out]
  (conde

    ; symbols
    [(symbolo/symbolo expr) (lookupo expr env out)]

    ; quote
    [(== expr (list 'quote out)) 
     (unboundo 'quote env) ; need to handle case where quote is shadowed
     (absento :closure out)
     ]

    ; list
    [(fresh [args] 
            (conso `list args expr)
            (unboundo 'quote env)
            (eval-exp*o args env out))]

    ; abstractions - lambda definitions
    [(fresh [arg body] 
       (== expr [`λ [arg] body] )
       (unboundo `λ env)
       (symbolo/symbolo arg)
       (== out [:closure arg body env]))]

    ; function application
    [(fresh [e1 e2 body arg value extended-env closure-env]
            (== expr [e1 e2])
            (eval-expo e1 env [:closure arg body closure-env])
            (eval-expo e2 env value)
            (extendo closure-env arg value extended-env)
            (eval-expo body extended-env out))]))
;
    ; numbers
    ;[(symbolo/numbero expr) (== out expr)]

    ; booleans
    ;[(conde [(== expr ':t) (== out true)]
            ;[(== expr ':f) (== out false)])]

    ; conditional if
    ;[(fresh [pred te fe pred-value]
            ;(== expr [`if pred te fe])
            ;(eval-expo pred env pred-value)
            ;(conde
              ;[(== pred-value ':t) (eval-expo te env out)]
              ;[(== pred-value ':f) (eval-expo fe env out)]))]

    ; empty list
    ;[(== expr '()) (== out '())]

    ; cons
    ;[(fresh [he te hv tv]
            ;; TODO: check that t is a list?
            ;(== expr [`cons he te])
            ;(== out (list hv tv)) 
            ;(eval-expo he env hv)
            ;(eval-expo te env tv))]
     
    ; car
    ;[(fresh [le t]
            ;(== expr [`car le])
            ;(eval-expo le env [out t]))]
     
    ; cdr
    ;[(fresh [h le]
            ;(== expr [`cdr le])
            ;(eval-expo le env [h out]))]
    
    ; TODO: bool? zero?
    ; TODO: tagged numbers and arithmatic
    ; TODO: mapo that simulates map (as used in list)
    
    ; let - introduce bindings
    ;[(fresh [k v body extended-env]
            ;(== expr [`let [k v] body])
            ;(extendo env k v extended-env)
            ;(eval-expo body extended-env out))]



(comment
  (run 1 [out] (eval-expo `a [[`a 1]] out))

  (run 1 [out] (eval-expo `(λ (x) x) [[`y 42]] out))
  (run 1 [out] (eval-expo `((λ (x) x) y) [[`y 42]] out))
  (run 1 [out] (eval-expo `((λ (x) x) y) out 42))

  ; TODO: is absento messing this up
  (run 1 [out] (eval-expo `((λ (x) x) ~out) [] 42))

  (run 1 [out] (eval-expo `() [] out))

  (run 1 [out] (eval-expo '(quote (car (cons ((λ (x) x) y) (quote ())))) [['y 42]] out))

  ; TODO: need to decide on quote type = I think syntax quote will be required if I want to run backwards

  ; list
  (run 1 [out] (eval-expo `(list '() '() '()) [] out))
  (run 2 [out] (eval-expo `(list a b c d e) [[`a 1] [`b 2] [`c 3] [`d 4] [`e 5]] out))
  (run 2 [out] (eval-expo out `() `(5 6 [:closure z y [[`y 7]]])))

  ; both the following return the same closure
  (run* [q] (eval-expo `(λ (x) x) [] q))
  (run* [q] (eval-expo `((λ (y) y) 
                            (λ (x) x)) [] q))

  ; minikanren quotes the closure instead of giving us
  ; the expression that evaluates to the closure since we have quote
  (run 2 [q] (eval-expo q [] [:closure `x `x []]))

  ; demonstrate that quoting doesn't handle shadowing
  (run* [q] (eval-expo `((λ (quote) (quote quote)) (λ (y) y)) [] q))
  ; => returns quote and the closure without unboundo

  (run 2 [q] (eval-expo q [] `(I love you)))

  ; quite (eval expr) => expr
  ; TODO: re-run this with absento that checks head and tail
  (run 1 [q] (eval-expo q [] q))

  (run 1 [p q] 
       (!= p q)
       (eval-expo q [] p)
       (eval-expo p [] q))
)



