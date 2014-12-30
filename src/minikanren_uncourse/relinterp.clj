
; -----------------------------------------------------------------
; minikanren version
;
; call-by-value, environment passing, lambda calculus interpreter in miniKanren
; -----------------------------------------------------------------
(ns minikanren-uncourse.relinterp
  (:refer-clojure :exclude [==])
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

(comment
  (run 1 [q] (lookupo 'x [['x 1] ['x 2]] q))
  (run 1 [q] (lookupo 'y [['x 1] ['x 2]] q))
  (run 1 [q] (lookupo q [['x 1] ['y 2]] 2))
  )

(defn unboundo [v env]
  (fresh []
    (symbolo/symbolo v)
    (conde
      [(== env '())]
      [(fresh [h t r]
              (conso [h t] r env)
              (!= h v)
              (unboundo v r))])))

(defn extendo* [syms values env out]
  (conde
    [(== syms '()) (== out env)]
    [(fresh [s ss v vs res]
            (conso s ss syms)
            (conso v vs values)
            (conso [s v] res out)
            (extendo* ss vs env res))]))

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
    [(== expr `(quote ~out)) 
     (unboundo `quote env) ; need to handle case where quote is shadowed
     ;(absento :closure out)
     ]

    ; list
    [(fresh [args] 
            (conso `list args expr)
            (unboundo `list env)
            (eval-exp*o args env out))]

    ; cons
    [(fresh [he te hv tv]
            ; TODO: check that t is a list?
            (== expr `(cons ~he ~te))
            (conso hv tv out)
            (unboundo `cons env)
            (eval-expo he env hv)
            (eval-expo te env tv))]

    ; car
    [(fresh [le t lv]
            (== expr `(car ~le))
            (unboundo `car env)
            (conso out t lv)
            (eval-expo le env lv))]
  
    ; cdr
    [(fresh [h le lv]
            (== expr `(cdr ~le))
            (unboundo `cdr env)
            (conso h out lv)
            (eval-expo le env lv))]

    ; null?
    [(fresh (e v)
            (== expr `(null? ~e)) 
            (unboundo `null? env)
            (conde
              [(== '() v) (== true out)]
              [(!= '() v) (== false out)])
            (eval-expo e env v))]
    
    ; conditional if
    [(fresh [pred te fe pred-value]
            (== expr `(if ~pred ~te ~fe))
            (unboundo `if env)
            (eval-expo pred env pred-value)
            (conde
              [(== pred-value false) (eval-expo fe env out)]
              [(!= pred-value false) (eval-expo te env out)]))]

    ; abstractions - lambda definitions
    ; TODO: lambdas with multiple arguments
    [(fresh [args body] 
       (== expr `(λ ~args ~body))
       (== out [:closure args body env])
       ;(symbolo/symbolo arg) ; TODO: check that everything is a symbol
       (unboundo `λ env)
       )]

    ;[(fresh [arg body] 
       ;(== expr `(λ (~arg) ~body))
       ;(== out [:closure arg body env])
       ;(symbolo/symbolo arg)
       ;(unboundo `λ env)
       ;)]

    ; function application
    ; application with multiple arguments
    [(fresh [funcexp funcargs procargs body values extended-env closure-env]
            (conso funcexp funcargs expr)
            (!= funcexp `quote)
            (!= funcexp `null?)
            (!= funcexp `if)
            (!= funcexp `cons)
            (!= funcexp `car)
            (!= funcexp `cdr)
            (!= funcexp `list)
            ; note: this ordering is required to get queries to complete quickly
            (eval-exp*o funcargs env values)
            (extendo* procargs values closure-env extended-env)
            (eval-expo funcexp env [:closure procargs body closure-env])
            (eval-expo body extended-env out))]))

    ; function application
    ;[(fresh [e1 e2 body arg value extended-env closure-env]
            ;(== expr `(~e1 ~e2))
            ;(eval-expo e1 env [:closure arg body closure-env])
            ;(eval-expo e2 env value)
            ;(conso [arg value] closure-env extended-env)
            ;(eval-expo body extended-env out))]  

    ; numbers
    ;[(symbolo/numbero expr) (== out expr)]

    ; booleans
    ;[(conde [(== expr ':t) (== out true)]
            ;[(== expr ':f) (== out false)])]

    ; empty list
    ;[(== expr '()) (== out '())]

     
    
    ; TODO: bool? zero?
    ; TODO: tagged numbers and arithmatic
    ; TODO: mapo that simulates map (as used in list)
    
    ; let - introduce bindings
    ;[(fresh [k v body extended-env]
            ;(== expr [`let [k v] body])
            ;(extendo env k v extended-env)
            ;(eval-expo body extended-env out))]

; as previously defined - converted from scheme implementation
(defn myappend [l s]
  (cond
    (empty? l) s
    :else (cons (first l) (myappend (rest l) s))))

(defn myappendo [l s out]
  (conde
    [(== '() l) (== s out)]
    [(fresh (h t res)
      (conso h t l)
      (conso h res out)
      (myappendo t s res))]))


; replacing with a new definition to make implementation in our interpreter simpler
(defn myappend2 [l]
  ; need to curry since our interpreter only takes one argument
  (fn [s]
    (if (empty? l) 
      s
      (cons (first l) ((myappend2 (rest l)) s)))))

(comment
  ((myappend2 [1 2 3]) [4 5 6])
  )


(defn Y [f]
  ((fn [x] (f (x x))) 
   (fn [x] (f (x x)))))


(comment
  (run 1 [out] (eval-expo `a [[`a 1]] out))

  (run 1 [out] (eval-expo `(λ (x) x) [[`y 42]] out))
  (run 1 [out] (eval-expo `((λ (x) x) y) [[`y 42]] out))
  (run 1 [out] (eval-expo `((λ (x) x) y) out 42))
  (run 1 [out] (eval-expo `((λ (λ) λ) x) [[`x 1]] out))

  ; TODO: is absento messing this up
  (run 1 [out] (eval-expo `((λ (x) x) ~out) [] 42))

  (run 1 [out] (eval-expo `() [] out))
  (run 1 [out] (eval-expo `(quote foobar) [] out))

  (run 1 [out] (eval-expo `(quote (car (cons ((λ (x) x) y) (quote ())))) [[`y 42]] out))

  ; list
  (run 1 [out] (eval-expo `(list '() '() '()) [] out))
  (run 2 [out] (eval-expo `(list a b c d e) [[`a 1] [`b 2] [`c 3] [`d 4] [`e 5]] out))
  (run 2 [out] (eval-expo out `() `(5 6 [:closure z y [[`y 7]]])))
  (run 1 [out] (eval-expo `((λ (list) list) x) [[`x 1] [`y 2] [`z 3]] out))

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

  (run 1 [q] (eval-expo `(cons (quote a) (quote b)) [] q))
  (run 1 [q] (eval-expo `(car (quote (a (b c)))) [] q))
  (run 1 [q] (eval-expo `(cdr (quote (a (b c)))) [] q))
  (run 1 [q] (eval-expo `(null? (quote ())) [] q))
  (run 1 [q] (eval-expo `(null? (cdr (quote (4 ())))) [] q))
  (run 1 [q] (eval-expo `(if (null? (quote ())) (quote t) (quote f)) [] q))
  (run 1 [q] (eval-expo `(if (null? (quote (2))) (quote t) (quote f)) [] q))

  (run 1 [q] (eval-expo `(cons (quote a) (cons (quote b) (cons (quote c) (quote ())))) [] q))
  (run 1 [q] (eval-expo `(car (cons (quote a) (cons (quote b) (cons (quote c) (quote ()))))) [] q))
  (run 1 [q] (eval-expo `(cdr (cons (quote a) (cons (quote b) (cons (quote c) (quote ()))))) [] q))

  (run*  [q]
    (eval-expo
     `((((λ (f)
        ((λ (x) (f (x x))) 
         (λ (x) (λ (y) ((f (x x)) y)))))

       (λ [myappend3]
          (λ (l)
            (λ (s)
              (if (null? l) 
                s
                (cons (car l) ((myappend3 (cdr l)) s)))))))
     (quote (a b c))) (quote (d e))) [] q)) 

  (run*  [q]
    (eval-expo
     `((((λ (f)
        ((λ (x) (f (x x))) 
         (λ (x) (λ (y) ((f (x x)) y)))))

       (λ [myappend3]
          (λ (l)
            (λ (s)
              (if (null? l) 
                s
                (cons (car l) ((myappend3 (cdr l)) s)))))))
     (quote (a b c))) (quote ~q)) [] `(a b c d e))) 

  (run* [x y]
    (eval-expo
     `((((λ (f)
        ((λ (x) (f (x x))) 
         (λ (x) (λ (y) ((f (x x)) y)))))

       (λ [myappend3]
          (λ (l)
            (λ (s)
              (if (null? l) 
                s
                (cons (car l) ((myappend3 (cdr l)) s)))))))
     (quote ~x)) (quote ~y)) [] `(a b c d e))) 


  ; multiple argument abstraction/application
  (run 1 [out] (eval-expo `(λ (x y z) (list z y x)) [] out))
  (run 1 [out] (eval-expo `((λ (x y z) (list z y x)) (quote a) (quote b) (quote c)) [] out))
)



