#lang racket

(require cKanren/miniKanren)
(require cKanren/absento)
(require cKanren/attributes)
(require cKanren/neq)

;; shimming numbero/absento with cKanren versions
(define symbolo symbol)
(define numbero number)

;; call-by-value environment-passing lambda-calculus interpreter in miniKanren

;; env : mapping from symbol (variable) to value
;;
;; (lookupo 'y '((x . 5) (y . (#t foo))) '(#t foo))

(define lookupo
  (lambda (x env out)
    (fresh (y val envˆ)
      (== `((,y . ,val) . ,envˆ) env)
      (symbolo x)
      (symbolo y)
      (conde
        [(== x y) (== val out)]
        [(=/= x y) (lookupo x envˆ out)]))))

(define unboundo
  (lambda (x env)
    (fresh ()
      (symbolo x)
      (conde
        [(== '() env)]
        [(fresh (y v env^)
           (== `((,y . ,v) . ,env^) env)
           (=/= x y)
           (unboundo x env^))]))))

(define eval-expo
  (lambda (expr env out)
    (fresh ()
      (conde
        [(symbolo expr) ;; variable
         (lookupo expr env out)]
        [(== `(quote ,out) expr)
         (absento 'closure out)
         (unboundo 'quote env)]
        [(fresh (expr*)
           (== `(list . ,expr*) expr)
           (eval-exp*o expr* env out)
           (unboundo 'list env))]
        [(fresh (xs le lv)
           (== `(car ,le) expr)
           (== `(,out . ,xs) lv)
           (eval-expo le env lv))]
        [(fresh (le lv x)
           (== `(cdr ,le) expr)
           (== `(,x . ,out) lv)
           (eval-expo le env lv))]
        [(fresh (h t hv tv)
           (== `(cons ,h ,t) expr)
           (== out (cons hv tv))
           (eval-expo h env hv)
           (eval-expo t env tv))]
        [(fresh (x body) ;; abstraction
           (== `(lambda (,x) ,body) expr)
           (== `(closure ,x ,body ,env) out)
           (symbolo x)
           (unboundo 'lambda env))]
        [(fresh (e value)
            (== `(eval ,e) expr)
            (eval-expo e env value)
            (unboundo 'eval env)
            (eval-expo value '() out))]
        [(fresh (e1 e2 val x body envˆ) ;; application
           (== `(,e1 ,e2) expr)
           (eval-expo e1 env `(closure ,x ,body ,envˆ))
           (eval-expo e2 env val)
           (eval-expo body `((,x . ,val) . ,envˆ) out))]))))

;; (run 1 (q) (eval-expo '(car (list x y)) '((x . 1) (y . 2)) q))
;; (run 1 (q) (eval-expo '(car (cdr (list x y z))) '((x . 1) (y . 2) (z . 42)) q))
;; (run 1 (q) (eval-expo '(cons (lambda (x) x) (quote (y))) '((y . 42)) q))

(define eval-exp*o
  (lambda (expr* env out)
    (conde
      [(== '() expr*) (== '() out)]
      [(fresh (a d res-a res-d)
         (== (cons a d) expr*)
         (== (cons res-a res-d) out)
         (eval-expo a env res-a)
         (eval-exp*o d env res-d))])))

;(run 2 (expr) (eval-expo expr '() '(I love you)))

;; Quines
;(run 1 (q) (eval-expo q '() q))

;; hangout #6
(define Y
  (lambda (f)
     ((lambda (x)
        (f (x x)))
      (lambda (x) 
        (lambda (y)
        ((f (x x)) y))))))

(define my-append
  (lambda [l]
    (lambda [s]
    (if (null? l) 
      s
      (cons (car l) ((my-append (cdr l)) s))
      ))))

(((Y (lambda [my-append]
       (lambda [l]
        (lambda [s]
        (if (null? l) 
          s
          (cons (car l) ((my-append (cdr l)) s)))))))
 '(a b c))
 '(d e))

((((lambda (f)
     ((lambda (x)
        (f (x x)))
      (lambda (x) 
        (lambda (y)
        ((f (x x)) y))))) 
    
    (lambda [my-append]
       (lambda [l]
        (lambda [s]
        (if (null? l) 
          s
          (cons (car l) ((my-append (cdr l)) s)))))))
 '(a b c))
 '(d e))


(define myappendo
  (lambda (l s out)
    (conde
      [(== '() l) (== s out)]
      [(fresh (a d res)
              (== `(,a . ,d) l)
              (== out `(,a . ,res))
              (myappendo d s res))]
      )
    )
  )


(run* (q) (eval-expo `(eval (quote (cons (quote 5) (quote 6)))) '() q))
;(run 2 (q) (eval-expo q '() q))
