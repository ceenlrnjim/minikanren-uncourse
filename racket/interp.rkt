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
         ;;(absento 'closure out) ;; absento missing from racket minikanren?
         (unboundo 'quote env)]
        [(fresh (expr*)
           (== `(list . ,expr*) expr)
           (eval-exp*o expr* env out)
           (unboundo 'list env))]
        [(fresh (x body) ;; abstraction
           (== `(lambda (,x) ,body) expr)
           (== `(closure ,x ,body ,env) out)
           (symbolo x)
           (unboundo 'lambda env))]
        [(fresh (e1 e2 val x body envˆ) ;; application
           (== `(,e1 ,e2) expr)
           (eval-expo e1 env `(closure ,x ,body ,envˆ))
           (eval-expo e2 env val)
           (eval-expo body `((,x . ,val) . ,envˆ) out))]))))

(define eval-exp*o
  (lambda (expr* env out)
    (conde
      [(== '() expr*) (== '() out)]
      [(fresh (a d res-a res-d)
         (== (cons a d) expr*)
         (== (cons res-a res-d) out)
         (eval-expo a env res-a)
         (eval-exp*o d env res-d))])))

(run 2 (expr) (eval-expo expr '() '(I love you)))

;; Quines
;(run 1 (q) (eval-expo q '() q))
