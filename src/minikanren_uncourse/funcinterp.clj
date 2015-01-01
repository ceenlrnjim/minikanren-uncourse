
; -----------------------------------------------------------------
; uncourse #4 - relational interpreters
; write an interpreter for subset of scheme in relational style
;
; call-by-value, environment passing, lambda calculus in scheme
; -----------------------------------------------------------------
(ns minikanren-uncourse.funcinterp
  (:use [clojure.core.match :only (match)]))

; interpreter for call-by-value lambda calculus that scheme is based on
; call-by-value since we have to evaluate all the arguments before we can pass them to 
;   a function invocation.  As opposed to call-by-name or call-by-need lazy evaluation (like Haskell)
; 3 types of fundamental expressions
; - 1: variables
; - 2: lambdas / anonymous functions - abstraction
; - 3: function application



; Note that list matching is not supported by core.match, using seq
;  which would technically match vectors etc. as well
;
(defn lookup [sym env]
  (match [env]
         ; match the empty sequence - break recursion
         [([] :seq)] (throw (IllegalArgumentException. (str "unbound variable: " sym)))
         ; first symbol in the list of pairs matches - we've found what we're looking for
         [([[sym v] & r] :seq)] v
         ; first symbol doesn't match, recur over the rest of the pairs
         [([[k v] & r] :seq)] (lookup sym r)))

(defn extend-env [env k v]
  (cons [k v] env))

(declare eval-exp)

(defn eval-exp* [expr* env]
  (cond
    (empty? expr*) '()
    :else (cons (eval-exp (first expr*) env) (eval-exp* (rest expr*) env))))

(defn eval-exp [expr env]
  (match [expr]
          
    ; Handle variable expansion
    [(x :guard symbol?) ] (lookup x env)

    ; numbers? (JLK extension)
    [(x :guard number?)] x

    ; add bindings to env (JLK extension)
    [(['let [(k :guard symbol?) v] body] :seq)]
      (eval-exp body (extend-env env k (eval-exp v env)))

    ; booleans - #t/#f causes problems due to # (reader macro?)
    [:t] true
    [:f] false

    ; if conditional
    [(['if pred t f] :seq)]
      (if (eval-exp pred env) 
        (eval-exp t env)
        (eval-exp f env))

    ; null?
    [(['null? e] :seq)] (empty? (eval-exp e env))

    ; empty list
    [([] :seq)] '()
         
    ; quote
    [(['quote x] :seq)] x

    [(['list & exprs] :seq)] 
         ;(map #(eval-exp % env) exprs)
         (eval-exp* exprs env)

    ; cons
    [(['cons h t] :seq)] 
       (cons (eval-exp h env) (eval-exp t env))
         
    ; car
    [(['car l] :seq)] (first (eval-exp l env))

    ; cdr
    [(['cdr l] :seq)] (rest (eval-exp l env))

    ; TODO: bool? zero?
    ; TODO: tagged numbers and arithmatic
    
          
    ; Handle abstraction - defining functions
         ; Using a tagged vector to represent functions
    [(['λ args body] :seq)] [:closure args body env] ; storing the environment is what give us lexical scope, shadowing, etc.
          
    ; Handle function application
       ; note that we're only supporting functions of one argument 
       ; everything should be curried
    [([e1 & args] :seq)]
      ; Note that in scheme order of evaluation between e1 and e2 is unspecified
      ; eval e1 - better eval to a closure, call it 'proc'
      ; eval e2 to some value
      ; apply proc to value
      (let [proc (eval-exp e1 env)
            values (map #(eval-exp % env) args)]
        ; note vector matching here, not seq since I create the closure data structure
        ; as a vector
        (match [proc]
               [[:closure proc-args body proc-env]] 
                  ; evaluate the body in an extended environment in which
                  ; the environment of the closure is extended with a binding between
                  ; x and value
                  (eval-exp body (reduce (fn [e [n v]] (extend-env e n v)) proc-env (map vector proc-args values))) ; using env here instead of proc-env would give dynamic instead of lexical scope
               [_] (throw (IllegalArgumentException. (str "e1 does not evaluate to a procedure" proc)))))
      
    ; Error - not a valid expression
    [_] (throw (IllegalArgumentException. (str "Invalid expression: " expr)))))


; Y combinator for eagerly evaluated, call by value, language
; "inverse eta"
;  Idea of eta: (lambda (x) (add1 x)) is the same as add1 (eta contraction)
;  so inverse eta: add1 => (lambda (x) (add1 x))  (eta expansion)
;
;  Mathematical definition of Y is:
;  Y x = x (Y x) fixed point combinator
(defn Y [f]
  ((fn [x] (f (x x))) 
   (fn [x] (fn [y] ((f (x x)) y)))))


; replacing with a new definition to make implementation in our interpreter simpler
(defn myappend2 [l]
  ; need to curry since our interpreter only takes one argument
  (fn [s]
    (if (empty? l) 
      s
      (cons (first l) ((myappend2 (rest l)) s)))))

; now a definition of append that doesn't require "define"
(((Y (fn [myappend3]
      (fn [l]
        (fn [s]
          (if (empty? l) 
            s
            (cons (first l) ((myappend3 (rest l)) s)))))))
 '(a b c)) '(d e))

; inline Y
((((fn [f]
    ((fn [x] (f (x x))) 
     (fn [x] (fn [y] ((f (x x)) y)))))

   (fn [myappend3]
      (fn [l]
        (fn [s]
          (if (empty? l) 
            s
            (cons (first l) ((myappend3 (rest l)) s)))))))
 '(a b c)) '(d e))


; examples of variable lookup
(comment
  
  (eval-exp 'x [['z 1] ['y 2] ['x 3]])
  (eval-exp 'y [['z 1] ['y 2] ['x 3]])
  (eval-exp 'a [['z 1] ['y 2] ['x 3]])

  ; example of abstraction
  (eval-exp '(λ [a] (+ a 2)) [['z 1] ['y 2] ['x 3]])

  ; examples of (successful and failed) application
  (eval-exp '((λ [z] z) y) [['y 5]])
  (eval-exp '(foo 2) [])
  (eval-exp '(foo 2) [['foo [:closure 'x 'x []]]])
  (eval-exp '(foo 2) [['foo (eval-exp '(λ [x] x) [])]])

  ; example of number extension
  (eval-exp '((λ [x] 42) y) [['y 5]])
  (eval-exp '())

  ;example of binding variables
  (eval-exp '(let [y 42] 
              ((λ [x] y) z)) 
            [['y 100] ['z 2]])

  (eval-exp '(let [foo (λ [x] x)] (foo 100)) [])

  ; if and booleans
  (eval-exp '(if y 1 0) [['y true]])
  (eval-exp '(if y 1 0) [['y false]])

  (eval-exp '(quote (1 2 3 4)) [])
  (eval-exp '(quote (λ (x) (λ (y) (cons x (cons y (quote ())))))) [])
  (eval-exp '(cons 4 (quote (2 ()))) [])
  (eval-exp '(car (quote (4 2))) [])
  (eval-exp '(cdr (quote (4 2))) [])

  ; list
  (eval-exp '(list 1 2 3 4 5 (car (quote (2 (quote ()))))) [])

  (eval-exp '(null? '()) [])
  (eval-exp '(null? (quote  (4))) [])
  (eval-exp '(null? (cdr (quote (4 2)))) [])
  (eval-exp '(null? (cdr (quote (4)))) [])

  (eval-exp '((λ [x] (car x)) (quote (2 3 4))) [])

  ; Inline Y and apply to definiton of myappend to have our evaluator execute it
  (eval-exp
   '((((λ [f]
      ((λ [x] (f (x x))) 
       (λ [x] (λ [y] ((f (x x)) y)))))

     (λ [myappend3]
        (λ [l]
          (λ [s]
            (if (null? l) 
              s
              (cons (car l) ((myappend3 (cdr l)) s)))))))
   (quote (a b c))) (quote (d e))) [])
  
  ; multiple argument functions/applications
  (eval-exp '((λ [x y z] (list x y z)) 1 2 3) [])
  )
 
  
; scheme list implementation
; ((lambda args args) 1 2 3 4 5)
; => (1 2 3 4 5)
