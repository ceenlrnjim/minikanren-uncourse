(ns minikanren-uncourse.core
  (:require [clojure.core.logic :as cl]))

; ------------------------------------
; Appendo
; ------------------------------------

; standard functional version
(defn append [l1 l2]
  (cond (empty? l1) l2
        :else (cons (first l1) (append (rest l1) l2))))

; relational version
; using - ==, conde, fresh ; goal constructors
(defn appendo [l s out]
  (cl/fresh [a d res]
    (cl/conde 
      [(cl/== '() l) (cl/== s out)]
      [
       ; where we would normally embed a function call and use its result,
       ; we instead need to first create a relation that "binds" the result to a value
       ; then use that value in our goal
       (cl/conso a d l)  
       (cl/conso a res out) 
       (appendo d s res) 
      ])) )
       ; inside of a fresh or other conjunction, if you have a recursive call, you
       ; want it to come last or some queries (like asking for 5 results when there are 4 in
       ; appendo queries) will go into and infinite loop

(cl/run 1 [out]
       (appendo '(1 2 3) out '(1 2 3 4 5)))

(time  (cl/run 5 [q y] (appendo q y '(1 2 3))))

; ------------------------------------
; Membero
; ------------------------------------

(defn member [item xs]
  (cond (empty? xs) false
        (= (first xs) item) xs
        :else (recur item (rest xs))))


(member 5 '(3 4 5 6 7))
(member 5 '(3 4 5 6 5 7))
(member 8 '(3 4 5 6 5 7))

(defn membero [item xs out]
  (cl/fresh [t]
    (cl/conde
      [(cl/== '() xs) (cl/== false out)]
      ; Note: we don't need a variable for the head of the list that we check for unification with 'item' -
      ; we can just use item directly in the conso call
      [(cl/conso item t xs) (cl/== xs out)]
      [(cl/resto xs t) (membero item t out)])))

(cl/run 1 [out]
        (membero 5 '() out))

(cl/run 1 [out]
        (membero 5 '(5 6 7) out))

(cl/run 1 [out]
        (membero out '(5 6 7) '(5 6 7)))

(cl/run 2 [out]
        (membero 5 '(3 4 5 6 5 7) out))
