(ns minikanren-uncourse.core
  (:require [clojure.core.logic :as cl]))


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

(defn -main []
  (println
    (cl/run 1 [out]
             (appendo '(1 2 3) '(4 5) out)
         )))

(time  (cl/run 5 [q y] (appendo q y '(1 2 3))))
