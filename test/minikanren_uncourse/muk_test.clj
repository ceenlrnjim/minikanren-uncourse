(ns minikanren-uncourse.muk-test
  (:refer-clojure :exclude [==]) 
  (:use [minikanren-uncourse.muk])
  (:use [clojure.test]))

(deftest walk-test
  (is (= 5 (walk (lvar 0) (ext-s (lvar 0) 5 (constraint-store))))) 
  (is (= (lvar 0) (walk (lvar 0) (ext-s (lvar 1) (lvar 0) (constraint-store)))))
  (is (= (lvar 0) (walk (lvar 1) (ext-s (lvar 1) (lvar 0) (constraint-store)))))
  (is (= 5 (walk (lvar 1) (ext-s (lvar 1) (lvar 0) (ext-s (lvar 0) 5 (constraint-store)))))))


(deftest unify-test
  (is (= (constraint-store) (unify 5 5 (constraint-store))))
  (is (= false (unify 5 6 (constraint-store))))
  (is (= (constraint-store {(lvar 0) 6}) (unify (lvar 0) 6 (constraint-store))))
  (is (= false (unify (lvar 0) 6 (ext-s (lvar 0) 5 (constraint-store)))))
  (let [c (unify [(lvar 0) (lvar 1) (lvar 2)] [0 1 2] (constraint-store))]
    (is (= 0 (walk (lvar 0) c)))
    (is (= 1 (walk (lvar 1) c)))
    (is (= 2 (walk (lvar 2) c)))))
  
(deftest check-diseq-test
  (is (= {{:lvarid 0} 6} (check-diseq {(lvar 0) 5} {(lvar 0) 6})))
  (is (= false (check-diseq {(lvar 0) 6} {(lvar 0) 6})))
  (is (= {{:lvarid 0} 6} (check-diseq {(lvar 0) (lvar 1) (lvar 1) 5} {(lvar 0) 6})))
  (is (= false (check-diseq {(lvar 0) (lvar 1) (lvar 1) 6} {(lvar 0) 6})))
  (is (= {(lvar 0) (lvar 1)}) (check-diseq {(lvar 2) 5} {(lvar 0) (lvar 1) (lvar 2) 5}))
  )
  
(deftest check-disequalities-test
  (is (check-disequalities
    (constraint-store {(lvar 0) 5} [{(lvar 0) 6}])))
  (is (not (check-disequalities
    (constraint-store {(lvar 0) 6} [{(lvar 0) 6}]))))
  (is (check-disequalities (constraint-store {(lvar 2) 5} [{(lvar 0) (lvar 1) (lvar 2) 5}]))))
  
(deftest diseq-test
  (is (= false (diseq 5 5 (constraint-store))))
  (is (= (constraint-store) (diseq 5 6 (constraint-store))))
  (is (diseq (lvar 0) 6 (constraint-store)))
  (is (not (diseq (lvar 0) 6 {:substitution {(lvar 0) 6} :disequalities []})))
  (is (= [{(lvar 2) 5 (lvar 0) (lvar 1)}] (:disequalities (diseq [(lvar 0) (lvar 2)] [(lvar 1) 5] (constraint-store))))))

(deftest ==-test
  ; this would make a good generative test, the relationship between unify and ==
  (is (= (first ; grab the first answer from the stream
           ((== (lvar 0) 5) (constraint-store {} [] 10))) 
         (unify (lvar 0) 5 (constraint-store {} [] 10))))
  (is (= [] ((== 5 6) (constraint-store))))
  )

(deftest call-fresh-test
  (is (=
       ((call-fresh (fn [x] (== x 5))) (constraint-store))
       (unit (unify (lvar 0) 5 (increment-counter (constraint-store))))))
  (is (=
       ((call-fresh
          (fn [x] 
            (call-fresh 
              (fn [y]
                (== x y)))))
        (constraint-store))
       (unit (unify (lvar 0) (lvar 1) (increment-counter (increment-counter (constraint-store))))))))

(deftest mplus-test
  (is (= (mplus mzero [:a :b :c]) [:a :b :c]))
  (is (= (mplus [:a :b :c] mzero) [:a :b :c]))
  ; test append
  (is (= (mplus [:a :b :c] [:d :e :f]) [:a :b :c :d :e :f]))
  ; test "lazy" stream 
  )

(deftest bind-test
  (let [g (== (lvar 1) (lvar 0))
        c1 (unify (lvar 0) 5 (constraint-store))
        c2 (unify (lvar 2) 6 (constraint-store))
        res (bind (mplus (unit c1) (unit c2)) g)]
    (is (= 5 (walk (lvar 0) (first res))))
    (is (= 5 (walk (lvar 1) (first res))))
    (is (= (lvar 0) (walk (lvar 1) (second res))))
    (is (= 6 (walk (lvar 2) (second res))))))

(deftest !=-test
  (is (empty? ((!= 1 1) (constraint-store))))
  (is (= 1 (count ((!= (lvar 0) 5) (constraint-store))))))

(deftest μdisj-test
  (let [g1 (== (lvar 0) 5)
        g2 (== 5 6)
        res1 ((μdisj g1 g2) (constraint-store))
        res2 ((μdisj g2 g1) (constraint-store))]
    (is (= 1 (count res1)))
    (is (= 1 (count res2)))
    (is (empty? ((μdisj g2 g2) (constraint-store))))))


(deftest μconj-test
  (let [g1 (== (lvar 0) 5)
        g2 (== 5 6)
        res1 ((μconj g1 g2) (constraint-store))
        res2 ((μconj g2 g1) (constraint-store))]
    (is (empty? res1))
    (is (empty? res2))
    (is (= 1 (count ((μconj g1 g1) (constraint-store)))))))
