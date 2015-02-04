(ns minikanren-uncourse.muk-test
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
  (is (= false (unify (lvar 0) 6 (ext-s (lvar 0) 5 (constraint-store))))))
  
(deftest check-diseq-test
  (is (= {{:lvarid 0} 6} (check-diseq {(lvar 0) 5} {(lvar 0) 6})))
  (is (= false (check-diseq {(lvar 0) 6} {(lvar 0) 6})))
  (is (= {{:lvarid 0} 6} (check-diseq {(lvar 0) (lvar 1) (lvar 1) 5} {(lvar 0) 6})))
  (is (= false (check-diseq {(lvar 0) (lvar 1) (lvar 1) 6} {(lvar 0) 6})))
  )
  
(deftest check-disequalities-test
  (is (check-disequalities
    (constraint-store {} [{(lvar 0) 6}])
    (constraint-store {(lvar 0) 5} [{(lvar 0) 6}])))
  (is (not (check-disequalities
    (constraint-store {} [{(lvar 0) 6}])
    (constraint-store {(lvar 0) 6} [{(lvar 0) 6}])))))
  
(deftest diseq-test
  (is (= false (diseq 5 5 (constraint-store))))
  (is (= (constraint-store) (diseq 5 6 (constraint-store))))
  (is (diseq (lvar 0) 6 (constraint-store)))
  (is (not (diseq (lvar 0) 6 {:substitution {(lvar 0) 6} :disequalities []})))
  (is (= [{(lvar 2) 5 (lvar 0) (lvar 1)}] (:disequalities (diseq [(lvar 0) (lvar 2)] [(lvar 1) 5] (constraint-store))))))
