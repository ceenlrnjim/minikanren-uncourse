(ns minikanren-uncourse.relinterp-test
  (:refer-clojure :exclude [== list cons quote])
  (:use [clojure.core.logic :exclude [is]])
  (:require [clojure.test :refer :all]
            [minikanren-uncourse.relinterp :refer :all]))

(deftest test-lookupo
  (testing "matching lookup"
    (is (= 1 (first (run 1 [out] (lookupo 'x [['x 1]] out))))))
  (testing "no matching lookup"
    (is (empty? (run 1 [out] (lookupo 'x [['y 1]] out)))))
  (testing "override lookup"
    (is (= 2 (first (run 1 [out] (lookupo 'x [['x 2] ['x 1]] out)))))))

(deftest test-eval-symbol
  (is (= 1 (first (run 1 [out] (eval-expo `a [[`a 1]] out))))))

(deftest test-eval-lambda
  (let [r (first (run 1 [out] (eval-expo `(λ (x) x) [[`y 42]] out)))]
    (println r)
    (is (vector? r))
    (is (= 4 (count r)))
    (is (= :closure (first r)))))


