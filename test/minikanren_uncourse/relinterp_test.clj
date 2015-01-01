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

(deftest test-eval-application
  (let [r (first (run 1 [out] (eval-expo `((λ (x) x) y) [[`y 42]] out)))]
    (is (= r 42))))

(deftest test-eval-with-symbol-shadow
  (let [r (first (run 1 [out] (eval-expo `((λ (λ) λ) x) [[`x 1]] out)))]
    (is (= r 1))))

(deftest test-quote
  (let [r (first (run 2 [out] (eval-expo `(quote foobar) [] out)))]
   (is (= r `foobar))))

(deftest test-list
  (let [l1 (first (run 1 [out] (eval-expo `(list '() '() '()) [] out)))
        l2 (first (run 2 [out] (eval-expo `(list a b c d e) [[`a 1] [`b 2] [`c 3] [`d 4] [`e 5]] out))) ]
    (is (= l1 '(() () ())))
    (is (= l2 '(1 2 3 4 5)))))


