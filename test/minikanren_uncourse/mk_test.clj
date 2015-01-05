(ns minikanren-uncourse.mk-test
  (:refer-clojure :exclude [reify])
  (:use [minikanren-uncourse.mk])
  (:use [clojure.test]))

(deftest walk-test
  (let [s [[(lvar :a) 1] [(lvar :b) 2] [(lvar :c) 3] [(lvar :a) 0]]]
    (is (= (walk (lvar :b) s) 2))
    (is (= (walk 4 s) 4))
    (is (= (walk (lvar :d) s) (lvar :d)))
    (is (= (walk (lvar :a) s) 1))))

(deftest ext-s-test
  (testing "ext-s"
    (is (= false (ext-s (lvar :a) (lvar :b) (ext-s (lvar :b) (lvar :a) (empty-s)))))
    (is (= false (ext-s (lvar :a) (lvar :a) (empty-s))))
    (is (= (walk (lvar :a)
                 (ext-s (lvar :a) 4 (empty-s)))
           4))))


(deftest unify-test
  (let [s-init (empty-s)
        s (unify (lvar :a) 1 s-init)
        s2 (unify (lvar :b) (lvar :a) s) 
        s3 (unify 2 (lvar :c) s2)
        ]
    (is (= (first s) [(lvar :a) 1]))
    (is (= (walk (lvar :b) s2) 1))
    (is (= (walk (lvar :c) s3) 2))
    (is (= false (unify (lvar :a) (lvar :c) s3)))
    ; TODO: add test that demonstrates additional safety of this version of unify
    (is (unify 4 4 (empty-s)))
    (is (not (unify 4 5 (empty-s))))))

(deftest unify-no-check-test
  (let [s-init (empty-s)
        s (unify-no-check (lvar :a) 1 s-init)
        s2 (unify-no-check (lvar :b) (lvar :a) s) 
        s3 (unify-no-check 2 (lvar :c) s2)
        ]
    (is (= (first s) [(lvar :a) 1]))
    (is (= (walk (lvar :b) s2) 1))
    (is (= (walk (lvar :c) s3) 2))
    (is (= false (unify-no-check (lvar :a) (lvar :c) s3)))
    (is (unify-no-check 4 4 (empty-s)))
    (is (not (unify-no-check 4 5 (empty-s))))))

(deftest walk*-test
  (let [s [[(lvar :z) 6] [(lvar :y) 5] [(lvar :x) [(lvar :y) (lvar :z)]]]]
    (is (= (walk (lvar :x) s) [(lvar :y) (lvar :z)]))
    (is (= (walk* (lvar :x) s) [5 6]))))
