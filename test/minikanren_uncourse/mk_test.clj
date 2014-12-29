(ns minikanren-uncourse.mk-test
  (:use [minikanren-uncourse.mk])
  (:use [clojure.test]))

(deftest walk-test
  (let [s [[(lvar :a) 1] [(lvar :b) 2] [(lvar :c) 3] [(lvar :a) 0]]]
    (is (= (walk (lvar :b) s) 2))
    (is (= (walk 4 s) 4))
    (is (= (walk (lvar :d) s) (lvar :d)))
    (is (= (walk (lvar :a) s) 1))
    ))

(deftest ext-s-test
  (is (= false (ext-s (lvar :a) (lvar :b) (ext-s (lvar :b) (lvar :a) (empty-s)))))
  )

