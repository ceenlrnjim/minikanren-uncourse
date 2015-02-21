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
  (is (check-disequalities (constraint-store {(lvar 2) 5} [{(lvar 0) (lvar 1) (lvar 2) 5}])))
  (is (check-disequalities (constraint-store {(lvar 0) (lvar 3)} [{(lvar 0) 0 (lvar 1) 1 (lvar 2) 2 (lvar 3) 3}]))))
  
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
  (is (= (mplus mzero mzero) mzero))
  (is (= (mplus mzero [:a :b :c]) [:a :b :c]))
  (is (= (mplus [:a :b :c] mzero) [:a :b :c]))
  ; test append
  (is (= (mplus [:a :b :c] [:d :e :f]) [:a :b :c :d :e :f]))
  ; fn then list
  (let [s (mplus (fn [] [:a :b :c]) [:d :e :f])]
    (is (fn? s))
    (is (= (s) [:d :e :f :a :b :c])))
  (let [s (mplus [:d :e :f] (fn [] [:a :b :c]))]
    (is (= (take 3 s) [:d :e :f]))
    (is (fn? (last s)))
    (is (fn? (cdr-stream (drop 2 s))))))

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

(deftest μdisj+-test
  (let [s1 ((call-fresh (fn [x] (μdisj+ (== x 5) (== x 6) (== x 7)))) (constraint-store))
        s2 ((call-fresh (fn [x] (μdisj (== x 5) (μdisj (== x 6) (== x 7))))) (constraint-store))]
    (is (= s1 s2))))

(deftest μconj+-test
  (let [s1 ((call-fresh (fn [x] (μconj+ (!= x 5) (!= x 6) (!= x 7)))) (constraint-store))
        s2 ((call-fresh (fn [x] (μconj (!= x 5) (μconj (!= x 6) (!= x 7))))) (constraint-store))]
    (is (= s1 s2))))

(deftest conde-test
  ; test disj
  (let [s1 ((call-fresh (fn [x] (conde [(== x 5)] [(== x 6)]))) (constraint-store))
        s2 ((call-fresh (fn [x] (μdisj (== x 5) (== x 6)))) (constraint-store))]
    (is (= s1 s2)))
  ; conj test
  (let [s1 ((call-fresh (fn [x] (conde [(!= x 5) (!= x 6)]))) (constraint-store))
        s2 ((call-fresh (fn [x] (μconj (!= x 5) (!= x 6)))) (constraint-store))]
    (is (= s1 s2))))

(deftest fresh+-test
  (let [s1 (call-goal (fresh+ [x y] (== x y)))
        s2 (call-goal (call-fresh (fn [x] (call-fresh (fn [y] (== x y))))))]
    (is (= s1 s2))))

(deftest fresh-test
  (let [s1 (call-goal (fresh [x y z] (== x y) (== y z)))
        s2 (call-goal (call-fresh 
                   (fn [x]
                     (call-fresh
                       (fn [y]
                         (call-fresh
                           (fn [z]
                             (μconj
                               (== x y) (== y z)))))))))]
    (is (= s1 s2))))

(deftest recursive-goal-constructor-test
  (defn fives [x]
    (μdisj
      (== x 5)
      (zzz (fives x))))

  (defn sixes [x]
    (μdisj 
      (== x 6)
      (zzz (sixes x))))

  (defn fives-and-sixes
    [x]
    (μdisj (fives x) (sixes x)))

  (let [res (take-n 4 (call-goal (call-fresh fives-and-sixes)))]
    (is (= (get (substitution (nth res 0)) (lvar 0)) 5))
    (is (= (get (substitution (nth res 1)) (lvar 0)) 6))
    (is (= (get (substitution (nth res 2)) (lvar 0)) 5))
    (is (= (get (substitution (nth res 3)) (lvar 0)) 6))
    )
  )

(deftest symbolo-test
  (is (= mzero (call-goal (fresh [x] (== x 5) (symbolo x)))))
  (is (= 1 (count (call-goal (fresh [x] (== x 'foo) (symbolo x))))))
  (is (= mzero (call-goal (fresh [x] (symbolo x) (== x 5)))))
  (is (= [(lvar 0)] (:symbols (first (call-goal (fresh [x] (symbolo x)))))))
  (is (= [] (:symbols (first (call-goal (fresh [x] (symbolo x) (== x 'foo)))))))
  )



(deftest numbero-test
  (is (= mzero (call-goal (fresh [x] (== x "a") (numbero x)))))
  (is (= 1 (count (call-goal (fresh [x] (== x 5) (numbero x))))))
  (is (= mzero (call-goal (fresh [x] (numbero x) (== x "a")))))
  (is (= [(lvar 0)] (:numbers (first (call-goal (fresh [x] (numbero x)))))))
  (is (= [] (:numbers (first (call-goal (fresh [x] (numbero x) (== x 5)))))))
  )

(deftest conso-test
  (let [r1 (call-goal (fresh [x y z] (conso x y z)))]
    (is (= 1 (count r1)))
    (is (= 1 (count (consos (first r1)))))) 
  (let [r2 (call-goal (fresh [x y z] (== x 5) (conso x y z))) ; head only bound
        r3 (call-goal (fresh [x y] (== x 5) (conso x y [5 6 7]))) ; head and result bound
        r4 (call-goal (fresh [x y] (== x 5) (== y [6 7]) (conso x y [5 6 7]))) ; all three bound - pass
        r5 (call-goal (fresh [x y] (== x 5) (== y [6 7]) (conso x y [5 8 9]))) ; all three bound - fail
        r6 (call-goal (fresh [x] (conso 5 [6 7] x)))   ; head and tail bound
        r7 (call-goal (fresh [h t] (conso h t [1 2 3]) (== t 5))) ; update after constraint - fail
        ]
    
    )
  
  )
