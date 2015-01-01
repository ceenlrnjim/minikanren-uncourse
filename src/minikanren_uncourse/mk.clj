; implementation of minikanren based on William Byrd's thesis
; http://media.proquest.com/media/pq/classic/doc/1917964651/fmt/ai/rep/NPDF?_s=KE6%2BUJyAhZTbDJ1HBgiibUAvkK4%3D
; I am aware core.logic exists, this is just my attempt to understand how
; this magic stuff works
(ns minikanren-uncourse.mk
  )

(defn lvar [name]
  (vector name))

(defn lvar? [x]
  (and (vector? x) (= (count x) 1)))

; empty substitution
(defn empty-s [] [])


; TODO: can I use maps?  do I need the ability to override values?
(defn assq [v l]
  (cond (empty? l) nil
        (= (ffirst l) v) (first l)
        :else (recur v (rest l))))

(defn walk [v s]
  (cond 
    (lvar? v) (let [a (assq v s)]
                (cond
                  a (walk (second a) s)
                  :else v))
    :else v))

(defn ext-s-no-check [x v s]
  (cons [x v] s))

(defn pair? [x]
  (and (vector? x) (= (count x) 2)))

(defn occurs [x v s]
  (let [sv (walk v s)]
    (cond
      (lvar? sv) (= sv x)
      (pair? sv) (or 
                     (occurs x (first sv) s)
                     (occurs x (second sv) s))
      :else false)))

(defn ext-s [x v s]
  (if (occurs x v s) 
    false
    (ext-s-no-check x v s)))

; TODO: left off here - need to understand this before proceeding
(defn unify [u v s]
  (let [u (walk u s)  ;note shadowing
        v (walk v s)] ;note shadowing
    (cond
      (= u v) s ; they are already the same in s, no change
      (lvar? u) ; still a variable, not in s
        (if (lvar? v)
          (ext-s-no-check u v s) ; unifying two lvars, since these are still lvars, they don't exist in the substitution and can be unified
          (ext-s u v s)) ; since v isn't a var it is in s somewhere and we need to check for circularity
      (lvar? v) (ext-s v u s) ; u is not a variable, so again we need to check for circularity
      (and (pair? u) (pair? v)) ; both are already in s
        (let [s (unify (first u) (first v) s)]
          (and s (unify (second u) (second v) s)))
      :else false)))
