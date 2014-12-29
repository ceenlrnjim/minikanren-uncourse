; implementation of minikanren based on William Byrd's thesis
; http://media.proquest.com/media/pq/classic/doc/1917964651/fmt/ai/rep/NPDF?_s=KE6%2BUJyAhZTbDJ1HBgiibUAvkK4%3D
; I am aware core.logic exists, this is just my attempt to understand how
; this magic stuff works
(ns minikanren-uncourse.mk
  )

(defn lvar [name]
  (vector name))

(defn lvar? [x]
  (vector? x))

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

(defn occurs [x v s]
  (let [sv (walk v s)]
    (cond
      (lvar? sv) (= sv x)
      ; TODO: lvar? is actually vector? so this won't work
      (vector? sv) (or 
                     (occurs x (first sv) s)
                     (occurs x (second sv) s))
      :else false)))

(defn ext-s [x v s]
  (if (occurs x v s) 
    false
    (ext-s-no-check x v s)))

