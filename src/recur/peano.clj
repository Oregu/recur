(ns recur.peano
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic]))

(defn zeroo [num]
  (== '(z) num))

(defn build-num [n]
  (into '(z) (repeat n 's)))

(defn inco [num num+]
  (all
   (!= '(z) num+)
   (conso 's num num+)))

(defn <o [n1 n2]
  (conde
   [(fresh [decr]
     (zeroo n1)
     (inco decr n2))]
   [(fresh [d1 d2]
     (inco d1 n1)
     (inco d2 n2)
     (<o d1 d2))]))

(defn <=1o [n v]
  (conde
   [(zeroo n)   (== v true)]
   [(== (peano '(s z)) n) (== v true)]
   [(!= '(z) n)
    (!= '(s z) n)
    (== v false)]))

(defn +o [a1 a2 s]
  (conde
   [(zeroo a1) (== s a2)]
   [(zeroo a2) (== s a1)]
   [(fresh [ts d1]
     (!= '(z) a1)
     (!= '(z) a2)
     (inco ts s)
     (inco d1 a1)
     (+o d1 a2 ts))]))
