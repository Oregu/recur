(ns recur.test.peano
  (:refer-clojure :exclude [==])
  (:use     [clojure.test])
  (:require [recur.peano :as r]
            [clojure.core.logic :as l]))

(deftest t-zeroo
  (is (= (l/run* [q] (r/zeroo q))
         '((z)))))

(deftest t-inco
  (is (= (l/run* [q] (r/inco '(z) q))
         '((s z))))

  (is (= (l/run* [q] (r/inco '(s s z) q))
         '((s s s z))))

  (is (= (l/run* [q] (r/inco q '(s s s z)))
         '((s s z)))))

