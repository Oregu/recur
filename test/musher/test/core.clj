(ns musher.test.core
  (:refer-clojure :exclude [==])
  (:use     [clojure.test])
  (:require [musher.core :as m]
            [clojure.core.logic :as l]))

(deftest t-zeroo
  (is (= (l/run* [q] (m/zeroo q))
         '((:num z)))))

(deftest t-inco
  (is (= (l/run* [q] (m/inco '(:num z) q))
         '((:num s z))))

  (is (= (l/run* [q] (m/inco '(:num s s z) q))
         '((:num s s s z))))

  (is (= (l/run* [q] (m/inco q '(:num s s s z)))
         '((:num s s z)))))

(deftest t-eval-zero
  (is (= (l/run 1 [q]
                (m/eval-expo '(zero) '() q))
         '((:num z)))
      "Evaluate zero function."))

(deftest t-eval-inc

  (is (= (l/run 1 [q]
                (m/eval-expo '(inc (inc (zero))) '() q))
         '((:num s s z)))
      "Evaluate inc function with function returning number."))

(deftest t-eval-empty?
  (is (= (l/run 1 [q]
                (m/eval-expo '(empty? (list)) '() q))
         '(true)))

  (is (= (l/run 1 [q]
                (m/eval-expo '(empty? (list (zero))) '() q))
         '(false))))

(deftest t-eval-first
  (is (= (l/run 1 [q]
                (m/eval-expo '(first (list)) '() q))
         '()))

  (is (= (l/run 1 [q]
                (m/eval-expo '(first (list (zero))) '() q))
         '((:num z))))

  (is (= (l/run 1 [q]
                (m/eval-expo '(first (list (zero))) '() q))
         '((:num z)))))

(deftest t-eval-rest
  (is (= (l/run 1 [q]
                (m/eval-expo '(rest (list)) '() q))
         '()))

  (is (= (l/run 1 [q]
                (m/eval-expo '(rest (list (inc (zero)))) '() q))
         '(())))

  (is (= (l/run 1 [q]
                (m/eval-expo '(rest (list (zero) (inc (zero)))) '() q))
         '(((:num s z)))))

  (is (= (l/run 1 [q]
                (m/eval-expo '((fn [a] (first (rest (list a a))))
                               (inc (zero))) '() q))
         '((:num s z)))))

(deftest t-eval-if
  (is (= (l/run 1 [q]
                (m/eval-expo '(if (empty? (list))
                                (zero)
                                (inc (zero)))
                             '() q))
         '((:num z))))

  (is (= (l/run 1 [q]
                (m/eval-expo '(if (empty? (list (zero)))
                                (zero)
                                (inc (zero)))
                             '() q))
         '((:num s z)))))

(deftest t-eval-self
  (let [lnfn '(fn [x]
                (if (empty? x)
                  (zero)
                  (inc (self (rest x)))))]

    (is (= (l/run 1 [q]
                  (m/eval-expo `(~lnfn ~'(list)) '() q))
           '((:num z)))
        "Should return correct length of empty list.")

    (is (= (l/run 1 [q]
                  (m/eval-expo `(~lnfn ~'(list (zero) (inc (zero)) (zero)))
                               '() q))
           '((:num s s s z)))
        "Should return correct length of list with three elements.")))

(deftest t-synth
  (is (= (first
          (first
           (l/run 1 [q]
                  (m/eval-expo `(~q ~'(list (zero) (inc (zero))))
                               '() '(:num s z))
                  (m/eval-expo `(~q ~'(list (inc (zero)) (zero)))
                               '() '(:num z)))))
         '(fn [_0] (first (rest _0))))
      "Can generate second function from examples."))
