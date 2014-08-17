(ns recur.test.len
  (:refer-clojure :exclude [==])
  (:use     [clojure.test])
  (:require [recur.len :as r]
            [clojure.core.logic :as l]))

(deftest t-eval-zero
  (is (= (l/run 1 [q]
                (r/eval-expo '(zero) '() '() q))
         '((z)))
      "Evaluate zero function."))

(deftest t-eval-inc

  (is (= (l/run 1 [q]
                (r/eval-expo '(inc (inc (zero))) '() '() q))
         '((s s z)))
      "Evaluate inc function with function returning number."))

(deftest t-eval-empty?
  (is (= (l/run 1 [q]
                (r/eval-expo '(empty? (list)) '() '() q))
         '(true)))

  (is (= (l/run 1 [q]
                (r/eval-expo '(empty? (list (zero))) '() '() q))
         '(false))))

(deftest t-eval-first
  (is (= (l/run 1 [q]
                (r/eval-expo '(first (list)) '() '() q))
         '()))

  (is (= (l/run 1 [q]
                (r/eval-expo '(first (list (zero))) '() '() q))
         '((z))))

  (is (= (l/run 1 [q]
                (r/eval-expo '(first (list (zero))) '() '() q))
         '((z)))))

(deftest t-eval-rest
  (is (= (l/run 1 [q]
                (r/eval-expo '(rest (list)) '() '() q))
         '()))

  (is (= (l/run 1 [q]
                (r/eval-expo '(rest (list (inc (zero)))) '() '() q))
         '(())))

  (is (= (l/run 1 [q]
                (r/eval-expo '(rest (list (zero) (inc (zero)))) '() '() q))
         '(((s z)))))

  (is (= (l/run 1 [q]
                (r/eval-expo '((fn [a] (first (rest (list a a))))
                               (inc (zero))) '() '() q))
         '((s z)))))

(deftest t-eval-if
  (is (= (l/run 1 [q]
                (r/eval-expo '(if (empty? (list))
                                (zero)
                                (inc (zero)))
                             '() '() q))
         '((z))))

  (is (= (l/run 1 [q]
                (r/eval-expo '(if (empty? (list (zero)))
                                (zero)
                                (inc (zero)))
                             '() '() q))
         '((s z)))))

(deftest t-eval-recur
  (let [lnfn '(fn [x]
                (if (empty? x)
                  (zero)
                  (inc (recur (rest x)))))]

    (is (= (l/run 1 [q]
                  (r/eval-expo `(~lnfn ~'(list)) '() '() q))
           '((z)))
        "Should return correct length of empty list.")

    (is (= (l/run 1 [q]
                  (r/eval-expo `(~lnfn ~'(list (zero) (inc (zero)) (zero)))
                               '() '() q))
           '((s s s z)))
        "Should return correct length of list with three elements.")))

#_(deftest t-synth
  (is (= (first
          (first
           (l/run 1 [q]
                  (r/eval-expo `(~q ~'(list (zero) (inc (zero))))
                               '() '() '(s z))
                  (r/eval-expo `(~q ~'(list (inc (zero)) (zero)))
                               '() '() '(z)))))
         '(fn [_0] (first (rest _0))))
      "Can generate second function from examples."))
