(ns recur.fib-peano
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic]
        [recur.peano]))


;; Recursive evaluator of Fibonacci program with peano numbers.
;; Evaluates (fib 7) in 180ms
;; Wasn't able to synthesize one in 2 hours.

;; Maybe I can speed up evaluation?
;; This double recursion mess things.


(defn symbolo [x] (predc x symbol?))

(declare eval-expo)

(defn lookupo [x env t]
  (fresh [rest y v]
   (conso `(~y ~v) rest env)
   (conde
    [(== y x) (== v t)]
    [(!= y x) (lookupo x rest t)])))

(defn not-in-envo [x env]
  (conde
   [(fresh [y v rest]
     (conso `(~y ~v) rest env)
     (!= y x)
     (not-in-envo x rest))]
   [(== '() env)]))

(defn proper-listo [exp env selves val]
  (conde
   [(== '() exp)
    (== '() val)]
   [(fresh [a d t-a t-d]
     (conso   a   d exp)
     (conso t-a t-d val)
     (eval-expo a env selves t-a)
     (proper-listo d env selves t-d))]))

(defn mentionso [x form]
  (conde
   [(fresh [h t]
     (conso h t form)
     (symbolo h)
     (== h x))]
   [(fresh [h t]
     (!= h x)
     (symbolo h)
     (conso h t form)
     (mentionso x t))]
   [(fresh [h t]
     (!= h x)
     (conso h t form)
     (mentionso x h))]))

(defn eval-expo [exp env selves val]
  (conde
   [(symbolo exp)
    (lookupo exp env val)]
   [(fresh [rator rand x body env- a env2 selves2]
     (== `(~rator ~rand) exp)
     (eval-expo rator env selves `(~'closure ~x ~body ~env-))
     (eval-expo rand env selves a)
     (conso `(~x ~a) env- env2)
     (conso `(~'closure ~x ~body ~env-) selves selves2)
     (eval-expo body env2 selves2 val))]
   [(fresh [x body]
     (== `(~'fn [~x] ~body) exp)
     (symbolo x)
     (not-in-envo 'fn env)
     (== `(~'closure ~x ~body ~env) val))]
   [(fresh [selfarg argv prevargv x body env- env2 t]
     (== `(~'recur ~selfarg) exp)
     (not-in-envo 'recur env)
     (conso `(~'closure ~x ~body ~env-) t selves)
     (lookupo x env prevargv)
     (mentionso x selfarg)
     (eval-expo selfarg env selves argv)
     (<o argv prevargv)
     (conso `(~x ~argv) env- env2)
     (eval-expo body env2 selves val))]
   [(fresh [e1 e2 e3 t]
     (== `(~'if ~e1 ~e2 ~e3) exp)
     (not-in-envo 'if env)
     (eval-expo e1 env selves t)
     (conde
      [(== true  t) (eval-expo e2 env selves val)]
      [(== false t) (eval-expo e3 env selves val)]))]
   [(== `(~'zero) exp)
    (not-in-envo 'zero env)
    (zeroo val)]
   [(fresh [a n]
     (== `(~'inc ~a) exp)
     (not-in-envo 'inc env)
     (eval-expo a env selves n)
     (inco n val))]
   [(fresh [a n]
     (== `(~'dec ~a) exp)
     (not-in-envo 'dec env)
     (eval-expo a env selves n)
     (inco val n))]
   [(fresh [a l]
     (== `(~'<=1 ~a) exp)
     (not-in-envo '<=1 env)
     (<=1o l val)
     (eval-expo a env selves l))]
   [(fresh [a1 a2 va1 va2]
     (== `(~'+ ~a1 ~a2) exp)
     (not-in-envo '+ env)
     (eval-expo a1 env selves va1)
     (eval-expo a2 env selves va2)
     (+o va1 va2 val))]))

;; Fibonacci

(let [fibfn '(fn [x]
               (if (<=1 x)
                 x
                 (+ (recur (dec x))
                    (recur (dec (dec x))))))]

  ;; (fibo 7) ~180 ms
  (defn eval-fib []
    (run 1 [q]
         (eval-expo `(~fibfn ~'(inc (inc (inc (inc (inc (inc (inc (zero)))))))))
                    '() '() q))))

(defn gen-fib []
  (run 1 [q]
   (eval-expo `(~q ~'(zero)) '() '() (build-num 0))
   (eval-expo `(~q ~'(inc (zero))) '() '() (build-num 1))
   (eval-expo `(~q ~'(inc (inc (zero)))) '() '() (build-num 1))
   (eval-expo `(~q ~'(inc (inc (inc (zero))))) '() '() (build-num 2))
   (eval-expo `(~q ~'(inc (inc (inc (inc (zero)))))) '() '() (build-num 3))
   (eval-expo `(~q ~'(inc (inc (inc (inc (inc (zero))))))) '() '() (build-num 5))
   #_(eval-expo `(~q ~'(inc (inc (inc (inc (inc (inc (zero)))))))) '() '() (build-num 8))))
