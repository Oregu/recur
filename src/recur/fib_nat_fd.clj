(ns recur.fib-nat-fd
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic])
  (:require [clojure.core.logic.fd :as fd]))


;; Fibonacci recursive program evaluator
;; with natural numbers and CLP(FD).


(defn symbolo [x] (predc x symbol?))
(defn numbero [x] (predc x number?))
(defn booleano [x] (predc x (fn [b] (or (true? b) (false? b)))))

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
   [(symbolo exp) (lookupo exp env val)]
   [(numbero exp) (== exp val)]
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
           (numbero argv)
           (numbero prevargv)
           #_(fd/in argv prevargv (fd/interval 20)) ;; TODO
           (trace-lvars "self" [exp val argv prevargv])
           #_(fd/< argv prevargv)
           (conso `(~x ~argv) env- env2)
           (eval-expo body env2 selves val))]
   [(fresh [e1 e2 e3 t]
           (== `(~'if ~e1 ~e2 ~e3) exp)
           (not-in-envo 'if env)
           (eval-expo e1 env selves t)
           (conde
            [(== true  t)
             (eval-expo e2 env selves val)]
            [(== false t)
             (eval-expo e3 env selves val)]))]
   [(fresh [a n]
           (== `(~'dec ~a) exp)
           (not-in-envo 'dec env)
           (numbero val)
           (numbero n)
           (!= val true) (!= val false)
           (!= n true) (!= n false)
           (fd/in n val (fd/interval 20)) ;; TODO
           (trace-lvars "dec" [exp val n])
           (fd/+ 1 val n)
           (eval-expo a env selves n))]
   [(fresh [a l]
           (== `(~'<=1 ~a) exp)
           (not-in-envo '<=1 env)
           (booleano val)
           (numbero l)
           (eval-expo a env selves l)
           (conde
            [(== l 0) (== val true)]
            [(== l 1) (== val true)]
            [(!= l 0) (!= l 1) (fd/> l 1) (== val false)]))]
   [(fresh [a1 a2 va1 va2]
           (== `(~'+ ~a1 ~a2) exp)
           (not-in-envo '+ env)
           (numbero va1)
           (numbero va2)
           (numbero val)
           (!= va1 true) (!= va1 false)
           (!= va2 true) (!= va2 false)
           (!= val true) (!= val false)
           (fd/in va1 va2 val (fd/interval 20)) ;; TODO
           (trace-lvars "+" [exp val va1 va2])
           (fd/+ va1 va2 val)
           (eval-expo a1 env selves va1)
           (eval-expo a2 env selves va2))]))

(defn evalo [e v]
  (eval-expo e '() '() v))

;; Fibonacci

(let [fibfn '(fn [x]
               (if (<=1 x)
                 x
                 (+ (recur (dec x))
                    (recur (dec (dec x))))))]

  ;; ~150ms to evaluate (fib 7)
  (defn eval-fib []
    (run 1 [q]
     (evalo `(~fibfn 7) q))))

(defn gen-fib []
  (run 1 [q]
   (evalo `(~q 0) 0)
   (evalo `(~q 1) 1)
   (evalo `(~q 2) 1)
   (evalo `(~q 3) 2)
   (evalo `(~q 4) 3)
   (evalo `(~q 5) 5)))
