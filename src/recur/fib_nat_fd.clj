(ns recur.fib-nat-fd
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.core.logic.protocols :as ps]))


;; Fibonacci recursive program evaluator
;; with natural numbers and CLP(FD).


#_(defn symbolo [x] (predc x symbol?))
#_(defn numbero [x] (predc x number?))

(declare numbero*)

(defn symbolo* [x]
  (reify
    ps/IConstraintStep
    (-step [this s]
      (reify
        clojure.lang.IFn
        (invoke [_ s]
          (let [x (ps/walk s x)]
            (when (symbol? x)
              ((remcg this) s))))
        ps/IRunnable
        (-runnable? [_]
          (not (lvar? (ps/walk s x))))))
    ps/IVerifyConstraint
    (-verify [_ a cs]
      (not (some (fn [c] (= (ps/-rator c) `numbero))
                 (map (:cm cs) (get (:km cs) (ps/root-var a x))))))
    ps/IConstraintOp
    (-rator [_] `symbolo)
    (-rands [_] [x])
    ps/IReifiableConstraint
    (-reifyc [c v r s]
      (when-not (lvar? (ps/walk r x))
        `(symbolo ~(-reify s x r))))
    ps/IConstraintWatchedStores
    (-watched-stores [this] #{:clojure.core.logic/subst})))

(defn symbolo [x]
  (cgoal (symbolo* x)))

(defn numbero* [x]
  (reify
    ps/IConstraintStep
    (-step [this s]
      (reify
        clojure.lang.IFn
        (invoke [_ s]
          (let [x (ps/walk s x)]
            (when (number? x)
              ((remcg this) s))))
        ps/IRunnable
        (-runnable? [_]
          (not (lvar? (ps/walk s x))))))
    ps/IVerifyConstraint
    (-verify [_ a cs]
      (not (some (fn [c] (= (ps/-rator c) `symbolo))
                 (map (:cm cs) (get (:km cs) (ps/root-var a x))))))
    ps/IConstraintOp
    (-rator [_] `numbero)
    (-rands [_] [x])
    ps/IReifiableConstraint
    (-reifyc [c v r s]
      (when-not (lvar? (ps/walk r x))
        `(numbero ~(-reify s x r))))
    ps/IConstraintWatchedStores
    (-watched-stores [this] #{:clojure.core.logic/subst})))

(defn numbero [x]
  (cgoal (numbero* x)))

(defn listo   [x] (predc x coll?))
(defn booleano [x] (predc x (fn [b] (or (true? b) (false? b)))))

(declare eval-expo)

(defn lookupo [x env t]
  (fresh [rest y v]
   (conso `(~y ~v) rest env)
   (symbolo y)
   (symbolo x)
   (conde
    [(symbolo x)
     (== y x)
     (== v t)]
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
     (symbolo x)
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
    (numbero val) ;; TODO Wrong, but fails in lookupo without it
    (lookupo exp env val)]
   [(numbero exp)
    (numbero val)
    (== exp val)]
   [(fresh [rator rand x body env- a env+ selves+]
           (listo exp)
           (== `(~rator ~rand) exp)
           (eval-expo rator env selves `(~'closure ~x ~body ~env-))
           (eval-expo rand env selves a)
           (conso `(~x ~a) env- env+)
           (conso `(~'closure ~x ~body ~a ~env-) selves selves+)
           (eval-expo body env+ selves+ val))]
   [(fresh [x body]
           (listo exp)
           (== `(~'fn [~x] ~body) exp)
           (symbolo x)
           (not-in-envo 'fn env)
           (== `(~'closure ~x ~body ~env) val))]
   [(fresh [selfarg argv prevargv x body env- env+ t]
           (listo exp)
           (== `(~'recur ~selfarg) exp)
           (not-in-envo 'recur env)
           ;; TODO since I put arg to selves list
           ;; need update it when recurring
           (numbero prevargv)
           (conso `(~'closure ~x ~body ~prevargv ~env-) t selves)
           (symbolo x)
           (numbero argv)
           (eval-expo selfarg env selves argv)
           #_(mentionso x selfarg)
           (fd/in argv prevargv (fd/interval 20)) ;; TODO
           (fd/< argv prevargv)
           (conso `(~x ~argv) env- env+)
           (eval-expo body env+ selves val))]
   [(fresh [e1 e2 e3 t]
           (listo exp)
           (== `(~'if ~e1 ~e2 ~e3) exp)
           (not-in-envo 'if env)
           (booleano t) (conde [(== t true)] [(== t false)])
           (eval-expo e1 env selves t)
           (conde
            [(== true  t)
             (eval-expo e2 env selves val)]
            [(== false t)
             (eval-expo e3 env selves val)]))]
   [(fresh [a n]
           (listo exp)
           (== `(~'dec ~a) exp)
           (not-in-envo 'dec env)
           (numbero val)
           (numbero n)
           (!= val true) (!= val false)
           (!= n true) (!= n false)
           (eval-expo a env selves n)
           (fd/in n val (fd/interval 20)) ;; TODO
           (fd/+ 1 val n))]
   [(fresh [a l]
           (listo exp)
           (== `(~'<=1 ~a) exp)
           (not-in-envo '<=1 env)
           (numbero l)
           (eval-expo a env selves l)
           (conde
            [(== l 0) (== val true)]
            [(== l 1) (== val true)]
            [(!= l 0) (!= l 1) (fd/> l 1) (== val false)]))]
   [(fresh [a1 a2 va1 va2]
           (listo exp)
           (== `(~'+ ~a1 ~a2) exp)
           (not-in-envo '+ env)
           (numbero va1)
           (numbero va2)
           (numbero val)
           (!= va1 true) (!= va1 false)
           (!= va2 true) (!= va2 false)
           (!= val true) (!= val false)
           (eval-expo a1 env selves va1)
           (eval-expo a2 env selves va2)
           (fd/in va1 va2 val (fd/interval 20)) ;; TODO
           (fd/+ va1 va2 val))]))

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
