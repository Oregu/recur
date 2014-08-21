(ns recur.fact-nat-fd
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.core.logic.protocols :as ps]))


;; Factorial recursive program evaluator
;; with natural numbers and CLP(FD).


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

(defn not-num-or-symo* [x]
  (reify
    ps/IConstraintStep
    (-step [this s]
      (reify
        clojure.lang.IFn
        (invoke [_ s]
          (let [x (ps/walk s x)]
            (when (not (and (number? x) (symbol? x)))
              ((remcg this) s))))
        ps/IRunnable
        (-runnable? [_]
          (not (lvar? (ps/walk s x))))))
    ps/IVerifyConstraint
    (-verify [_ a cs]
      (not (some (fn [c] (or (= (ps/-rator c) `symbolo)
                            (= (ps/-rator c) `numbero)))
                 (map (:cm cs) (get (:km cs) (ps/root-var a x))))))
    ps/IConstraintOp
    (-rator [_] `not-num-or-sym)
    (-rands [_] [x])
    ps/IReifiableConstraint
    (-reifyc [c v r s]
      (when-not (lvar? (ps/walk r x))
        `(not-num-or-symo ~(-reify s x r))))
    ps/IConstraintWatchedStores
    (-watched-stores [this] #{:clojure.core.logic/subst})))

(defn not-num-or-symo [x]
  (cgoal (not-num-or-symo* x)))


(declare eval-expo)

(defn lookupo [x env t]
  (fresh [rest y v]
   (conso `(~y ~v) rest env)
   (conde
    [(== y x)
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
  (fresh [h t]
   (not-num-or-symo form)
   (conde
    [(conso h t form)
     (== h x)]
    [(!= h x)
     (conso h t form)
     (conde
      [(mentionso x t)]
      [(mentionso x h)])])))

(defn eval-expo [exp env selves val]
  (conde
   [(symbolo exp)
    (numbero val) ;; TODO Wrong, but fails in lookupo without it
    (lookupo exp env val)]
   [(numbero exp)
    (numbero val)
    (== exp val)]
   [(fresh [rator rand x body env- a env+ selves+]
           (not-num-or-symo exp)
           (== `(~rator ~rand) exp)
           (eval-expo rator env selves `(~'closure ~x ~body ~env-))
           (eval-expo rand env selves a)
           (conso `(~x ~a) env- env+)
           (conso `(~'closure ~x ~body ~a ~env-) selves selves+)
           (eval-expo body env+ selves+ val))]
   [(fresh [x body]
           (not-num-or-symo exp)
           (== `(~'fn [~x] ~body) exp)
           (symbolo x)
           (not-in-envo 'fn env)
           (== `(~'closure ~x ~body ~env) val))]
   [(fresh [selfarg argv prevargv x body env- env+ t selves-]
           (not-num-or-symo exp)
           (== `(~'recur ~selfarg) exp)
           (not-in-envo 'recur env)
           ;; TODO since I put arg to selves list
           ;; need update it when recurring
           (numbero prevargv)
           (conso `(~'closure ~x ~body ~prevargv ~env-) t selves)
           (symbolo x)
           (numbero argv)
           (eval-expo selfarg env selves argv)
           (not-num-or-symo selfarg)
           (mentionso x selfarg)
           (fd/in argv prevargv (fd/interval 25)) ;; TODO
           (fd/< argv prevargv)
           (conso `(~x ~argv) env- env+)
           (conso `(~'closure ~x ~body ~argv ~env-) t selves-)
           (eval-expo body env+ selves- val))]
   [(fresh [e1 e2 e3 t]
           (not-num-or-symo exp)
           (== `(~'if ~e1 ~e2 ~e3) exp)
           (not-in-envo 'if env)
           (conde [(== t true)] [(== t false)])
           (eval-expo e1 env selves t)
           (conde
            [(== true  t)
             (eval-expo e2 env selves val)]
            [(== false t)
             (eval-expo e3 env selves val)]))]
   [(fresh [a n]
           (not-num-or-symo exp)
           (== `(~'dec ~a) exp)
           (not-in-envo 'dec env)
           (numbero val)
           (numbero n)
           (eval-expo a env selves n)
           (fd/in n val (fd/interval 25)) ;; TODO
           (fd/+ 1 val n))]
   [(fresh [a l]
           (not-num-or-symo exp)
           (== `(~'<=1 ~a) exp)
           (not-in-envo '<=1 env)
           (numbero l)
           (eval-expo a env selves l)
           (conde
            [(== l 0) (== val true)]
            [(== l 1) (== val true)]
            [(!= l 0) (!= l 1) (fd/> l 1) (== val false)]))]
   [(fresh [a1 a2 va1 va2]
           (not-num-or-symo exp)
           (== `(~'* ~a1 ~a2) exp)
           (not-in-envo '* env)
           (numbero va1)
           (numbero va2)
           (numbero val)
           (eval-expo a1 env selves va1)
           (eval-expo a2 env selves va2)
           (fd/in va1 va2 val (fd/interval 25)) ;; TODO
           (fd/* va1 va2 val))]))

(defn evalo [e v]
  (eval-expo e '() '() v))

;; Factorial

(let [factfn '(fn [x]
                (if (<=1 x)
                  1
                  (* x (recur (dec x)))))]

  ;; ~30ms to evaluate (fact 4)
  (defn eval-fact []
    (run 1 [q]
     (evalo `(~factfn 4) q))))

(defn gen-fact []
  (run 1 [q]
   (evalo `(~q 0) 1)
   (evalo `(~q 1) 1)
   (evalo `(~q 2) 2)
   (evalo `(~q 3) 6)
   (evalo `(~q 4) 24)))
