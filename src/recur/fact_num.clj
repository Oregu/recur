(ns recur.fact-num
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic]
        [recur.numbers]))


;; Factorial recursive program evaluator.
;; Implemented with Oleg's numbers.
;; Runs forward in 20ms.
;;
;; Too long to run backwards. Need to speed up evaluator.


(defn symbolo [x] (predc x symbol?))
(defn listo   [x] (predc x list?))

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
  (fresh [h t]
         (conde
          [(conso h t form)
           (symbolo h)
           (== h x)]
          [(!= h x)
           (symbolo h)
           (conso h t form)
           (conde [(mentionso x t)]
                  [(mentionso x h)])])))

(defn eval-expo [exp env selves val]
  (conde
   [(symbolo exp) (lookupo exp env val)]
   [(numo exp) (== exp val)]
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
   [(fresh [a n]
           (== `(~'dec ~a) exp)
           (not-in-envo 'dec env)
           (eval-expo a env selves n)
           (+o '(1) val n))]
   [(fresh [a l]
           (== `(~'<=1 ~a) exp)
           (not-in-envo '<=1 env)
           (eval-expo a env selves l)
           (conde
            [(== l '()) (== val true)]
            [(== l '(1)) (== val true)]
            [(>1o l) (== val false)]))]
   [(fresh [a1 a2 va1 va2]
           (== `(~'* ~a1 ~a2) exp)
           (not-in-envo '* env)
           (eval-expo a1 env selves va1)
           (eval-expo a2 env selves va2)
           (*o va1 va2 val))]))

;; Fibonacci

(let [factfn '(fn [x]
                (if (<=1 x)
                  x
                  (* x (recur (dec x)))))]

  ;; ~20ms to evaluate (fact 4)
  (defn eval-fact []
    (run 1 [q]
         (eval-expo `(~factfn ~(build-num 4)) '() '() q))))

(defn gen-fact []
  (run 1 [q]
   (eval-expo `(~q ~(build-num 1)) '() '() (build-num 1))
   (eval-expo `(~q ~(build-num 2)) '() '() (build-num 2))
   (eval-expo `(~q ~(build-num 3)) '() '() (build-num 6))
   (eval-expo `(~q ~(build-num 4)) '() '() (build-num 24))))
