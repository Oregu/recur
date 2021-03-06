(ns recur.len
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic]
        [recur.peano]))


;; Evaluator able to evaluate length program recursive definition.
;; And what is much more important -- able to synthesize one in 1m.


(defn noo [tag u]
  (predc u (fn [x] (clojure.core/not= (if (coll? x) (first x) x) tag))))
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
     (conso a d exp)
     (conso t-a t-d val)
     (eval-expo a env selves t-a)
     (proper-listo d env selves t-d))]))

;; Diverges if both unbound, e.g. (run 1 [q] (lessero q q))
(defn lessero [l1 l2]
  (conde
   [(fresh [h t]
     (== '() l1)
     (conso h t l2))]
   [(fresh [t1 t2]
     (resto l1 t1)
     (resto l2 t2)
     (lessero t1 t2))]))

(defn empty?o [l v]
  (conde
   [(== '()  l)
    (== true v)]
   [(fresh [h t]
     (!= l '())
     (== false v)
     (conso h t l))]))

(defn mentionso [x form]
  (fresh [h t]
   (conde
    [(== h x)
     (symbolo h)
     (conso h t form)]
    [(!= h x)
     (symbolo h)
     (conso h t form)
     (conde [(mentionso x t)]
            [(mentionso x h)])])))

(defn eval-expo [exp env selves val]
  (conde
   [(fresh [a*]
     (conso 'list a* exp)
     (not-in-envo 'list env)
     (noo 'closure a*)
     (proper-listo a* env selves val))]
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
     (== `(~'closure ~x ~body ~env) val)
     (symbolo x)
     (not-in-envo 'fn env))]
   [(fresh [selfarg argv prevargv x body env- env2 t]
     (== `(~'recur ~selfarg) exp)
     (not-in-envo 'recur env)
     (conso `(~'closure ~x ~body ~env-) t selves)
     (lookupo x env prevargv)
     (mentionso x selfarg)
     (eval-expo selfarg env selves argv)
     (lessero argv prevargv)
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
    (zeroo val)
    (not-in-envo 'zero env)]
   [(fresh [a n]
     (== `(~'inc ~a) exp)
     (not-in-envo 'inc env)
     (inco n val)
     (eval-expo a env selves n))]
   [(fresh [a l]
     (== `(~'empty? ~a) exp)
     (not-in-envo 'empty? env)
     (eval-expo a env selves l)
     (empty?o l val))]
   [(fresh [a l]
     (== `(~'first ~a) exp)
     (not-in-envo 'first env)
     (eval-expo a env selves l)
     (firsto l val))]
   [(fresh [a l]
     (== `(~'rest ~a) exp)
     (not-in-envo 'rest env)
     (eval-expo a env selves l)
     (resto l val))]))

;; Length evaluation and generation

(let [lnfn '(fn [x]
              (if (empty? x)
                (zero)
                (inc (recur (rest x)))))]

  ;; 14ms to eval
  (defn eval-length []
    (run* [q]
          (eval-expo `(~lnfn ~'(list (zero) (zero) (zero))) '() '() q))))

;; Generates length program in ~60s
(defn gen-length []
  (run 1 [q]
    (eval-expo `(~q ~'(list)) '() '() '(z))
    (eval-expo `(~q ~'(list (zero))) '() '() '(s z))
    (eval-expo `(~q ~'(list (zero) (zero))) '() '() '(s s z))))
