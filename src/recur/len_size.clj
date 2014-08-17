(ns recur.len-with-size
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic]
        [recur.peano]))


;; Try to synthesize length program of minimal size.
;; (So not to let mK to place several nested ifs.)

;; In progress.


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

(defn proper-listo [exp env val size-start size-left]
  (conde
   [(== '() exp)
    (== '() val)]
   [(fresh [a d t-a t-d]
     (conso a d exp)
     (conso t-a t-d val)
     (eval-expo a env t-a)
     (proper-listo d env t-d))]))

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
     (conso h t l)
     (== false v))]))

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

(defn eval-expo [exp env val size-start size-left]
  (conde
   [(fresh [a* size-st-1]
     (conso 'list a* exp)
     (not-in-envo 'list env)
     (noo 'closure a*)
     (inco size-st-1 size-start)
     (proper-listo a* env val size-s))]
   [(symbolo exp)
    (inco size-left size-start)
    (lookupo exp env val)]
   [(fresh [rator rand x body env- a env2 selves2
            sz-st-1 sz-left-1 sz-left-2]
     (== `(~rator ~rand) exp)
     (eval-expo rator env `(~'closure ~x ~body ~env-) sz-st-1 sz-left-1)
     (eval-expo rand env a sz-left-1 sz-left2)
     (conso `(~x ~a) env- env2)
     (conso `(~'closure ~x ~body ~env-) selves2)
     (eval-expo body env2 selves2 val size-left-2 size-left))]
   [(fresh [x body]
     (== `(~'fn [~x] ~body) exp)
     (symbolo x)
     (not-in-envo 'fn env)
     (inco size-left size-start)
     (== `(~'closure ~x ~body ~env) val))]
   [(fresh [selfarg argv prevargv x body env- env2 t sz-left-1]
     (== `(~'self ~selfarg) exp)
     (not-in-envo 'self env)
     (lookupo x env prevargv)
     #_(mentionso x selfarg)
     (eval-expo selfarg env argv size-sta)
     (lessero argv prevargv)
     (conso `(~x ~argv) env env2)
     (eval-expo body env2 val))] ; TODO save sizes to selves
   [(fresh [e1 e2 e3 t]
     (== `(~'if ~e1 ~e2 ~e3) exp)
     (not-in-envo 'if env)
     (eval-expo e1 env t)
     (conde
      [(== true  t) (eval-expo e2 env val)]
      [(== false t) (eval-expo e3 env val)]))]
   [(== `(~'zero) exp)
    (not-in-envo 'zero env)
    (inco size-left size-start)
    (zeroo val)]
   [(fresh [a n]
     (== `(~'inc ~a) exp)
     (not-in-envo 'inc env)
     (inco n val)
     (inco size-left size-start)
     (eval-expo a env n))]
   [(fresh [a l]
     (== `(~'empty? ~a) exp)
     (not-in-envo 'empty? env)
     (inco size-left size-start)
     (empty?o l val)
     (eval-expo a env l))]
   [(fresh [a l sz1 sz2]
     (== `(~'first ~a) exp)
     (not-in-envo 'first env)
     (inco size-left size-start)
     (firsto l val)
     (eval-expo a env l))]
   [(fresh [a l]
     (== `(~'rest ~a) exp)
     (not-in-envo 'rest env)
     (inco size-left size-start)
     (resto l val)
     (eval-expo a env l))]))

(defn evalo [exp val size-start]
  (all
   (noo 'closure exp)
   (eval-expo exp '() val size-start '(z))))

(defn eval-find-smallesto [exp val size]
  (loop [sz '(z)]
    (conda
     [(all (== sz size) (evalo exp val sz))]
     [(recur (cons 's sz))])))

;; Testing

(let [lnfn '(fn [x]
              (if (empty? x)
                (zero)
                (inc (self (rest x)))))]

  (defn eval-length []
    (run* [q]
     (eval-expo `(~lnfn ~'(list (zero) (zero) (zero))) '() '() q))))

(defn gen-length []
  (run 1 [q]
   (eval-expo `(~q ~'(list))               '() '() (build-num 0))
   (eval-expo `(~q ~'(list (zero)))        '() '() (build-num 1))
   (eval-expo `(~q ~'(list (zero) (zero))) '() '() (build-num 2))))
