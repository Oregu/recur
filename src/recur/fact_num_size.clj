(ns recur.fact-num-size
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic]
        [recur.numbers])
  (:require [recur.peano :as peano]))


;; Factorial recursive program evaluator.
;; Implemented with Oleg's numbers.
;; Uses size metric to search for smallest possible program.


(defn symbolo [x] (predc x symbol?))

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

#_(defn sizeo [form size-start size-left]
  (fresh [h t size-start']
         (trace-lvars "sizeo" [form size-left size-start])
         (conde
          [(conso h t form)
           (trace-lvars "sz" [form h t size-left size-start])
           (symbolo h)
           (peano/inco size-start' size-start)
           (sizeo t size-start' size-left)]
          [(== '() form)
           (== size-start size-left)])))

(defn eval-expo [exp env selves val size-start size-left]
  (all
   #_(trace-lvars "eval" [exp env val size-start size-left])
   (conde
     [(symbolo exp)
      (peano/inco size-left size-start)
      (lookupo exp env val)]
     [(fresh [rator rand x body env- a env+ selves+
              size-start' size-left' size-left'']
             (== `(~rator ~rand) exp)
             (peano/inco size-start' size-start)
             (eval-expo rator env selves `(~'closure ~x ~body ~env-)
                        size-start' size-left')
             (eval-expo rand env selves a
                        size-left' size-left'')
             (conso `(~x ~a) env- env+)
             (conso `(~'closure ~x ~body ~env-) selves selves+)
             (eval-expo body env+ selves+ val
                        size-left'' size-left))]
     [(fresh [x body]
             (== `(~'fn [~x] ~body) exp)
             (== `(~'closure ~x ~body ~env) val)
             (peano/inco size-left size-start)
             (symbolo x)
             (not-in-envo 'fn env))]
     [(fresh [selfarg argv prevargv x body env- env+ t
              size-start' s1 s2]
             (== `(~'recur ~selfarg) exp)
             (peano/inco size-start' size-start)
             (conso `(~'closure ~x ~body ~env-) t selves)
             (conso `(~x ~argv) env- env+)
             (not-in-envo 'recur env)
             (lookupo x env prevargv)
             (mentionso x selfarg)
             (eval-expo selfarg env selves argv size-start' size-left)
             (<o argv prevargv)
             (eval-expo body env+ selves val s1 s2))]
     [(fresh [e1 e2 e3 t val-other size-start' size-left' size-left'']
             (== `(~'if ~e1 ~e2 ~e3) exp)
             (peano/inco size-start' size-start)
             (not-in-envo 'if env)
             (eval-expo e1 env selves t size-start' size-left')
             (trace-lvars "if" [e1 t exp val size-start size-left])
             (conde
              [(== true t)
               ;; For the sake of sizing
               (eval-expo e3 env selves val-other size-left' size-left'')
               (eval-expo e2 env selves val size-left'' size-left)]
              [(== false t)
               ;; For the sake of sizing
               (eval-expo e2 env selves val-other size-left' size-left'')
               (eval-expo e3 env selves val size-left'' size-left)]))]
     [(fresh [a n size-start']
             (== `(~'dec ~a) exp)
             (peano/inco size-start' size-start)
             (not-in-envo 'dec env)
             (eval-expo a env selves n size-start' size-left)
             (+o '(1) val n))]
     [(fresh [a l size-start' size-left']
             (== `(~'<=1 ~a) exp)
             (peano/inco size-start' size-start)
             (not-in-envo '<=1 env)
             (conde
              [(== l '()) (== val true)]
              [(== l '(1)) (== val true)]
              [(>1o l) (== val false)])
             (eval-expo a env selves l size-start' size-left))]
     [(fresh [a1 a2 va1 va2 v size-start' size-left']
             (== `(~'* ~a1 ~a2) exp)
             (== v val)
             (peano/inco size-start' size-start)
             (not-in-envo '* env)
             (eval-expo a1 env selves va1 size-start' size-left')
             (eval-expo a2 env selves va2 size-left' size-left)
             (*o va1 va2 v))])))

(defn evalo [exp val size-start]
  (all #_(noo 'closure exp)
       (eval-expo exp '() '() val size-start (peano/zero))))

(defn eval-find-smallesto
  ([exp val sz size]
     (eval-find-smallesto exp '() '() val sz (peano/zero)))
  ([exp env selves val sz size]
     (conde
      [(all
        (== size sz)
        (eval-expo exp env selves val sz (peano/zero))
        #_(trace-lvars "sz" [sz size]))]
      [#_(trace-lvars "recur" [sz size])
       (eval-find-smallesto exp env selves val (peano/inc sz) size)])))

;; Factorial

(let [factbody '(if (<=1 x)
                  x
                  (* x (recur (dec x))))
      factfn `(~'fn [~'x] ~factbody)]

  ;; ~75ms to evaluate (fact 4)
  (defn eval-fact []
    (run 1 [q sz]
         (eval-expo factbody
                    `((~'x ~(build-num 4)))
                    `((~'closure ~'x ~factbody ()))
                    q
                    sz
                    (peano/zero)))))

;; Generates fact body in 13s
(defn gen-fact-fast []
  (run 1 [q size]
       (eval-find-smallesto q
                            `((~'x ~(build-num 1)))
                            `((~'closure ~'x ~q ()))
                            (build-num 1)
                            (peano/zero)
                            size)
       (eval-find-smallesto q
                            `((~'x ~(build-num 2)))
                            `((~'closure ~'x ~q ()))
                            (build-num 2)
                            (peano/zero)
                            size)
       (eval-find-smallesto q
                            `((~'x ~(build-num 3)))
                            `((~'closure ~'x ~q ()))
                            (build-num 6)
                            (peano/zero)
                            size)
       (eval-find-smallesto q
                            `((~'x ~(build-num 4)))
                            `((~'closure ~'x ~q ()))
                            (build-num 24)
                            (peano/zero)
                            size)))

;; 115ms (dec (dec x))
(defn gen-dec-dec []
  (run 1 [q size]
       (eval-find-smallesto q
                            `((~'x ~(build-num 2)))
                            '()
                            (build-num 0)
                            (peano/zero)
                            size)))

;; 7ms size 6
(defn eval-if-size []
  (run 1 [q sz]
       (eval-expo '(if (<=1 x) x (dec x))
                  `((~'x ~(build-num 4)))
                  `()
                  q
                  sz
                  (peano/zero))))

;; (if (<=1 x) x (dec x))
(defn gen-if-cond []
  (run 1 [q size]
       (== size (peano/build-num 6))
       (eval-find-smallesto q
                            `((~'x ~(build-num 0)))
                            '()
                            (build-num 0)
                            (peano/zero)
                            (build-num 6))
       (eval-find-smallesto q
                            `((~'x ~(build-num 1)))
                            '()
                            (build-num 1)
                            (peano/zero)
                            (build-num 6))
       (eval-find-smallesto q
                            `((~'x ~(build-num 2)))
                            '()
                            (build-num 1)
                            (peano/zero)
                            (build-num 6))))
