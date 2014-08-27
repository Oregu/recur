(ns recur.fib-num
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic]
        [recur.numbers]))


;; Fibonacci recursive program evaluator.
;; Implemented with Oleg's numbers.
;; Runs forward in 180ms (same as fib with peano nums).
;;
;; Too long to run backwards. Need to speed up evaluator.
;; Probably double recursion mess things up.


(defn symbolo [x] (predc x symbol?))
(defn listo   [x] (predc x list?))

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
     (== h x)]
    [(!= h x)
     (conso h t form)
     (conde
      [(mentionso x t)]
      [(mentionso x h)])])))

(defn eval-expo [exp env selves val]
  (conde
   [(symbolo exp) (lookupo exp env val)]
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
           (conso `(~'closure ~x ~body ~env-) t selves)
           (not-in-envo 'recur env)
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
           (conde
            [(== l '()) (== val true)]
            [(== l '(1)) (== val true)]
            [(>1o l) (== val false)])
           (eval-expo a env selves l))]
   [(fresh [a1 a2 va1 va2]
           (== `(~'+ ~a1 ~a2) exp)
           (not-in-envo '+ env)
           (eval-expo a1 env selves va1)
           (eval-expo a2 env selves va2)
           (+o va1 va2 val))]))

;; Fibonacci

(let [fibbody '(if (<=1 x)
                 x
                 (+ (recur (dec x))
                    (recur (dec (dec x)))))
      fibfn `(~'fn [~'x] ~fibbody)]

  ;; ~126ms to evaluate (fib 7)
  (defn eval-fib []
    (run 1 [q]
         (eval-expo fibbody
                    `((~'x ~(build-num 7)))
                    `((~'closure ~'x ~fibbody ()))
                    q)))

  ;; ~757ms to evaluate back
  (defn eval-fib-back []
    (run 1 [q]
         (eval-expo fibbody
                    `((~'x ~q))
                    `((~'closure ~'x ~fibbody ()))
                    (build-num 13)))))

(defn gen-fib []
  (run 1 [q]
   (eval-expo `(~q ~(build-num 0)) '() '() (build-num 0))
   (eval-expo `(~q ~(build-num 1)) '() '() (build-num 1))
   (eval-expo `(~q ~(build-num 2)) '() '() (build-num 1))
   (eval-expo `(~q ~(build-num 3)) '() '() (build-num 2))
   (eval-expo `(~q ~(build-num 4)) '() '() (build-num 3))
   (eval-expo `(~q ~(build-num 5)) '() '() (build-num 5))))

(defn gen-fib-fast []
  (run 1 [q]
       (fresh [s2]
              (== q `(~'if (~'<=1 ~'x)
                       ~'x
                       (~'+ (~'recur (~'dec ~'x))
                            ~s2)))
              (eval-expo q
                         `((~'x ~(build-num 0)))
                         `((~'closure ~'x ~q ()))
                         (build-num 0))
              (eval-expo q
                         `((~'x ~(build-num 1)))
                         `((~'closure ~'x ~q ()))
                         (build-num 1))
              (eval-expo q
                         `((~'x ~(build-num 2)))
                         `((~'closure ~'x ~q ()))
                         (build-num 1))
              (eval-expo q
                         `((~'x ~(build-num 3)))
                         `((~'closure ~'x ~q ()))
                         (build-num 2))
              (eval-expo q
                         `((~'x ~(build-num 4)))
                         `((~'closure ~'x ~q ()))
                         (build-num 3))
              (eval-expo q
                         `((~'x ~(build-num 5)))
                         `((~'closure ~'x ~q ()))
                         (build-num 5)))))
