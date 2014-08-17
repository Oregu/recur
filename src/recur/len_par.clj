(ns recur.len-par
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic]
        [recur.peano]))


;; Trying to generate length program with "parallel" evaluator.
;; By parallel I mean, it evaluates three programs at once.
;; Forward evaluation works. Backward do not.

;; In progress.
;; How about separating input from evaluated program?
;; For example (eval fn input output)


(defn symbolo [u] (predc u symbol?))

(defn noo [tag u]
  (predc u (fn [x] (clojure.core/not= (if (coll? x) (first x) x) tag))))

(defn primitivo [u]
  (predc u (fn [x] (:primitive (meta x)))))

(declare eval-expo-with-examples)

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

(defn proper-listo [exp1 env1 selves1 val1
                    exp2 env2 selves2 val2
                    exp3 env3 selves3 val3]
  (conde
   [(== '() exp1) (== '() val1)
    (== '() exp2) (== '() val2)
    (== '() exp3) (== '() val3)]
   [(fresh [a1 d1 t-a1 t-d1
            a2 d2 t-a2 t-d2
            a3 d3 t-a3 t-d3]
           (conso a1 d1 exp1)
           (conso a2 d2 exp2)
           (conso a3 d3 exp3)
           (conso t-a1 t-d1 val1)
           (conso t-a2 t-d2 val2)
           (conso t-a3 t-d3 val3)
           (eval-expo-with-examples a1 env1 selves1 t-a1
                                    a2 env2 selves2 t-a2
                                    a3 env3 selves3 t-a3)
           (proper-listo d1 env1 selves1 t-d1
                         d2 env2 selves2 t-d2
                         d3 env3 selves3 t-d3))]))

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

(defn prim [l]
  (with-meta l {:primitive true}))

(defn eval-expo-with-examples [exp1 env1 selves1 val1
                               exp2 env2 selves2 val2
                               exp3 env3 selves3 val3]
  (all
   #_(trace-lvars "eval" [exp1 exp2 exp3])
   (conde
    #_[(fresh [a*1 a*2 a*3]
              (conso 'list a*1 exp1)
              (conso 'list a*2 exp2)
              (conso 'list a*3 exp3)
              (not-in-envo 'list env1)
              (not-in-envo 'list env2)
              (not-in-envo 'list env3)
              (noo 'closure a*1)
              (noo 'closure a*2)
              (noo 'closure a*3)
              (proper-listo a*1 env1 selves1 val1
                            a*2 env2 selves2 val2
                            a*3 env3 selves2 val3))]
    [#_(trace-lvars "1")
     (symbolo exp1) (symbolo exp2) (symbolo exp3)
     (lookupo exp1 env1 val1)
     (lookupo exp2 env2 val2)
     (lookupo exp3 env3 val3)]
    [#_(trace-lvars "2")
     (== '(zero) exp1) (not-in-envo 'zero env1) (zeroo val1)
     (symbolo exp2) (symbolo exp3)
     (lookupo exp2 env2 val2) (lookupo exp3 env3 val3)]
    [#_(trace-lvars "3")
     (== '(zero) exp1) (not-in-envo 'zero env1) (zeroo val1)
     (== '(zero) exp2) (not-in-envo 'zero env2) (zeroo val2)
     (symbolo exp3) (lookupo exp3 env3 val3)]
    [#_(trace-lvars "4")
     (primitivo exp1) (primitivo exp2) (primitivo exp3)
     (== exp1 val1) (== exp2 val2) (== exp3 val3)]
    [#_(trace-lvars "5")
     (fresh [rator1 rand1 x1 body1 env-1 a1 env+1 selves+1
             rator2 rand2 x2 body2 env-2 a2 env+2 selves+2
             rator3 rand3 x3 body3 env-3 a3 env+3 selves+3]
            (== `(~rator1 ~rand1) exp1)
            (== `(~rator2 ~rand2) exp2)
            (== `(~rator3 ~rand3) exp3)
            (eval-expo-with-examples rator1 env1 selves1 `(~'closure ~x1 ~body1 ~env-1)
                                     rator2 env2 selves2 `(~'closure ~x2 ~body2 ~env-2)
                                     rator3 env3 selves3 `(~'closure ~x3 ~body3 ~env-3))
            (eval-expo-with-examples rand1 env1 selves1 a1
                                     rand2 env2 selves2 a2
                                     rand3 env3 selves3 a3)
            (conso `(~x1 ~a1) env-1 env+1)
            (conso `(~x2 ~a2) env-2 env+2)
            (conso `(~x3 ~a3) env-3 env+3)
            (conso `(~'closure ~x1 ~body1 ~env-1) selves1 selves+1)
            (conso `(~'closure ~x2 ~body2 ~env-2) selves2 selves+2)
            (conso `(~'closure ~x3 ~body3 ~env-3) selves3 selves+3)
            (eval-expo-with-examples body1 env+1 selves+1 val1
                                     body2 env+2 selves+2 val2
                                     body3 env+3 selves+3 val3))]
    [#_(trace-lvars "6")
     (fresh [x1 body1
             x2 body2
             x3 body3]
            (== `(~'fn [~x1] ~body1) exp1)
            (== `(~'fn [~x2] ~body2) exp2)
            (== `(~'fn [~x3] ~body3) exp3)
            (symbolo x1)
            (symbolo x2)
            (symbolo x3)
            (not-in-envo 'fn env1)
            (not-in-envo 'fn env2)
            (not-in-envo 'fn env3)
            (== `(~'closure ~x1 ~body1 ~env1) val1)
            (== `(~'closure ~x2 ~body2 ~env2) val2)
            (== `(~'closure ~x3 ~body3 ~env3) val3))]
    [#_(trace-lvars "7")
     (fresh [selfarg1 argv1 prevargv1 x1 body1 env-1 env+1 t1
             selfarg2 argv2 prevargv2 x2 body2 env-2 env+2 t2
             selfarg3 argv3 prevargv3 x3 body3 env-3 env+3 t3]
            (== `(~'recur ~selfarg1) exp1)
            (== `(~'recur ~selfarg2) exp2)
            (== `(~'recur ~selfarg3) exp3)
            (not-in-envo 'recur env1)
            (not-in-envo 'recur env2)
            (not-in-envo 'recur env3)
            (conso `(~'closure ~x1 ~body1 ~env-1) t1 selves1)
            (conso `(~'closure ~x2 ~body2 ~env-2) t2 selves2)
            (conso `(~'closure ~x3 ~body3 ~env-3) t3 selves3)
            (lookupo x1 env1 prevargv1)
            (lookupo x2 env2 prevargv2)
            (lookupo x3 env3 prevargv3)
            (mentionso x1 selfarg1)
            (mentionso x2 selfarg2)
            (mentionso x3 selfarg3)
            (eval-expo-with-examples selfarg1 env1 selves1 argv1
                                     selfarg2 env2 selves2 argv2
                                     selfarg3 env3 selves3 argv3)
            (lessero argv1 prevargv1)
            (lessero argv2 prevargv2)
            (lessero argv3 prevargv3)
            (conso `(~x1 ~argv1) env-1 env+1)
            (conso `(~x2 ~argv2) env-2 env+2)
            (conso `(~x3 ~argv3) env-3 env+3)
            (eval-expo-with-examples body1 env+1 selves1 val1
                                     body2 env+2 selves2 val2
                                     body3 env+3 selves3 val3))]
    [#_(trace-lvars "8")
     (fresh [selfarg2 argv2 prevargv2 x2 body2 env-2 env+2 t2
             selfarg3 argv3 prevargv3 x3 body3 env-3 env+3 t3]
            (== '(zero) exp1) (not-in-envo 'zero env1) (zeroo val1)
            (== `(~'recur ~selfarg2) exp2)
            (== `(~'recur ~selfarg3) exp3)
            (not-in-envo 'recur env2)
            (not-in-envo 'recur env3)
            (conso `(~'closure ~x2 ~body2 ~env-2) t2 selves2)
            (conso `(~'closure ~x3 ~body3 ~env-3) t3 selves3)
            (lookupo x2 env2 prevargv2)
            (lookupo x3 env3 prevargv3)
            (mentionso x2 selfarg2)
            (mentionso x3 selfarg3)
            (eval-expo-with-examples exp1 env1 selves1 val1
                                     selfarg2 env2 selves2 argv2
                                     selfarg3 env3 selves3 argv3)
            (lessero argv2 prevargv2)
            (lessero argv3 prevargv3)
            (conso `(~x2 ~argv2) env-2 env+2)
            (conso `(~x3 ~argv3) env-3 env+3)
            (eval-expo-with-examples exp1 env1 selves1 val1
                                     body2 env+2 selves2 val2
                                     body3 env+3 selves3 val3))]
    [#_(trace-lvars "9")
     (fresh [selfarg3 argv3 prevargv3 x3 body3 env-3 env+3 t3]
            (== '(zero) exp1) (not-in-envo 'zero env1) (zeroo val1)
            (== '(zero) exp2) (not-in-envo 'zero env2) (zeroo val2)
            (== `(~'recur ~selfarg3) exp3)
            (not-in-envo 'recur env3)
            (conso `(~'closure ~x3 ~body3 ~env-3) t3 selves3)
            (lookupo x3 env3 prevargv3)
            (mentionso x3 selfarg3)
            (eval-expo-with-examples exp1 env1 selves1 val1
                                     exp2 env2 selves2 val2
                                     selfarg3 env3 selves3 argv3)
            (lessero argv3 prevargv3)
            (conso `(~x3 ~argv3) env-3 env+3)
            (eval-expo-with-examples exp1 env1 selves1 val1
                                     exp2 env2 selves2 val2
                                     body3 env+3 selves3 val3))]
    [#_(trace-lvars "10")
     (fresh [e-cond1 e-true1 e-false1 t1
             e-cond2 e-true2 e-false2 t2
             e-cond3 e-true3 e-false3 t3]
            (== `(~'if ~e-cond1 ~e-true1 ~e-false1) exp1)
            (== `(~'if ~e-cond2 ~e-true2 ~e-false2) exp2)
            (== `(~'if ~e-cond3 ~e-true3 ~e-false3) exp3)
            (not-in-envo 'if env1)
            (not-in-envo 'if env2)
            (not-in-envo 'if env3)
            (eval-expo-with-examples e-cond1 env1 selves1 t1
                                     e-cond2 env2 selves2 t2
                                     e-cond3 env3 selves3 t3)
            (conde
             [(== true  t1) (== true t2) (== true t3)
              (eval-expo-with-examples e-true1 env1 selves1 val1
                                       e-true2 env2 selves2 val2
                                       e-true3 env3 selves3 val3)]
             [(== false t1) (== false t2) (== false t3)
              (eval-expo-with-examples e-false1 env1 selves1 val1
                                       e-false2 env2 selves2 val2
                                       e-false3 env3 selves3 val3)]
             [(== true  t1) (== false t2) (== false t3)
              (eval-expo-with-examples e-true1 env1 selves1 val1
                                       e-false2 env2 selves2 val2
                                       e-false3 env3 selves3 val3)]))]
    [#_(trace-lvars "11")
     (fresh [e-cond2 e-true2 e-false2 t2
             e-cond3 e-true3 e-false3 t3]
            (== '(zero) exp1) (not-in-envo 'zero env1) (zeroo val1)
            (== `(~'if ~e-cond2 ~e-true2 ~e-false2) exp2)
            (== `(~'if ~e-cond3 ~e-true3 ~e-false3) exp3)
            (not-in-envo 'if env2)
            (not-in-envo 'if env3)
            (eval-expo-with-examples exp1 env1 selves1 val1
                                     e-cond2 env2 selves2 t2
                                     e-cond3 env3 selves3 t3)
            (conde
             [(== true t2) (== true t3)
              (eval-expo-with-examples exp1 env1 selves1 val1
                                       e-true2 env2 selves2 val2
                                       e-true3 env3 selves3 val3)]
             [(== false t2) (== false t3)
              (eval-expo-with-examples exp1 env1 selves1 val1
                                       e-false2 env2 selves2 val2
                                       e-false3 env3 selves3 val3)]
             [(== true t2) (== false t3)
              (eval-expo-with-examples exp1 env1 selves1 val1
                                       e-true2 env2 selves2 val2
                                       e-false3 env3 selves3 val3)]))]
    [#_(trace-lvars "12")
     (fresh [e-cond3 e-true3 e-false3 t3]
            (== '(zero) exp1) (not-in-envo 'zero env1) (zeroo val1)
            (== '(zero) exp2) (not-in-envo 'zero env2) (zeroo val2)
            (== `(~'if ~e-cond3 ~e-true3 ~e-false3) exp3)
            (not-in-envo 'if env3)
            (eval-expo-with-examples exp1 env1 selves1 val1
                                     exp2 env2 selves2 val2
                                     e-cond3 env3 selves3 t3)
            (conde
             [(== true t3)
              (eval-expo-with-examples exp1 env1 selves1 val1
                                       exp2 env2 selves2 val2
                                       e-true3 env3 selves3 val3)]
             [(== false t3)
              (eval-expo-with-examples exp1 env1 selves1 val1
                                       exp2 env2 selves2 val2
                                       e-false3 env3 selves3 val3)]))]
    [#_(trace-lvars "13")
     (== '(zero) exp1) (not-in-envo 'zero env1) (zeroo val1)
     (== '(zero) exp2) (not-in-envo 'zero env2) (zeroo val2)
     (== '(zero) exp3) (not-in-envo 'zero env3) (zeroo val3)]
    [#_(trace-lvars "14")
     (fresh [rator2 rand2 x2 body2 env-2 a2 env+2 selves+2
             rator3 rand3 x3 body3 env-3 a3 env+3 selves+3]
            (== '(zero) exp1) (not-in-envo 'zero env1) (zeroo val1)
            (== `(~rator2 ~rand2) exp2)
            (== `(~rator3 ~rand3) exp3)
            (eval-expo-with-examples val1 env1 selves1 val1
                                     rator2 env2 selves2 `(~'closure ~x2 ~body2 ~env-2)
                                     rator3 env3 selves3 `(~'closure ~x3 ~body3 ~env-3))
            (eval-expo-with-examples val1 env1 selves1 val1
                                     rand2 env2 selves2 a2
                                     rand3 env3 selves3 a3)
            (conso `(~x2 ~a2) env-2 env+2)
            (conso `(~x3 ~a3) env-3 env+3)
            (conso `(~'closure ~x2 ~body2 ~env-2) selves2 selves+2)
            (conso `(~'closure ~x3 ~body3 ~env-3) selves3 selves+3)
            (eval-expo-with-examples val1 env1 selves1 val1
                                     body2 env+2 selves+2 val2
                                     body3 env+3 selves+3 val3))]
    [#_(trace-lvars "15")
     (fresh [rator3 rand3 x3 body3 env-3 a3 env+3 selves+3]
            (primitivo exp1)
            (== '(zero) exp2) (not-in-envo 'zero env2) (zeroo val2)
            (== `(~rator3 ~rand3) exp3)
            (eval-expo-with-examples val1 env1 selves1 val1
                                     val2 env2 selves2 val2
                                     rator3 env3 selves3 `(~'closure ~x3 ~body3 ~env-3))
            (eval-expo-with-examples val1 env1 selves1 val1
                                     val2 env2 selves2 val2
                                     rand3 env3 selves3 a3)
            (conso `(~x3 ~a3) env-3 env+3)
            (conso `(~'closure ~x3 ~body3 ~env-3) selves3 selves+3)
            (eval-expo-with-examples val1 env1 selves1 val1
                                     val2 env2 selves2 val2
                                     body3 env+3 selves+3 val3))]
    [#_(trace-lvars "16")
     (fresh [a1 n1 a2 n2 a3 n3]
            (== `(~'inc ~a1) exp1)
            (== `(~'inc ~a2) exp2)
            (== `(~'inc ~a3) exp3)
            (not-in-envo 'inc env1)
            (not-in-envo 'inc env2)
            (not-in-envo 'inc env3)
            (eval-expo-with-examples a1 env1 selves1 n1
                                     a2 env2 selves2 n2
                                     a3 env3 selves3 n3)
            (inco n1 val1)
            (inco n2 val2)
            (inco n3 val3))]
    [#_(trace-lvars "17")
     (fresh [a2 n2 a3 n3]
            (== '(zero) exp1) (not-in-envo 'zero env1) (zeroo val1)
            (== `(~'inc ~a2) exp2)
            (== `(~'inc ~a3) exp3)
            (not-in-envo 'inc env2)
            (not-in-envo 'inc env3)
            (eval-expo-with-examples exp1 env1 selves1 val1
                                     a2 env2 selves2 n2
                                     a3 env3 selves3 n3)
            (inco n2 val2)
            (inco n3 val3))]
    [#_(trace-lvars "18")
     (fresh [a3 n3]
            (== '(zero) exp1) (not-in-envo 'zero env1) (zeroo val1)
            (== '(zero) exp2) (not-in-envo 'zero env2) (zeroo val2)
            (== `(~'inc ~a3) exp3)
            (not-in-envo 'inc env3)
            (eval-expo-with-examples exp1 env1 selves1 val1
                                     exp2 env2 selves2 val2
                                     a3 env3 selves3 n3)
            (inco n3 val3))]
    [#_(trace-lvars "19")
     (primitivo exp1) (== val1 exp1)
     (primitivo exp2) (== val2 exp2)
     (== '(zero) exp3) (not-in-envo 'zero env3) (zeroo val3)]
    [#_(trace-lvars "20")
     (fresh [a1 l1 a2 l2 a3 l3]
            (== `(~'empty? ~a1) exp1)
            (== `(~'empty? ~a2) exp2)
            (== `(~'empty? ~a3) exp3)
            (not-in-envo 'empty? env1)
            (not-in-envo 'empty? env2)
            (not-in-envo 'empty? env3)
            (eval-expo-with-examples a1 env1 selves1 l1
                                     a2 env2 selves2 l2
                                     a3 env3 selves3 l3)
            (empty?o l1 val1)
            (empty?o l2 val2)
            (empty?o l3 val3))]
    [#_(trace-lvars "21")
     (fresh [a2 l2 a3 l3]
            (== '(zero) exp1) (not-in-envo 'zero env1) (zeroo val1)
            (== `(~'empty? ~a2) exp2)
            (== `(~'empty? ~a3) exp3)
            (not-in-envo 'empty? env2)
            (not-in-envo 'empty? env3)
            (eval-expo-with-examples exp1 env1 selves1 val1
                                     a2 env2 selves2 l2
                                     a3 env3 selves3 l3)
            (empty?o l2 val2)
            (empty?o l3 val3))]
    [#_(trace-lvars "22")
     (fresh [a3 l3]
            (== '(zero) exp1) (not-in-envo 'zero env1) (zeroo val1)
            (== '(zero) exp2) (not-in-envo 'zero env2) (zeroo val2)
            (== `(~'empty? ~a3) exp3)
            (not-in-envo 'empty? env3)
            (eval-expo-with-examples exp1 env1 selves1 val1
                                     exp2 env2 selves2 val2
                                     a3 env3 selves3 l3)
            (empty?o l3 val3))]
    [#_(trace-lvars "23")
     (fresh [a1 l1 a2 l2 a3 l3]
            (== `(~'first ~a1) exp1)
            (== `(~'first ~a2) exp2)
            (== `(~'first ~a3) exp3)
            (not-in-envo 'first env1)
            (not-in-envo 'first env2)
            (not-in-envo 'first env3)
            (eval-expo-with-examples a1 env1 selves1 l1
                                     a2 env2 selves2 l2
                                     a3 env3 selves3 l3)
            (firsto l1 val1)
            (firsto l2 val2)
            (firsto l3 val3))]
    [#_(trace-lvars "24")
     (fresh [a1 l1 a2 l2 a3 l3]
            (== `(~'rest ~a1) exp1)
            (== `(~'rest ~a2) exp2)
            (== `(~'rest ~a3) exp3)
            (not-in-envo 'rest env1)
            (not-in-envo 'rest env2)
            (not-in-envo 'rest env3)
            (resto l1 val1)
            (resto l2 val2)
            (resto l3 val3)
            (eval-expo-with-examples a1 env1 selves1 l1
                                     a2 env2 selves2 l2
                                     a3 env3 selves3 l3))]
    [#_(trace-lvars "25")
     (fresh [a2 l2 a3 l3]
            (== '(zero) exp1) (not-in-envo 'zero env1) (zeroo val1)
            (== `(~'rest ~a2) exp2)
            (== `(~'rest ~a3) exp3)
            (not-in-envo 'rest env2)
            (not-in-envo 'rest env3)
            (eval-expo-with-examples exp1 env1 selves1 val1
                                     a2 env2 selves2 l2
                                     a3 env3 selves3 l3)
            (resto l2 val2)
            (resto l3 val3))]
    [#_(trace-lvars "26")
     (fresh [a3 l3]
            (== '(zero) exp1) (not-in-envo 'zero env1) (zeroo val1)
            (== '(zero) exp2) (not-in-envo 'zero env2) (zeroo val2)
            (== `(~'rest ~a3) exp3)
            (not-in-envo 'rest env3)
            (eval-expo-with-examples exp1 env1 selves1 val1
                                     exp2 env2 selves2 val2
                                     a3 env3 selves3 l3)
            (resto l3 val3))])))

;; Length

(let [lnfn '(fn [x]
              (if (empty? x)
                (zero)
                (inc (recur (rest x)))))]

  (defn eval-length []
    (run* [q1 q2 q3]
          (eval-expo-with-examples
           `(~lnfn ~(prim '(     ))) '() '() q1
           `(~lnfn ~(prim '(   ()))) '() '() q2
           `(~lnfn ~(prim '(() ()))) '() '() q3))))

;; Generates length program in XXs

(defn gen-length []
  (run 1 [q]
       (eval-expo-with-examples
        `(~q ~(prim '(     ))) '() '() '(z)
        `(~q ~(prim '(()   ))) '() '() '(s z)
        `(~q ~(prim '(() ()))) '() '() '(s s z))))

