(ns recur.numbers
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic]))

(defn zeroo [n]
  (== '() n))

(defn build-num [n]
  (cond
   (odd? n) (cons 1 (build-num (quot (- n 1) 2)))
   (and (not (zero? n)) (even? n)) (cons 0 (build-num (quot n 2)))
   (zero? n) '()))

(defn poso [n]
  (fresh [a d]
   (conso a d n)))

(defn >1o [n]
  "Bigger that one."
  (fresh [a t ad dd]
   (conso ad t dd)
   (conso a dd n)))

(defn- full-addero [b x y r c]
  (conde
   [(== 0 b) (== 0 x) (== 0 y) (== 0 r) (== 0 c)]
   [(== 1 b) (== 0 x) (== 0 y) (== 1 r) (== 0 c)]
   [(== 0 b) (== 1 x) (== 0 y) (== 1 r) (== 0 c)]
   [(== 1 b) (== 1 x) (== 0 y) (== 0 r) (== 1 c)]
   [(== 0 b) (== 0 x) (== 1 y) (== 1 r) (== 0 c)]
   [(== 1 b) (== 0 x) (== 1 y) (== 0 r) (== 1 c)]
   [(== 0 b) (== 1 x) (== 1 y) (== 0 r) (== 1 c)]
   [(== 1 b) (== 1 x) (== 1 y) (== 1 r) (== 1 c)]))

(declare gen-addero)

(defn- addero [d n m r]
  (conde
   [(== 0 d) (== '() m) (== n r)]
   [(== 0 d) (== '() n) (== m r) (poso m)]
   [(== 1 d) (== '() m) (addero 0 n '(1) r)]
   [(== 1 d) (== '() n) (poso m) (addero 0 '(1) m r)]
   [(== '(1) n) (== '(1) m)
    (fresh [a c]
     (matche [r]
      ([[a c]] succeed))
     (full-addero d 1 1 a c))]
   [(== '(1) n) (gen-addero d n m r)]
   [(== '(1) m) (>1o n) (>1o r) (addero d '(1) n r)]
   [(>1o n) (gen-addero d n m r)]))

(defn- gen-addero [d n m r]
  (fresh [a b c e x y z]
   (conso a x n)
   (conso b y m) (poso y)
   (conso c z r) (poso z)
   (full-addero d a b c e)
   (addero e x y z)))

(defn pluso [n m k]
  (addero 0 n m k))

(def +o pluso)

(defn minuso [n m k]
  (pluso m k n))

(def -o minuso)

(declare odd-*o)

(defn *o [n m p]
  (conde
   [(== '() n) (== '() p)]
   [(poso n) (== '() m) (== '() p)]
   [(== '(1) n) (poso m) (== m p)]
   [(>1o n) (== '(1) m) (== n p)]
   [(matche [n]
     ([[0 . ?x]]
        (poso ?x)
        (matche [p]
         ([[0 . ?z]]
            (poso ?z)
            (>1o m)
            (*o ?x m ?z)))))]
   [(matche [n] ([[1 . ?x]] (poso ?x)))
    (matche [m] ([[0 . ?y]] (poso ?y)))
    (*o m n p)]
   [(matche [n]
     ([[1 . ?x]]
        (poso ?x)
        (matche [m]
         ([[1 . ?y]]
            (poso ?y)
            (odd-*o ?x n m p)))))]))

(declare bound-*o)

(defn- odd-*o [x n m p]
  (fresh [q r]
   (bound-*o q p n m)
   (*o x m q)
   (conso 0 q r)
   (pluso r m p)))

(defn- bound-*o [q p n m]
  (conde
   [(== '() q) (poso p)]
   [(fresh [a0 a1 a2 a3 x y z]
     (matche [q] ([[a0 . x]] succeed))
     (matche [p] ([[a1 . y]] succeed))
     (conde
      [(== '() n)
       (matche [m] ([[a2 . z]] succeed))
       (bound-*o x y z '())]
      [(matche [n] ([[a3 . z]] succeed))
       (bound-*o x y z m)]))]))

(defn- =lo [n m]
  (conde
   [(== '() n) (== '() m)]
   [(== '(1) n) (== '(1) m)]
   [(fresh (a b x y)
     (conso a x n) (poso x)
     (conso b y m) (poso y)
     (=lo x y))]))

(defn- <lo [n m]
  (conde
   [(== '() n) (poso m)]
   [(== '(1) n) (>1o m)]
   [(fresh (x y t1 t2)
     (conso t1 x n) (poso x)
     (conso t2 y m) (poso y)
     (<lo x y))]))

(defn- <=lo [n m]
  (conde
   [(=lo n m)]
   [(<lo n m)]))

(defn <o [n m]
  (conde
   [(<lo n m)]
   [(=lo n m)
    (fresh (x)
     (poso x)
     (pluso n x m))]))

(defn <=o [n m]
  (conde
   [(== n m)]
   [(<o n m)]))

(defn- splito [n r l h]
  (conde
   [(== '() n) (== '() h) (== '() l)]
   [(fresh [b n-hat t1]
     (conso b n-hat t1)
     (conso 0 t1 n)
     (== '() r)
     (conso b n-hat h)
     (== '() l))]
   [(fresh [n-hat]
     (conso 1 n-hat n)
     (== '() r)
     (== n-hat h)
     (== '(1) l))]
   [(fresh [b n-hat a r-hat t1 t2]
     (conso b n-hat t1)
     (conso 0 t1 n)
     (conso a r-hat r)
     (== '() l)
     (conso b n-hat t2)
     (splito t2 r-hat '() h))]
   [(fresh [n-hat a r-hat]
     (conso 1 n-hat n)
     (conso a r-hat r)
     (== '(1) l)
     (splito n-hat r-hat '() h))]
   [(fresh [b n-hat a r-hat l-hat]
     (conso b n-hat n)
     (conso a r-hat r)
     (conso b l-hat l)
     (poso l-hat)
     (splito n-hat r-hat l-hat h))]))

(defn divideo [n m q r]
  (conde
   [(== r n) (== '() q) (<o n m)]
   [(== '(1) q) (=lo n m) (pluso r m n)
    (<o r m)]
   [(<lo m n)
    (<o r m)
    (poso q)
    (fresh [nh nl qh ql qlm qlmr rr rh]
     (splito n r nl nh)
     (splito q r ql qh)
     (conde
      [(== '() nh)
       (== '() qh)
       (minuso nl r qlm)
       (*o ql m qlm)]
      [(poso nh)
       (*o ql m qlm)
       (pluso qlm r qlmr)
       (minuso qlmr nl rr)
       (splito rr r '() rh)
       (divideo nh m qh rh)]))]))

(defn- repeated-mul [n q nq]
  (conde
   [(poso n) (== '() q) (== '(1) nq)]
   [(== '(1) q) (== n nq)]
   [(>1o q)
    (fresh [q1 nq1]
     (pluso q1 '(1) q)
     (repeated-mul n q1 nq1)
     (*o nq1 n nq))]))

(defn exp2 [n b q]
  (conde
    [(== '(1) n) (== '() q)]
    [(>1o n) (== '(1) q)
     (fresh [s]
       (splito n b s '(1)))]
    [(fresh [q1 b2 t1]
      (conso 0 q1 q)
      (poso q1)
      (<lo b n)
      (conso 1 b t1)
      (appendo b t1 b2)
      (exp2 n b2 q1))]
    [(fresh [q1 nh b2 s t1]
      (conso 1 q1 q)
      (poso q1)
      (poso nh)
      (splito n b s nh)
      (conso 1 b t1)
      (appendo b t1 b2)
      (exp2 nh b2 q1))]))

(defn logo [n b q r]
  (conde
    [(== '(1) n) (poso b) (== '() q) (== '() r)]
    [(== '() q) (<o n b) (pluso r '(1) n)]
    [(== '(1) q) (>1o b) (=lo n b) (pluso r b n)]
    [(== '(1) b) (poso q) (pluso r '(1) n)]
    [(== '() b) (poso q) (== r n)]
    [(== '(0 1) b)
     (fresh [a ad dd t1]
       (poso dd)
       (conso ad dd t1)
       (conso a t1 n)
       (exp2 n '() q)
       (fresh [s]
         (splito n dd r s)))]
    [(fresh [a ad add ddd t1 t2]
       (conde
         [(== '(1 1) b)]
         [(conso add ddd t1)
          (conso ad t1 t2)
          (conso a t2 b)]))
     (<lo b n)
     (fresh [bw1 bw nw nw1 ql1 ql s]
       (exp2 b '() bw1)
       (pluso bw1 '(1) bw)
       (<lo q n)
       (fresh [q1 bwq1]
         (pluso q '(1) q1)
         (*o bw q1 bwq1)
         (<o nw1 bwq1))
       (exp2 n '() nw1)
       (pluso nw1 '(1) nw)
       (divideo nw bw ql1 s)
       (pluso ql '(1) ql1)
       (<=lo ql q)
       (fresh [bql qh s qdh qd]
         (repeated-mul b ql bql)
         (divideo nw bw1 qh s)
         (pluso ql qdh qh)
         (pluso ql qd q)
         (<=o qd qdh)
         (fresh [bqd bq1 bq]
           (repeated-mul b qd bqd)
           (*o bql bqd bq)
           (*o b bq bq1)
           (pluso bq r n)
           (<o n bq1))))]))

(defn expo [b q n]
  (logo n b q '()))
