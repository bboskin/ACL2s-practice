; **************** BEGIN INITIALIZATION FOR ACL2s B MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#|
Pete Manolios
Fri Jan 27 09:39:00 EST 2012
----------------------------

Made changes for spring 2012.


Pete Manolios
Thu Jan 27 18:53:33 EST 2011
----------------------------

The Beginner level is the next level after Bare Bones level.

|#

; Put CCG book first in order, since it seems this results in faster loading of this mode.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%") (value :invisible))
(include-book "custom" :dir :acl2s-modes :uncertified-okp nil :ttags :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading trace-star and evalable-ld-printing books.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "trace-star" :uncertified-okp nil :dir :acl2s-modes :ttags ((:acl2s-interaction)) :load-compiled-file nil)
(include-book "hacking/evalable-ld-printing" :uncertified-okp nil :dir :system :ttags ((:evalable-ld-printing)) :load-compiled-file nil)

;theory for beginner mode
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s beginner theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "beginner-theory" :dir :acl2s-modes :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s Beginner mode.") (value :invisible))
;Settings specific to ACL2s Beginner mode.
(acl2s-beginner-settings)

; why why why why 
(acl2::xdoc acl2s::defunc) ; almost 3 seconds

(cw "~@0Beginner mode loaded.~%~@1"
    #+acl2s-startup "${NoMoReSnIp}$~%" #-acl2s-startup ""
    #+acl2s-startup "${SnIpMeHeRe}$~%" #-acl2s-startup "")


(acl2::in-package "ACL2S B")

; ***************** END INITIALIZATION FOR ACL2s B MODE ******************* ;
;$ACL2s-SMode$;Beginner
(defdata lor (listof rational))

(defunc insert (a x)
  :input-contract (and (rationalp a) (lorp x))
  :output-contract (lorp (insert a x))
  (cond ((endp x) (list a))
        ((<= a (first x)) (cons a x))
        (t (cons (first x) (insert a (rest x))))))

(defunc isort (x)
  :input-contract (lorp x)
  :output-contract (lorp (isort x))
  (if (endp x)
      ()
    (insert (first x) (isort (rest x)))))

(defunc less (x lst)
  :input-contract (and (rationalp x) (lorp lst))
  :output-contract (lorp (less x lst))
  (cond ((endp lst) ())
        ((< (first lst) x)
         (cons (first lst) (less x (rest lst))))
        (t (less x (rest lst)))))

(defunc notless (x lst)
  :input-contract (and (rationalp x) (lorp lst))
  :output-contract (lorp (notless x lst))
  (cond ((endp lst) nil)
        ((>= (first lst) x)
         (cons (first lst) (notless x (rest lst))))
        (t (notless x (rest lst)))))

(defunc qsort (x)
  :input-contract (lorp x)
  :output-contract (lorp (qsort x))
  (if (endp x) 
      ()
    (append (qsort (less (first x) (rest x)))
            (append (list (first x))
                    (qsort (notless (first x) (rest x)))))))

(defunc orderedp (x)
  :input-contract (lorp x)
  :output-contract (booleanp (orderedp x))
  (or (endp x)
      (endp (rest x))
      (and (<= (first x) (second x))
           (orderedp (rest x)))))

(defunc del (e x)
  :input-contract (and (rationalp e) (lorp x))
  :output-contract (lorp (del e x))
  (cond ((endp x) nil)
        ((equal e (first x)) (rest x))
        (t (cons (first x) (del e (rest x))))))

(defunc perm (x y)
  :input-contract (and (lorp x) (lorp y))
  :output-contract (booleanp (perm x y))
  (if (endp x)
      (endp y)
    (and (in (first x) y)
         (perm (rest x) (del (first x) y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Q1 -- done using ACL2s
;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
(implies (lorp x)
         (orderedp (isort x)))
|#
(defthm endp-ordered
  (implies (and (lorp x) (endp x))
           (orderedp x)))

(defthm insert-endp-ordered
  (implies (and (rationalp x)
                (lorp xs)
                (endp xs)
                (orderedp xs))
           (orderedp (insert x xs))))

(defthm insert-consp-ordered
  (implies (and (rationalp x)
                (lorp xs)
                (consp xs)
                (orderedp xs))
           (orderedp (insert x xs)))) 

(defthm insert-correct
  (implies (and (rationalp x)
                (lorp xs)
                (orderedp xs))
           (orderedp (insert x xs))))

(defthm isort-end-ordered
  (implies (and (lorp xs) (endp xs))
           (orderedp (isort xs))))

(defthm isort-step-ordered
  (implies (and (lorp xs) 
                (consp xs) 
                (orderedp (isort (rest xs))))
           (orderedp (isort xs))))
;; Final proof for Q1
(defthm isort-correct
  (implies (lorp xs)
           (orderedp (isort xs))))
#|




;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Q2 -- (implies (lorp x) (orderedp (qsort x)))

Helper functions for Q2:
|#
(defunc less-than-all (x xs)
  :input-contract (and (rationalp x) (lorp xs))
  :output-contract (booleanp (less-than-all x xs))
  (cond ((endp xs) t)
        ((< x (first xs)) (less-than-all x (rest xs)))
        (t nil)))

(defunc greater-than-all (x xs)
  :input-contract (and (rationalp x) (lorp xs))
  :output-contract (booleanp (greater-than-all x xs))
  (cond ((endp xs) t)
        ((>= x (first xs)) (greater-than-all x (rest xs)))
        (t nil)))

#|
This will be proven using the induction scheme of (qsort x).

Proof obligations: 

1. (implies (not (lorp x)) Q2)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (endp x)) Q2)

C1. (lorp x)
C2. (endp x)
------------


(implies (lorp x) (orderedp (qsort x)))
={MP, C1}
(orderedp (qsort x))
={Def qsort, C2}
(orderedp nil)
={Def orderedp}
t

3. (implies (and (lorp x) (consp x) 
                 (Q2 | (x (less (first x) (rest x)))) 
                 (Q2 | (x (notless (first x) (rest x))))) 
            Q2)

C1. (lorp x)
C2. (consp x)
C3. (implies (lorp (less (first x) (rest x))) 
             (orderedp (qsort (less (first x) (rest x)))))
C4. (implies (lorp (notless (first x) (rest x))) 
             (orderedp (qsort (notless (first x) (rest x)))))
------------
C5. (and (rationalp (first x)) (lorp (rest x))) {Def lorp, C1, C2}
C6. (lorp (less (first x) (rest x))) {Contract thm less, C2, C5}
C7. (lorp (notless (first x) (rest x))) {Contract thm notless, C2, C5}
C8. (orderedp (qsort (less (first x) (rest x)))) {MP, C3, C6}
C9. (orderedp (qsort (notless (first x) (rest x)))) {MP, C4, C7}
C10. (lorp (qsort (less (first x) (rest x)))) {Contract thm, qsort, C6}
C11. (lorp (qsort (notless (first x) (rest x)))) {Contract thm, qsort, C7}
C12. (greater-than-all (first x) (less (first x) (rest x))) {L2.2, C5}
C13. (less-than-all (first x) (notless (first x) (rest x))) {L2.3, C5}
C14. (perm (less (first x) (rest x))) (qsort (less (first x) (rest x))) {Q8, C6}
C15. (perm (notless (first x) (rest x))) (qsort (notless (first x) (rest x))) {Q8, C7}
C16. (greater-than-all (first x) (qsort (less (first x) (rest x)))) {L2.5, C12, C14}
C17. (less-than-all (first x) (qsort (notless (first x) (rest x)))) {L2.6, C13, C15}


(orderedp (qsort x))
={Def qsort, C2}
(orderedp (append (qsort (less (first x) (rest x)))
                  (append (list (first x)) 
                          (qsort (less (first x) (rest x))))))
={L2.3, C5, C10, C11, C8, C9, C16, C17}
t

Thus, Q2 has been proven.

Lemmas used for Q2:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

L2.0:      
(implies (and (rationalp pivot)
              (lorp ls))
         (less-than-all pivot (notless pivot ls)))

This will be proved using the induction scheme of (notless pivot ls):

1. (implies (not (and (rationalp pivot) (lorp ls))) L2.0)

Reductio ad absurdum. Done.

2. (implies (and (rationalp pivot) (lorp ls) (endp ls)) L2.0)

C1. (rationalp pivot)
C2. (lorp ls)
C3. (endp ls)
-------------

(less-than-all pivot (notless pivot ls))
={Def notless, C1, C3}
(less-than-all pivot nil)
={Def less-than-all, C1}
t
     
3. (implies (and (rationalp pivot) (lorp ls) (not (endp ls))
                 (not (< pivot (first ls)))
                 (L2.0 | (ls (rest ls))))
            L2.0)

C1: (rationalp pivot)
C2: (lorp ls)
C3: (not (endp ls))
C4: (not (< pivot (first ls)))
C5: (implies (and (rationalp pivot) (lorp (rest ls)))
             (less-than-all pivot (notless pivot (rest ls))))
----------------------
C6: (lorp (rest ls)) {Def lorp, C3}
C7: (less-than-all pivot (notless pivot (rest ls))) {MP, C5, C6, C7}
C8: (equal (notless pivot ls) (notless pivot (rest ls)))
    {Def notless, C3, C4}
C9: (less-than-all pivot (notless pivot ls)) {C7, C8}

(less-than-all pivot (notless pivot ls))
={C9}
t

4. (implies (and (rationalp pivot) (lorp ls) (not (endp ls)) (< pivot (first ls))
                 (L2.0 | ((pivot pivot) (ls (rest ls))))) L2.0)

C1: (rationalp pivot)
C2: (lorp ls)
C3: (not (endp ls))
C4: (< pivot (first ls))
C5: (implies (and (rationalp pivot)
                  (lorp (rest ls)))
             (less-than-all pivot (notless pivot (rest ls))))
----------------
C6: (lorp (rest ls)) {Def lorp, C2, C3}
C7: (less-than-all pivot (notless pivot (rest ls))) {MP, C5, C1, C6}

(less-than-all pivot (notless pivot ls))
={Def notless, C1, C2, C4}
(less-than-all pivot (notless pivot (rest lst)))
={C7}
t
================
L2.1 
(implies (and (rationalp pivot)
              (lorp ls))
         (greater-than-all pivot (less pivot ls)))

This will be proved using the induction scheme of (less pivot ls):

1. (implies (not (and (rationalp pivot) (lorp ls))) L2.0)

Reductio ad absurdum. Done.

2. (implies (and (rationalp pivot) (lorp ls) (endp ls)) L2.0)

C1. (rationalp pivot)
C2. (lorp ls)
C3. (endp ls)
-------------

(greater-than-all pivot (less pivot ls))
={Def less, C1, C3}
(greater-than-all pivot nil)
={Def less-than-all, C1}
t
  
3. (implies (and (rationalp pivot) (lorp ls) (not (endp ls))
                 (not (>= pivot (first ls)))
                 (L2.0 | (ls (rest ls))))
            L2.0)

C1: (rationalp pivot)
C2: (lorp ls)
C3: (not (endp ls))
C4: (not (>= pivot (first ls)))
C5: (implies (and (rationalp pivot) (lorp (rest ls)))
             (greater-than-all pivot (less pivot (rest ls))))
----------------------
C6: (lorp (rest ls)) {Def lorp, C3}
C7: (greater-than-all pivot (less pivot (rest ls))) {MP, C5, C6, C7}
C8: (equal (less pivot ls) less pivot (rest ls)))
    {Def less, C3, C4}
C9: (greater-than-all pivot (less pivot ls)) {C7, C8}

(greater-than-all pivot (less pivot ls))
={C9}
t

4. (implies (and (rationalp pivot) (lorp ls) (not (endp ls)) (>= pivot (first ls))
                 (L2.0 | ((pivot pivot) (ls (rest ls))))) L2.0)

C1: (rationalp pivot)
C2: (lorp ls)
C3: (not (endp ls))
C4: (>= pivot (first ls))
C5: (implies (and (rationalp pivot)
                  (lorp (rest ls)))
             (greater-than-all pivot (less pivot (rest ls))))
----------------
C6: (lorp (rest ls)) {Def lorp, C2, C3}
C7: (greater-than-all pivot (less pivot (rest ls))) {MP, C5, C1, C6}

(greater-than-all pivot (less pivot ls))
={Def notless, C1, C2, C4}
(greater-than-all pivot (less pivot (rest lst)))
={C7}
t
================
L2.2: (implies (and (rationalp pivot) 
                    (lorp ls) 
                    (consp ls) 
                    (less-than-all pivot ls))
               (< pivot (first ls)))

This will be proven using the induction scheme of (less-than-all pivot ls)

Obligations:
1. (implies (not (and (rationalp pivot) (lorp ls))) L2.2)

Reductio ad absurdum. Done.

2. (implies (and (rationalp pivot)
                 (lorp ls)
                 (endp ls))
            L2.2)
Reductio ad absurdum. Done.

3. (implies (and (rationalp pivot)
                 (lorp ls)
                 (consp ls)
                 (not (< pivot (first ls))))
            L2.2)
Reductio ad absurdum. Done.

4. (implies (and (rationalp pivot)
                 (lorp ls)
                 (consp ls)
                 (< pivot (first ls))
                 (L2.2 | ((ls (rest ls)))))
            L2.2)
            
C1: (rationalp pivot)
C2: (lorp ls)
C3: (consp ls)
C4: (< pivot (first ls))
C5: (less-than-all pivot ls)
C6: (implies (and (rationalp pivot) (lorp (rest ls)) (consp (rest ls)) (less-than-all pivot (rest ls)))
                  (< pivot (first (rest ls))))
----------------------

(< pivot (first ls))
= {C4}
t
===============
L2.3 (implies (and (rationalp pivot) 
                    (lorp ls) 
                    (consp ls) 
                    (greater-than-all pivot ls))
               (>= pivot (first ls)))

This will be proven using the induction scheme of (greater-than-all pivot ls)

Obligations:
1. (implies (not (and (rationalp pivot) (lorp ls))) L2.2)

Reductio ad absurdum. Done.

2. (implies (and (rationalp pivot)
                 (lorp ls)
                 (endp ls))
            L2.2)
Reductio ad absurdum. Done.

3. (implies (and (rationalp pivot)
                 (lorp ls)
                 (consp ls)
                 (not (>= pivot (first ls))))
            L2.2)
Reductio ad absurdum. Done.

4. (implies (and (rationalp pivot)
                 (lorp ls)
                 (consp ls)
                 (>= pivot (first ls))
                 (L2.2 | ((ls (rest ls)))))
            L2.2)
            
C1: (rationalp pivot)
C2: (lorp ls)
C3: (consp ls)
C4: (>= pivot (first ls))
C5: (greater-than-all pivot ls)
C6: (implies (and (rationalp pivot) (lorp (rest ls)) (consp (rest ls)) (greater-than-all pivot (rest ls)))
                  (>= pivot (first (rest ls))))
----------------------

(>= pivot (first ls))
= {C4}
t
====================
L2.4

(implies (and (lorp x)
              (rationalp z)
              (rationalp y)
              (in z x)
              (less-than-all y x))
          (>= z y))

This will be proven using the induction scheme of (in z x).

Proof obligations:

1. (implies (not (and (lorp x) (rationalp z))
            L2.4)
            
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (rationalp z) (endp x))
            L2.4)
            
Reductio ad absurdum. Done.

3. (implies (and (lorp x) (rationalp z) (not (endp x)) (not (equal (first x) z))
                 (L2.4 | (x (rest x))))
            L2.4) 

C1. (lorp x)
C2. (rationalp z)
C3. (not (endp x))
C4. (not (equal (first x) z))
C5. (implies (and (lorp (rest x)) 
                  (rationalp y) 
                  (rationalp z) 
                  (in z (rest x)) 
                  (less-than-all y (rest x))) 
             (>= z y))
C6. (rationalp y)
C7. (in z x)
C8. (less-than-all y x)
------------------
C9. (and (rationalp (first x)) (lorp (rest x))) {Def lorp, C1, C6}
C10. (in z (rest x)) {Def in, C4, C6, C7}
C11. (less-than-all y (rest x)) {Def less-than-all C5, C6}
C12. (>= z y) {MP, C5, C9, C2, C6, C10, C11}

(>= z y)
={C12}
t
=================
L2.5
(implies (and (lorp x)
              (lorp y)
              (rationalp z)
              (perm y x)
              (greater-than-all z x))
         (greater-than-all z y))
|#

(defunc ind-L2.5 (x y z)
  :input-contract (and (lorp x) (lorp y) (rationalp z))
  :output-contract (booleanp (ind-L2.5 x y z))
  (cond ((endp x) (endp y))
        ((>= z (first x)) (ind-L2.5 (rest x) (del (first x) y) z))
        (t nil)))
#|
This will be proven using the induction scheme of (ind-L2.5 x y z)
Proof obligations:

1. (implies (not (and (lorp x) (lorp y) (rationalp z))
            L2.6)
Reductio ad absurdum. Done.


2. (implies (and (lorp x) (lorp y) (rationalp z) (endp x))
             L2.4)
C1. (lorp x)
C2. (lorp y)
C3. (rationalp z)
C4. (endp x)
C5. (perm y x)
C6. (greater-than-all z x)
--------------
C7. (endp y) {Def perm, C5, C4}
C8. (greater-than-all z y) {Def greater-than-all, C7}

(less-than-all z y)
={C8}
t

3. (implies (and (lorp x) (lorp y) (rationalp z)
                 (not (endp x))
                 (not (>= z (first x))))
             L2.4)

C1. (lorp x)
C2. (lorp y)
C3. (rationalp z)
C4. (not (endp x))
C5. (not (>= z (first x)))
C6. (perm y x)
C7. (greater-than-all z x)
-------------------------
C8. (and (>= z (first x)) (greater-than-all z (rest x))) {Def greater-than-all, C7, C4}
C9. (greater-than-all z y) {Reductio ad absurdum, C5, C8}

(greater-than-all z y)
={C9}
t
=================

L2.6
(implies (and (lorp x)
              (lorp y)
              (rationalp z)
              (perm y x)
              (less-than-all z x))
         (less-than-all z y))
|#

(defunc ind-L2.6 (x y z)
  :input-contract (and (lorp x) (lorp y) (rationalp z))
  :output-contract (booleanp (ind-L2.6 x y z))
  (cond ((endp x) (endp y))
        ((< z (first x)) (ind-L2.6 (rest x) (del (first x) y) z))
        (t nil)))
#|
This will be proven using the induction scheme of (ind-L2.6 x y z)
Proof obligations:

1. (implies (not (and (lorp x) (lorp y) (rationalp z))
            L2.6)
Reductio ad absurdum. Done.


2. (implies (and (lorp x) (lorp y) (rationalp z) (endp x))
             L2.4)
C1. (lorp x)
C2. (lorp y)
C3. (rationalp z)
C4. (endp x)
C5. (perm y x)
C6. (less-than-all z x)
--------------
C7. (endp y) {Def perm, C5, C4}
C8. (less-than-all z y) {Def less-than-all, C7}

(less-than-all z y)
={C8}
t

3. (implies (and (lorp x) (lorp y) (rationalp z)
                 (not (endp x))
                 (not (< z (first x))))
             L2.4)

C1. (lorp x)
C2. (lorp y)
C3. (rationalp z)
C4. (not (endp x))
C5. (not (< z (first x)))
C6. (perm y x)
C7. (less-than-all z x)
-------------------------
C8. (and (< z (first x)) (less-than-all z (rest x))) {Def less-than-all, C7, C4}
C9. (less-than-all z y) {Reductio ad absurdum, C5, C8}

(less-than-all z y)
={C9}
t
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
Q3: (implies (and (lorp x) (lorp y) (perm x y))
             (equal (len x) (len y)))

This will be proven using the induction scheme of (perm x y).

Proof obligations:

1. (implies (not (and (lorp x) (lorp y))) Q3)

Reductio ad absurdum. Done.

2. (implies (and (lorp x) (lorp y) (endp x))
            Q3)

C1: (lorp x)
C2: (lorp y)
C3: (endp x)
C4: (perm x y)
-------------
C5: (endp y) {Def perm, C3, C4}

(equal (len x) (len y))
={C4, C5}
(equal 0 0)
={equal axiom}
t

3. (implies (and (lorp x) (lorp y) (not (endp x)) (in (first x) y) 
                 (Q3 | ((x (rest x)) (y (del (first x) y)))))
            Q3)

C1: (lorp x)
C2: (lorp y)
C3: (not (endp x))
C4: (in (first x) y)
C5: (perm x y)
C6: (implies (and (lorp (rest x)) 
                  (lorp (del (first (rest x)) y)) 
                  (perm (rest x) (del (first x) y)))
             (equal (len (rest x)) 
                    (len (del (first (rest x)) y))))
--------------------------------
C7: (and (consp x) (lorp (rest x))) {Def lorp, C1, C3}
C8: (lorp (del (first (rest x)) y)) {Contract thm, C2, C3}
C9: (perm (rest x) (del (first x) y)) {Def perm, C5, C3, C2}
C10: (equal (len (rest x)) (len (del (first (rest x)) y))) {MP, C6, C7, C8, C9}
C11: (consp y) {in axiom, C4}
C12: (equal (len (rest y))
            (len (del (first (rest x)) y))) {L3, C2, C11, C5}

(equal (len x) (len y))
={C7}
(equal (len (cons (first x) (rest x))) (len y))
={C11}
(equal (len (cons (first x) (rest x)))
       (len (cons (first y) (rest y))))
={Def len}
(equal (+ 1 (len (rest x)))
       (+ 1 (len (rest y))))
={C12}
(equal (+ 1 (len (rest x)))
       (+ 1 (len (del (first (rest x)) y))))
={C10}
(equal (+ 1 (len (rest x))) (+ 1 (len (rest x))))
={equal axiom}
t

Thus, Q3 is proven.
===================
Lemma

L3: 
  (implies (and (listp x) (consp x) (in y x))
           (equal (len (rest x)) (len (del y x))))

This will be proven using the inductions scheme of (del y x).
Proof obligations:

1. (implies (not (listp x)) L3)

Reductio ad absurdum. Done.

2. (implies (and (listp x) (endp x)) L3)

Reductio ad absurdum. Done.

2. (implies (and (listp x) (not (endp x))
                 (equal y (first x)) (in y x)) L3)
                 
C1. (listp x)
C2. (not (endp x))
C3. (equal y (first x))
C4. (in y x)
-------------
 
(equal (len (rest x)) (len (del y x)))
={Def del, C2, C3}
(equal (len (rest x)) (len (rest x)))
={equal axiom}
t

3. (implies (and (listp x) (not (endp x)) (not (equal y (first x)))
                 (L3 | ((x (rest x)) (y y)))) L3)

C1: (listp x)
C2: (not (endp x))
C3: (not (equal y (first x)))
C4: (in y x)
C5: (implies (and (listp (rest x)) (consp (rest x)) (in y (rest x))
                  (equal (len (rest (rest x))) (del y (rest x)))))
--------------
C6: (in y (rest x)) {Def in, C2, C3}
C7: (consp (rest x)) {Def in, C6}
C8: (listp (rest x)) (Def listp, C1, C7}
C9: (equal (len (rest (rest x)) (del y (rest x)))) {MP, C5, C8, C7, C6}

(equal (len (rest x)) (len (del y x)))
={Def del, C2, C3}
(equal (len (rest x)) (len (cons (first x) (del y (rest x)))))
={C7}
(equal (len (cons (first (rest x)) (rest (rest x))) 
       (len (cons (first x) (del y (rest x)))))
= {Def len}
(equal (+ 1 (len (rest (rest x)))) (+ 1 (len (del y (rest x)))))
= {C9}
(equal (+ 1 (len (rest (rest x)))) (+ 1 (len (rest (rest x)))))
= {equal axiom}
t

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Q4
(implies (lorp x)
         (perm x x))

This will be proven using the inductive scheme of (listp x)

Proof obligations:
1. (implies (not (lorp x)) Q4)

Reductio ad absurdum. Done.

2. (implies (and (lorp x) (endp x)) Q4)

C1. (lorp x)
C2. (endp x)
------------

(perm x x)
={Def perm, C2}
(endp x)
={C2}
t

3. (implies (and (lorp x) (consp x) (Q4 | ((x (rest x))))) Q4)

C1: (lorp x)
C2: (consp x)
C3: (implies (lorp (rest x)) (perm (rest x) (rest x)))
-------------
C4: (in (first x) x) {Def in, C1, C2}
C5: (lorp (rest x)) {Def lorp, C2}
C6: (perm (rest x) (rest x)) {MP, C3, C5}
C7: (equal (del (first x) x) (rest x)) {def del, C2}

(implies (lorp x) (perm x x))
={MP, C1}
(perm x x)
={Def perm, C2, C4}
(perm (rest x) (del (first x) x))
={C7}
(perm (rest x) (rest x))
={C6}
t

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
Q5:

(implies (and (lorp x) (lorp y) (perm x y))
         (perm y x))
         
This will be proven using the induction scheme of (perm y x)

1. (implies (not (and (lorp x) (lorp y))) Q5)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (lorp y) (endp y)) Q5)

C1. (lorp x)
C2. (lorp y)
C3. (perm x y)
C4. (endp y)
--------------
C5. (endp x) {Q3, C4, C3}

(perm y x)
={C4}
(endp x)
={C5}
t

3. (implies (and (lorp x) (lorp y) (not (endp y))
                 (in (first y) x)
                 (Q5 | ((y (rest y)) (x (del (first y) x)))))
            Q5)
            
C1. (lorp x)
C2. (lorp y)
C3. (not (endp y))
C4. (in (first y) x)
C5. (implies (and (lorp (rest y) (lorp (del (first y) x)) 
                  (perm (del (first y) x) (rest y)))
             (perm (rest y) (del (first y) x)))
----------------------
C6. (not (endp x)) {Q3, C3, C3}
C7. (in (first y) x) {L5.1, C1, C2, C3, C5}
C8. (equal (del (first y) y) (rest y)) {Def del, C3}
C9. (perm (del (first y) x) (del (first y) y)) {L5.2, C3, C7}
C10. (perm (del (first y) x) (rest y)) {C9, C8}
C11. (and (rationalp (first y)) (lorp (rest y))) {Def lorp, C2}
C12. (lorp (del (first y) x)) {Contract thm, del, C1, C11}
C13. (perm (rest y) (del (first y) x)) {MP, C12, C11, C5}
C14. (perm y x) {Def perm, C13, C7, C6}

(implies (and (lorp x) (lorp y) (perm x y)) (perm y x))
={MP, C1, C2, C3}
(perm y x)
={C14}
t
=======================
Lemmas

L5.0
(implies (and (lorp x) (lorp y) 
              (in z x)
              (perm (del z x) y))
         (perm x (cons z y)))
|#
(defunc ind-L5-a (x y z)
  :input-contract (and (lorp x) (lorp y) (rationalp z))
  :output-contract (booleanp (ind-L5-a x y z))
  (cond ((endp x) (endp y))
        ((equal (first x) z) (in z y))
        (t (ind-L5-a (rest x) (del (first x) y) z))))
#|
This will be proven using the induction scheme of (ind-L5-a x y z).

Proof obligations:
1. (implies (not (lorp x)) L5.0)

Reductio ad absurdum.

2. (implies (and (lorp x) (endp x)) L5.0)
Reductio ad absurdum.

3. (implies (and (lorp x) (not (endp x)) (equal (first x) z)) L5.0)

C1. (lorp x)
C2. (not (endp x))
C3. (equal (first x) z)
C4. (perm (del z x) y)
-------------------
C5. (equal (del z x) (rest x)) {Def del, C2, C3}

(perm x (cons z y))
={C2, C3}
(perm (cons z (rest x)) (cons z y))
={Def perm}
(and (in z (cons z y)) (perm (rest x) (del z (cons z y))))
={Def in}
(perm (rest x) (del z (cons z y)))
={def del}
(perm (rest x) y)
={C5}
(perm (del z x) y)
={C4}
t

3. (implies (and (lorp x) (not (endp x)) (not (equal (first x) z))
                 (L5.0 | ((x (rest x)) (y (del (first x) y))))) L5.0)
C1. (lorp x)
C2. (not (endp x))
C3. (not (equal (first x) z))
C4. (implies (and (lorp (rest x)) (lorp (del (first x) y))
                  (in z (rest x))
                  (perm (rest x) (del (first x) y)))
             (perm (rest x) (cons z (del (first x) y))))
C5. (in z x)             
C6. (perm (del z x) y)
-------------------
C7. (equal (del z x) (cons (first x) (del z (rest x)))) {Def del, C2, C3}
C8. (and (in (first x) y) (perm (del z (rest x)) (del (first x) y))) {Def perm, C6, C7}
C9. (in z (cons z (del (first x) y))) {Def in}
C10. (perm (cons z (del z (rest x))) (cons z (del (first x) y))) {Def perm, C9, C8}
C11. (perm (cons z (del z (rest x)) (rest x)) {reflexivity of perm}
C12. (perm (rest x) (cons z (del (first x) y))) {transitivity of perm}
C13. (perm (rest x) (del (first x) (cons z y))) {Def del, C3}
C14. (perm x (cons z y)) {Def perm, C8, C13}


(perm x (cons z y))
={C14}
t

===================
L5.1:

(implies (and (listp x) (listp y) (consp y) (perm x y))
         (in (first y) x))
         
This will be proven using the induction scheme of (perm x y).

Proof obligations:
1. (implies (not (and (listp x) (listp y)) L5.1)
Reductio ad absurdum. Done.

2. (implies (and (listp x) (listp y) (endp x))
            L5.1)
            
C1. (listp x)
C2. (listp y)
C3. (endp x)
C4. (consp y)
C5. (perm x y)
-------------------
C6. (endp y) {Def perm, C5}
C7. False {C4, C6}
C8. L5.1 {Reductio ad absurdum, C7}

L5.1
={C8}
t
            
3. (implies (and (listp x) (listp y)
                 (not (endp x)) 
                 (L5.1 | ((x (rest x)) (y (del (first x) y)))))
            L5.1)
C1. (listp x)
C2. (listp y)
C3. (not (endp x))
C4. (implies (and (listp (rest x)) (listp (del (first x) y))
                  (perm (rest x) (del (first x) y)))
             (perm (del (first x) y) (rest x)))
C5. (perm x y)
-------------------
C6. (and (in (first x) y) (perm (rest x) (del (first x) y))) {Def perm, C4, C5}
C7. (listp (rest x)) {Def listp, C1, C3}
C8. (listp (del (first x) y)) {Contract thm, del, C2, C3}
C9. (perm (del (first x) y) (rest x)) {MP, C4, C6, C7, C8}
C10. (perm y x) {L5.0, C1, C2, C6, C9}

(perm y x)
={C10}
t
===================
L5.2

(implies (and (lorp x) (lorp y) (rationalp z)
              (in z x) (in z y) (perm x y))
              (perm (del z x) (del z y)))

This will be proven using the induction scheme of (ind-L5-a x y z)

1. (implies (not (and (lorp x) (lorp y) (rationalp z))
            L5.2)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (lorp y) (rationalp z) (endp x))
            L5.2)
Reductio ad absurdum. Done.

3. (implies (and (lorp x) (lorp y) (rationalp z) (not (endp x))
                 (equal (first x) z))
            L5.2)
C1. (lorp x)
C2. (lorp y)
C3. (rationalp z)
C4. (not (endp x))
C5. (equal (first x) z)
C6. (in z x)
C7. (in z y)
C8. (perm x y)
--------------------

(perm (del z x) (del z y))
={Def del, C4, C5}
(perm (rest x) (del z y))
={C5}
(perm (rest x) (del (first x) y))
={Def perm, C4, C8}
t

4. (implies (and (lorp x) (lorp y) (rationalp z)
                 (not (endp x))
                 (not (equal (first x) z))
                 (L5.2 | ((x (rest x)) (y (del (first x) y)))))
            L5.2)
C1. (lorp x)
C2. (lorp y)
C3. (rationalp z)
C4. (not (endp x))
C5. (not (equal (first x) z))
C6. (implies (and (lorp (rest x)) (lorp (del (first x) y)) (rationalp z)
             (in z (rest x)) (in z (del (first x) y)) (perm (rest x) (del (first x) y)))
             (perm (del z (rest x)) (del z (del (first x) y))))
C7. (in z x)
C8. (in z y)
C9. (perm x y)
--------------------            
C10. (and (rationalp (first x)) (lorp (rest x))) {Def lorp, C1, C4}
C11. (lorp (del (first x) y)) {Contract thm, C10, C2}
C12. (in z (rest x)) {Def in, C4, C5, C7}
C13. (in z (del (first x) y)) {L6 (proven below for Q6), C8, C12}
C14. (perm (rest x) (del (first x) y)) {Def perm, C6, C7}
C15. (perm (del z (rest x)) (del z (del (first x) y))) {MP, C9, C10, C11, C12, C13, C14}
C16. (equal (del z (del (first x) y)) (del (first x) (del z y))) {L5.3, C2, C3, C10}
C17. (perm (del z (rest x)) (del (first x) (del z y))) {Transitivity of perm, C15, C16}
C18. (perm (cons (first x) (del z (rest x))) (del z y)) {Def perm, C17}



(perm (del z x) (del z y))
={Def del, C7, C8}
(perm (cons (first x) (del z (rest x))) (del z y))
={C18}
t
===================
L5.3

(implies (and (lorp x) (rationalp y) (rationalp z))
         (equal (del y (del z x)) (del z (del y x))))
|#
(defunc ind-L5-b (x y z)
  :input-contract (and (lorp x) (rationalp y) (rationalp z))
  :output-contract (booleanp (ind-L5-b x y z))
  (cond ((endp x) nil)
        ((equal (first x) y) t)
        ((equal (first x) z) t)
        (t (ind-L5-b (rest x) y z))))
#|

         
This will be proven using the induction scheme of (ind-L5-b x y z)

1. (implies (not (and (lorp x) (rationalp y) (rationalp z))) L5.3)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (rationalp y) (rationalp z) (endp x)) L5.3)

C1. (lorp x)
C2. (rationalp y)
C3. (rationalp z)
C4. (endp x)
--------------

(implies (and (lorp x) (rationalp y) (rationalp z))
         (equal (del y (del z x)) (del z (del y x))))
={MP, C1, C2, C3}  
(equal (del y (del z x)) (del z (del y x)))
={Def del, C4}
(equal (del y nil) (del z nil))
={Def del}
(equal nil nil)
={equal axiom}
t

2. (implies (and (lorp x) (rationalp y) (rationalp z) (not (endp x))
                 (equal (first x) y)) 
            L5.3)

C1. (lorp x)
C2. (rationalp y)
C3. (rationalp z)
C4. (not (endp x))
C5. (equal (first x) y)
--------------
C6. (or (equal y z) (not (equal y z)))
C7. (implies (equal y z) (equal (del z x) (rest x))) {Def del, C5}
C8. (implies (equal y z) (equal (del y (del z x)) (del z (rest x)))) {C7}
C9. (implies (not (equal y x)) 
             (equal (del y (del z x))
                    (del y (cons (first x) (del z (rest x)))))) {Def del, C4}
C10. (implies (not (equal y x))
              (equal (del y (del z x))
                     (del z (rest x))))
C11. (equal (del y (del z x)) (del z (rest x))) {Or-elim C6, C8, C10}

(implies (and (lorp x) (rationalp y) (rationalp z))
         (equal (del y (del z x)) (del z (del y x))))
={MP, C1, C2, C3}  
(equal (del y (del z x)) (del z (del y x)))
={Def del, C5}
(equal (del y (del z x)) (del z (rest x)))
={C11}
t

3. (implies (and (lorp x) (rationalp y) (rationalp z) (not (endp x))
                 (equal (first x) z)) 
            L5.3)
C1. (lorp x)
C2. (rationalp y)
C3. (rationalp z)
C4. (not (endp x))
C5. (equal (first x) z)
--------------
C6. (or (equal y z) (not (equal y z)))
C7. (implies (equal y z) (equal (del y x) (rest x))) {Def del, C5}
C8. (implies (equal y z) (equal (del z (del y x)) (del z (rest x)))) {C7}
C9. (implies (not (equal y x)) 
             (equal (del z (del y x))
                    (del z (cons (first x) (del y (rest x)))))) {Def del, C4}
C10. (implies (not (equal y x))
              (equal (del z (del y x))
                     (del y (rest x))))
C11. (equal (del z (del y x)) (del y (rest x))) {Or-elim C6, C8, C10}

(implies (and (lorp x) (rationalp y) (rationalp z))
         (equal (del y (del z x)) (del z (del y x))))
={MP, C1, C2, C3}  
(equal (del y (del z x)) (del z (del y x)))
={Def del, C5}
(equal (del y (rest x)) (del z (del y x)))
={C11}
t
            
4. (implies (and (lorp x) (rationalp y) (rationalp z) (not (endp x))
                 (not (equal (first x) y)) (not (equal (first x) z))
                 (L5.3 | (x (rest x))))
            L5.3) 

C1. (lorp x)
C2. (rationalp y)
C3. (rationalp z)
C4. (not (endp x))
C5. (not (equal (first x) y))
C6. (not (equal (first x) z))
C7. (implies (and (lorp (rest x)) (rationalp y) (rationalp z))
             (equal (del y (del z (rest x))) (del z (del y (rest x)))))
-----------------------
C8. (lorp (rest x)) {Def lorp, C1, C4}
C9. (equal (del y (del z (rest x))) (del z (del y (rest x)))) {MP, C7, C8, C2, C3}

(implies (and (lorp x) (rationalp y) (rationalp z))
         (equal (del y (del z x)) (del z (del y x))))
={MP, C1, C2, C3}  
(equal (del y (del z x)) (del z (del y x)))
={Def del, C6}
(equal (del y (cons (first x) (del z (rest x)))) (del z (del y x)))
={Def del, C5}
(equal (cons (first x) (del y (del z (rest x)))) (del z (cons (first x) (del y (rest x)))))
={Def del, C6}
(equal (cons (first x) (del y (del z (rest x)))) (cons (first x) (del z (del y (rest x)))))
={C9}
(equal (cons (first x) (del y (del z (rest x)))) 
       (cons (first x) (del y (del z (rest x)))))
={equal axiom}
t

;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;
Q6: 
(implies (and (lorp x) (lorp y) (lorp z) 
              (perm x y) (perm y z))
         (perm x z))
         
|#
(defunc perm-2 (x y z)
  :input-contract (and (lorp x) (lorp y) (lorp z))
  :output-contract (booleanp (perm-2 x y z))
  (cond ((endp x) (and (endp y) (endp z)))
        ((and (in (first x) y)
              (in (first x) z))
         (perm-2 (rest x)
                 (del (first x) y)
                 (del (first x) z)))
        (t nil)))

#|
This will be proven using the induction scheme of (perm-2 x y z)


1. (implies (not (and (lorp x) (lorp y) (lorp z)))
            Q6)

Reductio ad absurdum. Done.


2. (implies (and (lorp x) (lorp y) (lorp z) (endp x))
            Q6)

C1. (lorp x)
C2. (lorp y)
C3. (lorp z)
C4. (endp x)
C5. (perm x y)
C6. (perm y z)
-------------
C7. (endp y) {Def perm, C5, C4}
C8. (endp z) {Def perm, C6, C7}

(perm x z)
={Def perm, C4}
(endp z)
={C8}
t


3. (implies (and (lorp x) (lorp y) (lorp z) 
                 (not (endp x))
                 (not (and (in (first x) y)
                           (in (first x) z))))
            Q6)

C1. (lorp x)
C2. (lorp y)
C3. (lorp z)
C4. (not (endp x))
C5. (not (and (in (first x) y) (in (first x) z)))
C6. (perm x y)
C7. (perm y z)
-------------            
C8. (and (in (first x) y) (perm (rest x) (del (first x) y)))
C9. (not (in (first x) z)) {PL, C5, C8}
C10. (in (first x) z) {L6, C2, C8, C7}
C11. (perm x z) {F-elim, C9, C10}
(perm x z)
={C11}
t

4. (implies (and (lorp x) (lorp y) (lorp z) 
                 (not (endp x))
                 (in (first x) y)
                 (in (first x) z)
                 (Q6 | ((x (rest x)) (y (del (first x) y)) (z (del (first x) z)))))
            Q6)

C1. (lorp x)
C2. (lorp y)
C3. (lorp z)
C4. (not (endp x))
C5. (in (first x) y)
C6. (in (first x) z)
C7. (implies (and (lorp (rest x))
                  (lorp (del (first x) y))
                  (lorp (del (first x) z))
                  (perm (rest x) (del (first x) y))
                  (perm (del (first x) y) (del (first x) z)))
             (perm (rest x) (del (first x) z)))
C8. (perm x y)
C9. (perm y z)
--------------------------------             
C10. (and (rationalp (first x)) (lorp (rest x))) {Def lorp, C1, C4}
C11. (lorp (del (first x) y)) {Contract thm, del, C2, C10}
C12. (lorp (del (first x) z)) {Contract thm, del, C3, C10}
C13. (perm (rest x) (del (first x) y)) {Def perm, C8, C4}
C14. (not (endp y)) {in axiom, C5}
C15. (perm (del (first x) y) (del (first x) z)) {Def perm, C9, C14}
C16. (perm (rest x) (del (first x) z)) {MP, C7, C10, C11, C12, C13, C15}
C17. (perm x z) {Def perm, C4, C6, C16}

(perm x z)
={C17}
t

Thus, Q6 has been proven.

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;
Q7:

(implies (lorp x) (perm (isort x) x))

This will be proven using the induction scheme of (lorp x)
Proof obligations:

2. (implies (endp x) Q7)

C1. (endp x)
----------

(implies (lorp x) (perm (isort x) x))
={MP, C1}
(perm (isort x) x)
={Def isort, C1}
(perm () x)
={Def perm}
(endp x)
={C1}
t

3. (implies (and (lorp x) (consp x) (Q7 | ((x (rest x))))) Q7)

C1. (lorp x)
C2. (consp x)
C3. (implies (lorp (rest x)) (perm (isort (rest x)) (rest x)))
-------------
C4. (lorp (rest x)) {Def lorp, C1, C2}
C5. (lorp (isort x)) {Contract thm, isort, C1}
C6. (perm (isort (rest x)) (rest x)) {MP, C3, C4}

(implies (lorp x) (perm (isort x) x))
={MP, C1}
(perm (isort x) x)
={Q5, C1, C5}
(perm x (isort x))
={C2}
(perm (cons (first x) (rest x)) (isort x))
={Def isort, C2}
(perm (cons (first x) (rest x)) 
      (insert (first x) (isort (rest x))))
={Def perm}
(and (in (first x) (insert (first x) (isort (rest x))))
     (perm (rest x) (del (first x) (insert (first x) (isort (rest x))))))
={L7.1}
(perm (rest x) (del (first x) (insert (first x) (isort (rest x)))))
={L7.2}
(perm (rest x) (isort (rest x)))
={C6}
t
====================
L7.1:

(implies (lorp x) (in z (insert z x)))

This will be done using the induction scheme of (insert z x)

Proof obligations:

1. (implies (not (and (lorp x) (rationalp z))) L7.1)
Reductio ad absurdum. done.

2. (implies (and (lorp x) (rationalp z) (endp x)) L7.1)

C1. (lorp x)
C2. (rationalp z)
C3. (endp x)
------------

(implies (lorp x) (in z (insert z x)))
={MP, C1}
(in z (insert z x))
={Def insert, C3}
(in z (list z))
={equal axiom}
(in z (cons z nil))
={Def in}
t

3. (implies (and (lorp x) (rationalp z) (consp x) (<= z (first x))) L7.1)

C1. (lorp x)
C2. (rationalp z)
C3. (consp x)
C4. (<= z (first x))
------------------

(implies (lorp x) (in z (insert z x)))
={MP, C1}
(in z (insert z x))
={Def insert, C3, C4}
(in z (cons z x))
={Def in}
t

4. (implies (and (lorp x) (rationalp z) (consp x) (> z (first x)) (L7.1 | (x (rest x)))) L7.1)

C1. (lorp x)
C2. (rationalp z)
C3. (consp x)
C4. (> z (first x))
C5. (implies (lorp (rest x)) (in z (insert z (rest x))))
----------------------------
C6. (lorp (rest x)) {Def lorp, C1, C3}
C7. (in z (insert z (rest x))) {MP, C5, C6}

(implies (lorp x) (in z (insert z x)))
={MP, C1}
(in z (insert z x))
={Def insert, C2, C3}
(in z (cons (first x) (insert z (rest x))))
={Def in, C2, C3}
(in z (insert z (rest x)))
={C6}
t
====================
L7.2:

(implies (lorp x) (equal x (del z (insert z x))))

This will be proven using the induction scheme of (insert z x)

Proof obligations:

1. (implies (not (and (lorp x) (rationalp z))) Q7)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (rationalp z) (endp x)) Q7)

C1. (lorp x)
C2. (rationalp z)
C3. (endp x)
------------

(implies (lorp x) (equal x (del z (insert z x))))
={MP, C1}
(equal x (del z (insert z x)))
={def insert, C3}
(equal x (del z (list z)))
={def del}
(equal x ())
={C1, C3}
t

3. (implies (and (lorp x) (rationalp z) (consp x) (<= z (first x))) Q7)

C1. (lorp x)
C2. (rationalp z)
C3. (consp x)
C4. (<= z (first x))
-----------------------

(implies (lorp x) (equal x (del z (insert z x))))
={MP, C1}
(equal x (del z (insert z x)))
={Def insert, C3, C4}
(equal x (del z (cons z x)))
={Def del}
(equal x x)
={equal axiom}
t

4. (implies (and (lorp x) (rationalp z) (consp x) (> z (first x)) (Q7 | ((x (rest x))))) Q7)

C1. (lorp x)
C2. (rationalp z)
C3. (consp x)
C4. (> z (first x))
C5. (implies (lorp (rest x)) (equal (rest x) (del z (insert z (rest x)))))
-----------------------
C6. (lorp (rest x)) {Def lorp, C1, C2}
C7. (equal (rest x) (del z (insert z (rest x)))) {MP, C4, C5}


(implies (lorp x) (equal x (del z (insert z x))))
={MP, C1}
(equal x (del z (insert z x)))
={Def insert, C3, C4}
(equal x (del z (cons (first x) (insert z (rest x)))))
={Def del, C3, C4}
(equal x (cons (first x) (del z (insert z (rest x)))))
={C7}
(equal x (cons (first x) (rest x)))
={cons axiom, C3}
t
;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;
Q8: (implies (lorp x) (perm (qsort x) x))

This will be proven using the induction scheme of (qsort x).

Proof obligations:

1. (implies (not (lorp x)) Q8)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (endp x)) Q8)

C1. (lorp x)
C2. (endp x)
------------

(implies (lorp x) (perm (qsort x) x))
={MP, C1}
(perm (qsort x) x)
={Def qsort, C2}
(perm () x)
={Def perm}
(endp x)
={C2}
t

2. (implies (and (lorp x) (consp x) 
                 (Q8 | (x (less (first x) (rest x))))
                 (Q8 | (x (notless (first x) (rest x))))) 
            Q8)

C1. (lorp x)
C2. (consp x)
C3. (implies (lorp (less (first x) (rest x))) 
             (perm (qsort (less (first x) (rest x))) 
                   (less (first x) (rest x))))
C4. (implies (lorp (notless (first x) (rest x))) 
             (perm (qsort (notless (first x) (rest x))) 
                   (notless (first x) (rest x))))                   
--------------
C5. (lorp (rest x)) {Def lorp, C1, C2}
C6. (rationalp (first x)) {Def lorp, C1, C2}
C7. (lorp (less (first x) (rest x))) {Contract thm, less, C5, C6}
C8. (lorp (notless (first x) (rest x))) {Contract thm, notless, C5, C6}
C9. (lorp (less (first x) (rest x))) {Contract thm, less, C5, C6}
C10. (perm (qsort (less (first x) (rest x))) 
           (less (first x) (rest x))) {MP, C3, C8}
C11. (perm (qsort (notless (first x) (rest x))) 
           (notless (first x) (rest x))) {MP, C4, C9}
C12. (perm (append (less (first x) (rest x))
                   (append (list (first x))
                           (qsort (notless (first x) (rest x)))))
           (append (qsort (less (first x) (rest x)))
                   (append (list (first x))
                           (qsort (notless (first x) (rest x)))))) {L8.1}
C13. (perm (append (less (first x) (rest x))
                   (append (list (first x))
                           (notless (first x) (rest x))))                            
           (append (qsort (less (first x) (rest x)))
                   (append (list (first x))
                           (qsort (notless (first x) (rest x)))))) {L8.3}
C14. (perm (append (less (first x) (rest x))
                   (notless (first x) (rest x)))
           (rest x)) {L8.4}
C13. (perm (append (list (first x))
                   (append (less (first x) (rest x))
                           (notless (first x) (rest x))))
           x) {Def append, perm, C2, C14}
C14. (perm (append (less (first x) (rest x))
                   (append (list (first x))
                           (notless (first x) (rest x))))
           x) {L8.5, C13}
C15. (perm (append (qsort (less (first x) (rest x)))
                   (append (list (first x))
                           (qsort (notless (first x) (rest x)))))
           x) {Q7, Q6, C15, C13}

(implies (lorp x) (perm (qsort x) x))     
={MP, C1}
(perm (qsort x) x)
={Def qsort, C2}
(perm (append (qsort (less (first x) (rest x)))
              (append (list (first x))
                      (qsort (notless (first x) (rest x)))))
      x)
={C15}
t
=================
L8.1:

(implies (and (lorp x)
              (lorp y)
              (lorp z)
              (perm x y))
         (perm (append x z) (append y z)))

This will be proven using the induction scheme for (perm x y).

1. (implies (not (and (lorp x) (lorp y))) L8.1)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (lorp y) (endp x))
            L8.1)
C1. (lorp x)
C2. (lorp y)
C3. (endp x)
C4. (lorp z)
C5. (perm x y)
-----------------------
C6. (endp y) {Def perm, C5, C3}
C7. (perm z z) {reflexivity of perm, C4}
C8. (perm (append x z) z) {Def append, C3, C7}
C9. (perm (append x z) (append y z)) {Def append, C6, C8}

(perm (append x z) (append y z))
={C9}
t

2. (implies (and (lorp x) (lorp y) (lorp z) 
                 (not (endp x))
                 (in (first x) y)
                 (L8.1 | ((x (rest x)) (y (del (first x) y)))))
            L8.1)
C1. (lorp x)
C2. (lorp y)
C3. (not (endp x))
C4. (in (first x) y)
C5. (implies (and (lorp (rest x)) (lorp (del (first x) y)) (lorp z) (perm (rest x) (del (first x) y)))
              (perm (append (rest x) z) (append (del (first x) y) z)))
C6. (lorp z)
C7. (perm x y)
-----------------------
C8. (and (rationalp (first x)) (lorp (rest x))) {Def lorp, C1, C3}
C9. (lorp (del (first x) y)) {Contract thm, del, C3, C2}
C10. (and (in (first x) y) (perm (rest x) (del (first x) y))) {Def perm, C7, C3}
C11. (perm (append (rest x) z) (append (del (first x) y) z)) {MP, C5, C8, C9, C3, C10}
C12. (in (first x) (append y z)) {apend axiom, C4}
C13. (equal (append (del (first x) y) z) (del (first x) (append y z))) {L8.2, C2, C8, C10}
C14. (perm (append (rest x) z) (del (first x) (append y z))) {C11, C13}
C15. (perm (cons (first x) (append (rest x) z)) (append y z)) {Def perm, C14}
C16. (perm (apend x z) (append y z)) {Def append, C15}

(perm (append x z) (append y z))
={C16}
t
=====================
L8.2
(implies (and (lorp y) (lorp z) (rationalp x) (in x y))
         (equal (append (del x y) z)
                (del x (append y z))))
                
This will be proven with the induction scheme of (in x y).

1. (implies (not (lorp y)) L8.2)
Reductio ad absurdum. Done.

2. (implies (and (lorp y) (endp y)) L8.2)
Reductio ad absurdum.

3. (implies (and (lorp y) (not (endp y)) (equal x (first y))) L8.2)

C1. (lorp y)
C2. (not (endp y))
C3. (equal x (first y))
C4. (rationalp x)
C5. (in x y)
--------------


(equal (append (del x y) z)
       (del x (append y z)))
={Def del, C3}
(equal (append (rest y) z)
       (del x (append y z)))
={Def append, C2}
(equal (append (rest y) z)
       (del x (cons (first y) (append (rest y) z))))
={Def del, C3}
(equal (append (rest y) z)
       (append (rest y) z))
={equal axiom}
t

4. (implies (and (lorp y) (not (endp y)) (not (equal x (first y)))
                 (L8.2 | ((y (rest y))))) L8.2)

C1. (lorp y)
C2. (not (endp y))
C3. (not (equal x (first y)))
C4. (implies (and (lorp (rest y)) (rationalp x))
             (equal (append (del x (rest y)) z)
                    (del x (append (rest y) z))))
C5. (rationalp x)
C6. (in x y)
--------------
C7. (lorp (rest y)) {Def lorp, C1, C2}
C8. (equal (append (del x (rest y)) z)
           (del x (append (rest y) z))) {MP, C7, C5}

(equal (append (del x y) z)
       (del x (append y z)))
={Def del, C2, C3}
(equal (append (cons (first y) (del x (rest y))) z)
       (del x (append y z)))
={Def append, C2}
(equal (cons (first y) (append (del x (rest y)) z))
       (del x (cons (first y) (append (rest y) z)))
={Def del, C3}
(equal (cons (first y) (append (del x (rest y)) z))
       (cons (first y) (del x (append (rest y) z)))
={C8}       
(equal (cons (first y) (append (del x (rest y)) z))
       (cons (first y) (del x (append (rest y) z)))       
={equal axiom}
t
====================
L8.3:
(implies (and (lorp x)
              (lorp y)
              (lorp z)
              (perm x y))
         (perm (append z x) (append z y)))

This will be proven using the induction scheme (lorp z).

Proof obligations:

1. (implies (endp z) L8.3)

C1. (endp z)
C2. (lorp x)
C3. (lorp y)
C4. (lorp z)
C5. (perm x y)
--------------

(perm (append z x) (append z y))
={Def append, C1}
(perm x y)
={C5}
t

2. (implies (and (consp z) (rationalp (first z)) (lorp (rest z))
                 (L8.3 | ((z (rest z)))))
            L8.3)

C1. (consp z)
C2. (rationalp (first z))
C3. (lorp (rest z))
C4. (implies (and (lorp x) (lorp y) (lorp (rest z)) (perm x y))
             (perm (append (rest z) x) (append (rest z) y)))
C5. (lorp x)
C6. (lorp y)
C7. (perm x y)
--------------    
C8. (perm (append (rest z) x) (append (rest z) y)) {MP, C4, C5, C, C3, C7}
C9. (in (first z) (cons (first z) (append (rest z) y))) {Def in}

(perm (append z x) (append z y))
={Def append, C1}
(perm (cons (first z) (append (rest z) x))
      (cons (first z) (append (rest z) y)))
={Def perm, C9}
(perm (append (rest z) x)
      (del (first z) (cons (first z) (append (rest z) y))))
={Def del}
(perm (append (rest z) x)
      (append (rest x) y))
={C8}
t

===================
L8.4:
(implies (and (lorp x) (rationalp z))
         (perm x (append (less z x) (notless z x))))

This will be proven using the induction scheme of (lorp x).

Proof obligations:

1. (implies (endp x) L8.4)

C1. (endp x)
C2. (lorp x)
C3. (rationalp z)
-----------------

(perm x (append (less z x) (notless z x)))
={Def less, notless, C1}
(perm x (append nil nil))
={Def append}
(perm x nil)
={Def perm, C1}
(endp nil)
={Def endp}
t

2. (implies (and (consp x) (rationalp (first x)) (lorp (rest x))
                 (L8.4 | ((x (rest x)))))

C1. (consp x)
C2. (rationalp (first x))
C3. (lorp (rest x))
C4. (implies (and (lorp (rest x)) (rationalp z))
             (perm (rest x) (append (less z (rest x)) (notless z (rest x)))))
C5. (rationalp z)
----------------
C6. (perm (rest x) (append (less z (rest x)) (notless z (rest x)))) {MP, C4, C3, C5}
C7. (or (< (first x) z) (>= (first x) z)) {PL}
C8. (implies (< (first x) z) (in (first x) (less z x))) {Def less, C1}
C9. (implies (>= (first x) z) (in (first x) (notless z x))) {Def notless, C1}
C11. (implies (< (first x) z) (in (first x) (append (less z x) (notless z x)))) {append axiom, C8}
C12. (implies (>= (first x) z) (in (first x) (append (less z x) (notless z x)))) {append axiom, C9}
C13. (in (first x) (append (less z x) (notless z x))) {Or-elim, C7, C11, C12}
C14. (implies (< (first x) z) (equal (less z x) (cons (first x) (less z (rest x))))) {Def less, C1}
C15. (implies (>= (first x) z) (equal (notless z x) (cons (first x) (notless z (rest x))))) {Def notless, C1}
C16. (implies (>= (first x) z) (not (in (first x) (notless z (rest x))))) {Def notless}
C17. (implies (< (first x) z) 
              (equal (del (first x) (append (less z x) (notless z x)))
                     (append (less z (rest x)) (notless z (rest x))))) {C14}
C18. (implies (>= (first x) z) 
              (equal (del (first x) (append (less z x) (notless z x)))
                     (append (less z (rest x)) (notless z (rest x))))) {C16}                                     
C19. (equal (del (first x) (append (less z x) (notless z x)))
            (append (less z (rest x)) (notless z (rest x)))) {Or-elim C7, C17, C18}

(perm x (append (less z x) (notless z x)))
={Def perm, C1, C13}
(perm (rest x) (del (first x) (append (less z x) (notless z x))))
={C19}
(perm (rest x) (append (less z (rest x)) (notless z (rest x))))
={C6}
t

====================   
L8.5:
(implies (and (lorp x) (lorp y) (lorp z) (lorp w) 
              (perm (append x (append y z)) w))
         (perm (append y (append x z)) w))
         
This will be proven using the inductive scheme of (perm x w)

1. (implies (not (and (lorp x) (lorp w))) L8.5)
Reductio ad absurdum. Done.

2. (implies (endp x) L8.5)

C1. (endp x)
C2. (lorp x)
C3. (lorp y)
C4. (lorp z)
C5. (lorp w)
C6. (perm (append x (append y z)) w)
-----------------
C7. (perm (append y z) w) {Def append, C6, C1}

(perm (append y (append x z)) w)
={Def append, C1}
(perm (append y z) w)
={C7}
t

3. (implies (and (lorp x) (consp x)
            (in (first x) w)
            (L8.5 | ((x (rest x)) (w (del (first x) w))))
            L8.5)

C1. (lorp x)
C2. (consp x)
C3. (in (first x) w)
C4. (implies (and (lorp (rest x)) (lorp y) (lorp z) (lorp (del (first x) w)) 
                  (perm (append (rest x) (append y z)) (del (first x) w)))
             (perm (append y (append (rest x) z)) (del (first x) w)))
C5. (lorp y)
C6. (lorp z)
C7. (lorp w)
C8. (perm (append x (append y z)) w)
------------------------------------
C8. (and (in (first x) w)
         (perm (append (rest x) (append y z)) (del (first x) w))) {def perm, C8, C4}
C9. (lorp (del (first x) w)) {Contract thm, del, C2, C7}
C10. (perm (append y (append (rest x) z)) (del (first x) w)) {MP, C4, C5, C6, C9, C8}
C11. (perm (cons (first x) (append y (append (rest x) z))) (del (first x) w)) {Def perm, C10}
C12. (perm (cons (first x) (append y (append (rest x) z))) (append y (append x z))) {L8.6, C11}
C13. (perm (append y (append x z)) w) {transitivity of perm, C11, C12}
(perm (append y (append x z)) w)  
={C13}
t
==================
L8.6
(implies (and (lorp x) (lorp y) (lorp z) (rationalp q))
         (perm (cons q (append x (append y z)))
               (append x (cons q (append y z)))))
               
This will be proven using the induction scheme from (lorp x).

1. (implies (endp x) L8.6)

C1. (endp x)
C2. (lorp x)
C3. (lorp y)
C4. (lorp z)
C5. (rationalp q)
----------------

(perm (cons q (append x (append y z)))
      (append x (cons q (append y z))))
={Def append, C1}
(perm (cons q (append y z))
      (cons q (append y z)))
={reflexivity of perm}
t

2. (implies (and (lorp x) (consp x)
                 (L8.6 | ((x (rest x)))) L8.6)

C1. (lorp x)
C2. (consp x)
C3. (implies (and (lorp (rest x) (lorp y) (lorp z) (rationalp q))
             (perm (cons q (append (rest x) (append y z)))
                   (append (rest x) (cons q (append y z)))))
C4. (lorp y)
C5. (lorp z)
C6. (rationalp q)
----------------
C7. (lorp (rest x)) {Def lorp, C1, C2}
C8. (perm (cons q (append (rest x) (append y z)))
          (append (rest x) (cons q (append y z)))) {MP, C3, C7, C4, C5, C6}
C9. (perm (append (rest x) (cons q (append y z)))
          (cons q (append (rest x) (append y z)))) {symmetry of perm, C8}          
C10. (or (equal (first x) q)
        (not (equal (first x) q)) {PL}
C11. (implies (equal (first x) q)
              (equal (del (first x) (cons q (append x (append y z))))
                     (cons q (append (rest x) (append y z)))))
C12. (implies (not (equal (first x) q))
              (equal (del (first x) (cons q (append x (append y z))))
                     (cons q (append (rest x) (append y z)))))
C13. (equal (del (first x) (cons q (append x (append y z))))
            (cons q (append (rest x) (append y z)))) {Or-elim, C10, C11, C12}
C14. (in (first x) (cons q (append x (append y z)))) {in axiom, C2}
C15. (perm (append x (cons q (append y z))) 
           (cons q (append x (append y z)))) {Def perm, C13, C14, C9}
C16. (perm (cons q (append x (append y z)))
           (append x (cons q (append y z)))) {Symmetry of perm, C15}

(perm (cons q (append x (append y z)))
      (append x (cons q (append y z))))
={C16}
t
|#

;;;;;;;;;;;;;;;;;;;;;;;;
;; Induction Scheme generator

:program

(defun lookup (v ls)
  (cond ((endp ls) nil)
        ((equal v (first ls)) 0)
        (t (let ((r (lookup v (rest ls))))
             (if r (+ 1 r) nil)))))

(defun get (i l)
  (cond ((endp l) nil)
        ((equal 0 i) (first l))
        (t (get (- i 1) (rest l)))))

(defun do-subst (conj params args)
  (cond ((endp conj)
         (let ((new (lookup conj params)))
           (if new (get new args) 
             conj)))
        (t (cons (do-subst (first conj) params args)
                 (do-subst (rest conj) params args)))))

(defun subst-all (conj params args)
  (cond ((endp args) nil)
        (t (cons (do-subst conj params (first args))
                 (subst-all conj params (rest args))))))



(defun find-recursions (b name)
  (cond ((atom b) nil)
        ((equal (first b) name) (list (rest b)))
        ((consp (rest b)) 
         (let ((v (find-recursions (first (rest b)) name))
               (vs (find-recursions (cons (first b) (rest (rest b))) name)))
           (if v (app v vs) vs)))))

(defun parse (b n p conj ants)
  (cond ((atom b) (list (list 'implies ants conj)))
        ((equal (first b) 'if)
         (app (parse (first (rest (rest b))) n p conj 
                     (app ants (list (first (rest b)))))
              (parse (first (rest (rest (rest b)))) n p conj 
                     (app ants (list (list 'not (first (rest b))))))))
        ((equal (first b) 'cond)
         (if (endp (rest b)) nil
           (let ((test (first (first (rest b))))
                 (then (first (rest (first (rest b)))))
                 (more (rest (rest b))))
             (app (parse then n p conj 
                         (if (equal test 't)
                           ants
                           (app ants (list test))))
                  (parse (cons 'cond more) n p conj 
                         (app ants (list (list 'not test))))))))
        (t (let ((rec (find-recursions b n)))
             (if rec
               (list (list 'implies 
                           (app ants (subst-all conj p rec))
                           conj))
               (list (list 'implies ants conj)))))))

(defun induction-scheme (e c)
  (let ((name (first (rest e)))
        (params (first (rest (rest e))))
        (input-contr (first (rest (rest (rest (rest e))))))
        (body (first (rest (rest (rest (rest (rest (rest (rest e))))))))))
   (let ((unsat (list 'implies (list 'not input-contr) c)))
     (app (list 'and unsat) (parse body name params c input-contr)))))
(acl2::set-guard-checking :none)
(check= (induction-scheme
               '(defunc app (x y)
                  :input-contract (and (listp x) (listp y))
                  :output-contract (listp (app x y))
                  (if (endp x)
                    y
                    (cons (first x) (app (rest x) y))))
               '(implies (and (listp x) (listp y) (listp z))
                         (equal (app (app x y)) (app x (app y z)))))
              (induction-scheme
               '(defunc app (x y)
                  :input-contract (and (listp x) (listp y))
                  :output-contract (listp (app x y))
                  (cond ((endp x) y)
                        (t (cons (first x) (app (rest x) y)))))
               '(implies (and (listp x) (listp y) (listp z))
                         (equal (app (app x y)) (app x (app y z))))))


(induction-scheme
 '(defunc perm-2 (x y z)
  :input-contract (and (lorp x) (lorp y) (lorp z))
  :output-contract (booleanp (perm-2 x y z))
  (cond ((endp x) (and (endp y) (endp z)))
        ((and (in (first x) y)
              (in (first x) z))
         (perm-2 (rest x)
                 (del (first x) y)
                 (del (first x) z)))
        (t nil)))
 '(implies (and (lorp x) (lorp y) (lorp z) (perm-2 x y z))
           (perm x y)))#|ACL2s-ToDo-Line|#

#|
(induction-scheme 
 '(defunc perm (x y)
    :input-contract (and (lorp x) (lorp y))
    :output-contract (booleanp (perm x y))
    (if (endp x)
      (endp y)
      (and (in (first x) y)
           (perm (rest x) (del (first x) y))))) 
 '(implies (and (lorp x) (lorp y) (perm x y)) (perm y x)))
|#


