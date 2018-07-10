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
#|
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

For this homework you will NOT need to use ACL2s. However, you could
use the Eclipse/ACL2s text editor to write up your solution and
you may want to use ACL2s to help you check your answers.

If you want to use ACL2s, then you can. This is entirely optional and
will require you understand how to steer the theorem prover, which
will require you read some lecture notes that are available on the
class Webpage, but which we will not cover in class and will not be on
the exam. If you still want to try, then if you submit a sequence of
defthms that include conjectures you are asked to prove below, then we
will give you full credit for any such conjectures, but none of the
defthms you submit can use nested induction proofs. You can tell that
a nested induction proof was used by looking at the output of the
theorem prover.  If you see the following:

"*1 is COMPLETED!"

then no nested inductions were performed. If you see something like:

"..., *1.1 and *1 are COMPLETED!"

Then nested inductions were performed. So, at that point you can look
at what *1.1 is, generalize it and submit it as a defthm, which should
allow ACL2s to not have to perform that nested induction.

You can use ACL2s for some of the conjectures and text proofs for the
rest. I do not recommend doing this unless you feel very confident in
doing paper and pencil proofs.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

Technical instructions:
 
- Open this file in ACL2s as hwk9.lisp

- Make sure you are in BEGINNER mode. This is essential! Note that you
  can only change the mode when the session is not running, so set the
  correct mode before starting the session.

- Insert your solutions into this file where indicated (usually as "...")

- Only add to the file. Do not remove or comment out anything
  pre-existing.

- Make sure the entire file is accepted by ACL2s. In particular, there
  must be no "..." left in the code. If you don't finish all problems,
  comment the unfinished ones out. Comments should also be used for
  any English text that you may add. This file already contains many
  comments, so you can see what the syntax is.

- When done, save your file and submit it as hwk9.lisp

- Do not submit the session file (which shows your interaction with
  the theorem prover). This is not part of your solution. Only submit
  the lisp file.

PROGRAMMING INSTRUCTIONS

For each function you define, you must provide a purpose statement
(unless we have provided one for you), contracts (unless we have
provided one for you), a body, check= tests *and* test?
forms (property-based testing).  For each data definition you define,
you must provide a purpose statement, check= tests *and* test?
forms (property-based testing).  This is in addition to the tests
sometimes provided. Make sure you produce sufficiently many new test
cases and at least two interesting test? forms. If we provide a
purpose statement for you, you do not need to provide another one.

For function definitions, make sure to provide as many tests as the
data definitions dictate. For example, a function taking two lists
should have at least 4 tests: all combinations of each list being
empty and non-empty.  Beyond that, the number of tests should reflect
the difficulty of the function. For very simple ones, the above
coverage of the data definition cases may be sufficient. For complex
functions with numerical output, you want to test whether it produces
the correct output on a reasonable number of inputs.

Use good judgment. For example, if you are asked to define a function
with no arguments and we ask you to show the output it generates,
there is no need to add any check= or test? forms. For unreasonably
few test cases and properties we will deduct points. If you have any
questions at all, please ask on Piazza. It is better to be safe that
sorry.

EQUATIONAL REASONING INSTRUCTIONS

The questions on equational reasoning ask for equational proofs about
ACL2s programs. You are given a set of function definitions you can
use.  Note in many cases the name has been slightly changed so you
can't simply use a theorem from class (ex. in2 instead of in).

The definitional axioms and contract theorems for defined functions
can be used in your proofs, unless we specifically prohibit you from
doing so.

You can use ACL2s to check the conjectures you come up with, but you are 
not required to do so. 

Here are some notes about equational proofs although additional
information can be found in the course notes on equational
reasoning. Remember the key consideration when grading your proofs
will be how well you communicate your ideas and justifications.

1. The context. Remember to use propositional logic to rewrite the
context so that it has as many hypotheses as possible.  See the
lecture notes for details. Label the facts in your context with C1,
C2, ... as in the lecture notes.

2. The derived context. Draw a dashed line (----) after the context
and add anything interesting that can be derived from the context.
Use the same labeling scheme as was used in the context. Each derived
fact needs a justification. Again, look at the lecture notes for more
information.

3. Use the proof format shown in class and in the lecture notes, which
requires that you justify each step.

4. When using an axiom, theorem or lemma, show the name of the axiom,
theorem or lemma. Starting with this homework, you do not have to
specify the substitution used.  You can use any "shortcut" we've used
in lab or in the lectures. For example, you do not need to cite the if
axioms when using a definitional axiom.  Look at the lecture notes for
examples.

5. When using the definitional axiom of a function, the justification
should say "Def. <function-name>".  When using the contract theorem of
a function, the justification should say
"Contract <function-name>".

6. Arithmetic facts such as commutativity of addition can be used. The
name for such facts is "Arithmetic" or "Arith".

7. You can refer to the axioms for cons, and consp as the "cons
axioms", Axioms for first and rest can be referred to as "first-rest
axioms".  The axioms for if are named "if axioms"

8. Any propositional reasoning used can be justified by "propositional
reasoning", "Prop logic", or "PL" except you should use "MP" to
explicitly identify when you use modus ponens.

9. For this homework, you can only use theorems we explicitly tell you
you can use or we have covered in class/lab.  You can, of course, use
the definitional axiom and contract theorem for any function used or
defined in this homework. You may also use theorems you've proven
earlier in the homework. 

10. For any given propositional expression, feel free to re-write it
in infix notation. 

For example, you can write A => (B ^ C) instead of (implies A (and B C))) 

The same hold for arithmetic expressions.

For example, you can write xy/2 instead of (/ (* x y) 2)

|#


#|

PROOFS BY INDUCTION 

Prove the following conjectures using induction.  Almost all of these
conjectures will require lemmas. Some of them will require
generalization and some will require exploration and thought so give
yourselves plenty of time.  You can freely use the definitional and
function contract theorems of the functions we provide below or that
we have covered in class. You can also freely use any theorems we
proved in class and in the lecture notes.

Make sure you identify what induction scheme you are using.  For
example, suppose you were proving that app is associative:

(listp x) ^ (listp y) ^ (listp z) =>
(app (app x y) z) = (app x (app y z))

At the beggining of the proof you should say:

Proof by induction using (listp x).

Make sure you understand the algorithm provided in the lecture
notes for generating induction schemes.

For this homework, the goal is to define the beginnings of a verified
library for sorting lists of numbers. We provide you with simple
versions of insert sort and quicksort (functions that we also saw in
the last homework) and you will prove that they satisfy various
properties.

|#

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

; Prove the following

; Q1
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
; Q2
(implies (lorp x)
         (orderedp (qsort x)))

; Helper Functions for lemmas
|#
(defunc less-than-all (x xs)
  :input-contract (and (rationalp x) (lorp xs))
  :output-contract (booleanp (less-than-all x xs))
  (cond ((endp xs) t)
        ((< x (first xs)) (less-than-all x (rest xs)))
        (t nil)))

;; to say that every element of one list is less than or equal to 
;; every element in another
(defunc all-less-than (xs1 xs2)
  :input-contract (and (lorp xs1) (lorp xs2))
  :output-contract (booleanp (all-less-than xs1 xs2))
  (cond ((endp xs1) t)
        ((less-than-all (first xs1) xs2)
         (all-less-than (rest xs1) xs2))
        (t nil)))

(defunc greater-than-all (x xs)
  :input-contract (and (rationalp x) (lorp xs))
  :output-contract (booleanp (greater-than-all x xs))
  (cond ((endp xs) t)
        ((>= x (first xs)) (greater-than-all x (rest xs)))
        (t nil)))

;; to say that every element of one list is greater than 
;; every element in another
(defunc all-greater-than (xs1 xs2)
  :input-contract (and (lorp xs1) (lorp xs2))
  :output-contract (booleanp (all-greater-than xs1 xs2))
  (cond ((endp xs1) t)
        ((greater-than-all (first xs1) xs2)
         (all-greater-than (rest xs1) xs2))
        (t nil)))
#|

Q2:

(implies (lorp x)
         (orderedp (qsort x)))

Lemma 1 for Q2 (L2.0)         
(implies (and (rationalp pivot)
              (lorp ls))
         (less-than-all pivot (notless pivot ls)))

This will be proved using the induction scheme of less-than-all:

1. (implies (or (not (rationalp pivot)) (lorp ls)) L2.0)

Reductio ad absurdum. Done.

2. (implies (and (rationalp pivot) (endp ls)) L2.0)

C1: (rationalp pivot)
C2: (endp ls)
-------------

(implies (and (rationalp pivot)
              (lorp ls))
         (less-than-all pivot (notless pivot ls)))
={MP, C1, C2}
(less-than-all pivot (notless pivot ls))
={Def notless, C1, C2}
(less-than-all pivot nil)
={Def less-than-all, C1}
t
         
3. (implies (and (rationalp pivot) (lorp ls) (consp ls) (< pivot (first ls))
                 (L2.0 | ((pivot pivot) (ls (rest ls))))) L2.0)

C1: (rationalp pivot)
C2: (lorp ls)
C3: (consp ls)
C4: (< pivot (first ls))
C5: (implies (and (rationalp pivot)
                  (lorp (rest ls)))
             (less-than-all pivot (notless pivot (rest ls))))
----------------
C6: (lorp (rest ls)) {Def lorp, C2, C3}
C7: (less-than-all pivot (notless pivot (rest ls))) {MP, C5, C1, C6}

(implies (and (rationalp pivot)
              (lorp ls))
         (less-than-all pivot (notless pivot ls)))
={MP, C1, C2}
(less-than-all pivot (notless pivot ls))
={Def notless, C1, C2, C4}
(less-than-all pivot (notless pivot (rest lst)))
={C7}
t

4. (implies (and (rationalp pivot) (lorp ls) (consp ls) (not (< pivot (first ls)))
                 (L2.0 | ((pivot pivot) (ls (rest ls)))))
            L2.0)

C1: (rationalp pivot)
C2: (lorp ls)
C3: (consp ls)
C4: (not (< pivot (first ls)))
C5: (implies (and (rationalp pivot)
                  (lorp (rest ls)))
             (less-than-all pivot (notless pivot (rest ls))))
-----------------------------
C6: (lorp (rest ls)) {Def lorp, C2, C3}
C8: (lorp (notless pivot (rest ls))) {Contract thm, notless, C1, C5}
C9: (less-than-all pivot (notless pivot (rest ls))) {MP, C5, C1, C6}

(implies (and (rationalp pivot)
              (lorp ls))
         (less-than-all pivot (notless pivot ls)))
= {C1, C2}
(less-than-all pivot (notless pivot ls))
={Def notless, C1, C3, C7}
(less-than-all pivot (cons (first ls) (notless pivot (rest ls))))
={Def less-than-all, C1, C7, C4, C8}
(less-than-all pivot (notless pivot (rest ls)))
= {C9}
t
   
Lemma 1 for Q2 (L2.1)
L2.1: (implies (and (rationalp pivot) 
                    (lorp ls) 
                    (consp ls) 
                    (less-than-all pivot ls))
               (< pivot (first ls)))

Obligations:
1. (implies (or (not (rationalp pivot))
                (not (lorp ls))
                (not (consp ls))
                (not (less-than-all pivot ls)))
            L2.1)

MP -> (implies nil (< pivot (first ls))) -> t

2. (implies (and (rationalp pivot)
                 (lorp ls)
                 (endp ls)
                 (less-than-all pivot ls))
            L2.1)
MP -> (implies nil (< pivot (first ls))) -> t

3. (implies (and (rationalp pivot)
                 (lorp ls)
                 (consp ls)
                 (< pivot (first ls))
                 (L2.1 | ((pivot pivot) (ls (rest ls)))))
            L2.1)
C1: (rationalp pivot)
C2: (lorp ls)
C3: (consp ls)
C4: (< pivot (first ls))
C5: (less-than-all pivot ls)
C6: (implies (and (rationalp pivot) (lorp (rest ls)) (consp (rest ls)) (less-than-all pivot (rest ls)))
                  (< pivot (first (rest ls))))
----------------------

(implies (and (rationalp pivot) (lorp ls) (consp ls) (less-than-all pivot ls))
         (< pivot (first ls)))
= {MP, C1, C2, C3, C5}
(< pivot (first ls))
= {C4}
t

Lemma 2 for L2 (L2.2)
L1: (implies (and (rationalp pivot)
                  (lorp ls))
             (greater-than-all pivot (less pivot ls)))

Essentially the same proof as L2.1.

Lemma 3 for Q2 (L2.3)

(implies (and (lorp x)
              (lorp y)
              (rationalp z)
              (orderedp x)
              (orderedp y)
              (greater-than-all z x)
              (less-than-all z y))
         (orderedp (append x (cons z y))))
           
This will be proven using the induction scheme of orderedp.

Proof obligations:

1. (implies (not (and (lorp x) (lorp y) (orderedp x) (orderedp y)
                      (greater-than-all z x) (less-than-all z y)))
            L2.3)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (lorp y) (orderedp x) (orderedp y)
                 (greater-than-all z x) (less-than-all z y)
                 (endp x))
             L2.3)
C1. (lorp x)
C2. (lorp y)
C3. (orderedp x)
C4. (orderedp y)
C5. (greater-than-all z x)
C6. (less-than-all z y)
C7. (endp x)
-----------
C8. (or (endp y) (and (consp y) (lorp (rest y)))) {Def lorp, C2}
C9. (implies (endp y) (orderedp (cons z y))) {Def orderedp}
C10. (implies (consp y) (< z (first y))) {Def less-than-all, C6}
C11. (implies (and (< z (first y)) (orderedp y)) (orderedp (cons z y))) {Def orderedp, C4}
C12: (implies (consp y) (orderedp (cons z y))) {MP, C10, C11, C4}
C13: (orderedp (cons z y)) {Or-elim, C8, C9, C12}

(implies (and (lorp x)
              (lorp y)
              (rationalp z)
              (orderedp x)
              (orderedp y)
              (greater-than-all z x)
              (less-than-all z y))
         (orderedp (append x (cons z y))))
={MP, C1, C2, C3, C4, C5, C6}
(orderedp (append x (cons z y)))
={Def append, C7}
(orderedp (cons z y))
={C13}
t

3. (implies (and (lorp x) (lorp y) (orderedp x) (orderedp y)
                 (greater-than-all z x) (less-than-all z y)
                 (consp x)
                 (L2.3 | (x (rest x))))
             L2.3)

C1. (lorp x)
C2. (lorp y)
C3. (orderedp x)
C4. (orderedp y)
C5. (greater-than-all z x)
C6. (less-than-all z y)
C7. (consp x)
C8. (implies (and (lorp (rest x))
                  (lorp y)
                  (rationalp z)
                  (orderedp (rest x))
                  (orderedp y)
                  (greater-than-all z (rest x))
                  (less-than-all z y))
             (orderedp (append (rest x) (cons z y))))
-----------   
C9. (lorp (rest x)) {Def lorp, C1, C7}
C10. (orderedp (rest x)) {Def orderedp, C3, C7}
C11. (greater-than-all z (rest x)) {Def greater-than-all C5, C7}
C12. (orderedp (append (rest x) (cons z y))) {MP, C8, C9, C2, C10, C4, C11, C6}
C13. (lorp (append (rest x) (cons z y))) {Contract thm append, C7, C2}
C14. (or (endp (append (rest x) (cons z y)))
         (and (consp (append (rest x) (cons z y))) (lorp (rest (append (rest x) (cons z y)))))) {Def lorp, C13}
C15. (implies (endp (append (rest x) (cons z y))) (orderedp (cons (first x) (append (rest x) (cons z y)))))
     {Def orderedp, C7}
C16. (or (endp (rest x)) (and (consp (rest x)) (lorp (rest x)))) {Def lorp, C9}
C17. (implies (consp (rest x)) (< (first x) (first (rest x)))) {Def orderedp, C3}
C18. (< (first x) z) {Def greater-than-all, C5, C7}
C20. (implies (endp (rest x)) (orderedp (cons (first x) (append (rest x) (cons z y))))) {C18, C12}
C21. (implies (consp (rest x)) (orderedp (cons (first x) (append (rest x) (cons z y))))) {C17, C12}
C22. (orderedp (cons (first x) (append (rest x) (cons z y)))) {Or-elim, C14, C20, C21}

(implies (and (lorp x)
              (lorp y)
              (rationalp z)
              (orderedp x)
              (orderedp y)
              (greater-than-all z x)
              (less-than-all z y))
         (orderedp (append x (cons z y))))
={MP, C1, C2, C3, C4, C5, C6}
(orderedp (append x (cons z y)))
={Def append, C7}
(orderedp (cons (first x) (append (rest x) (cons z y))))
={C22}
t

Lemma 4 for Q2 (L2.4):

(implies (and (lorp x)
              (lorp y)
              (rationalp z)
              (perm y x)
              (less-than-all z x))
         (less-than-all z y))

Lemma for L2.4 (L2.4.1)

(implies (and (lorp x)
              (rationalp z)
              (rationalp y)
              (in z x)
              (less-than-all y x))
          (>= z y))

This will be proven using the induction scheme of in.

Proof obligations:

1. (implies (not (and (lorp x) (rationalp z) (rationalp y)
                      (in z x) (less-than-all y x))) L2.4.1)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (rationalp z) (rationalp y)
                 (in z x) (less-than-all y x)
                 (endp x)) L2.4.1)
Reductio ad absurdum. Done.

3. (implies (and (lorp x) (rationalp z) (rationalp y)
                 (in z x) (less-than-all y x)
                 (consp x) (not (equal (first x) z)) (L2.4.1 | (x (rest x)))) L2.4.1) 

C1. (lorp x)
C2. (rationalp z)
C3. (rationalp y)
C4. (in z x)
C5. (less-than-all y x)
C6. (consp x)
C7. (not (equal (first x) z))
C8. (implies (and (lorp (rest x)) (rationalp y) (rationalp z) (in z (rest x)) (less-than-all y (rest x))) (>= z y))
------------------
C9. (and (rationalp (first x)) (lorp (rest x))) {Def lorp, C1, C6}
C10. (in z (rest x)) {Def in, C4, C6, C7}
C11. (less-than-all y (rest x)) {Def less-than-all C5, C6}
C12. (>= z y) {MP, C8, C9, C2, C3, C10, C11}

(implies (and (lorp x)
              (rationalp z)
              (rationalp y)
              (in z x)
              (less-than-all y x))
          (>= z y))
={MP, C1, C2, C3, C4, C5}
(>= z y)
={C12}
t

Thus, L2.4.1 has been proven.

Now, L2.4         
This will be proven using the induction scheme of perm.

Proof obligations:

1. (implies (not (and (lorp x) (lorp y) (rationalp z)
                      (perm y x) (less-than-all z x))) L2.4)
Reductio ad absurdum. Done.


2. (implies (and (lorp x) (lorp y) (rationalp z)
                 (perm y x) (less-than-all z x)
                 (endp x))
             L2.4)
C1. (lorp x)
C2. (lorp y)
C3. (rationalp z)
C4. (perm y x)
C5. (less-than-all z x)
C6. (endp x)
--------------
C7. (endp y) {Def perm, C4, C6}
C8. (less-than-all z y) {Def less-than-all, C7}

(implies (and (lorp x)
              (lorp y)
              (rationalp z)
              (perm y x)
              (less-than-all z x))
         (less-than-all z y))
={MP, C1, C2, C3, C4, C5}
(less-than-all z y)
={C8}
t

3. (implies (and (lorp x) (lorp y) (rationalp z)
                 (perm y x) (less-than-all z x)
                 (consp y)
                 (L2.4 | (x (del (first y) x)) (y (rest y))))
             L2.4)

C1. (lorp x)
C2. (lorp y)
C3. (rationalp z)
C4. (perm y x)
C5. (less-than-all z x)
C6. (consp y)
C7. (implies (and (lorp (del (first y) x)) (lorp (rest y)) (rationalp z) 
                  (perm (rest y) (del (first y) x)) (less-than-all z (del (first y) x)))
             (less-than-all z (rest y)))
--------------             
C8. (and (rationalp (first y)) (lorp (rest y))) {Def lorp, C1, C6}
C9. (lorp (del (first y) x)) {Contract thm del, C8, C1}
C10. (and (in (first y) x) (perm (rest y) (del (first y) x))) {Def perm, C4, C6}
C11. (consp x) {in axiom, C10}
C12. (less-than-all z (rest x)) {Def less-than-all C5, C11}
C13. (less-than-all z (rest y)) {MP, C7, C8, C9, C3, C10, C12}
C14. (< (first y) z) {L2.4.1, C10, C5}

(implies (and (lorp x)
              (lorp y)
              (rationalp z)
              (perm x y)
              (less-than-all z x))
         (less-than-all z y))
={MP, C1, C2, C3, C4, C5}
(less-than-all z y)
={Def less-than-all, C6, C14}
(less-than-all z (rest y))
={C13}
t

Thus, L2.4 is proven.          

Last lemma for Q2 (L2.5)

(implies (and (lorp x)
              (lorp y)
              (rationalp z)
              (perm y x)
              (greater-than-all z x))
         (greater-than-all z y))

This is essentially the same proof as L2.4.


Now, Q2:  
(implies (lorp x)
         (orderedp (qsort x)))
This will be proven using the induction scheme of qsort.

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
C9. (orderedp (qsort (less (first x) (rest x)))) {MP, C4, C7}
C10. (lorp (qsort (less (first x) (rest x)))) {Contract thm, qsort, C6}
C11. (lorp (qsort (notless (first x) (rest x)))) {Contract thm, qsort, C7}
C12. (greater-than-all (first x) (less (first x) (rest x))) {L2.1, C5}
C13. (less-than-all (first x) (notless (first x) (rest x))) {L2.2, C5}
C14. (perm (less (first x) (rest x))) (qsort (less (first x) (rest x))) {Q8, C6}
C15. (perm (notless (first x) (rest x))) (qsort (notless (first x) (rest x))) {Q8, C7}
C16. (greater-than-all (first x) (qsort (less (first x) (rest x)))) {L2.5, C12, C14}
C17. (less-than-all (first x) (qsort (notless (first x) (rest x)))) {L2.4, C13, C15}



(implies (lorp x) (orderedp (qsort x)))
={MP, C1}
(orderedp (qsort x))
={Def qsort, C2}
(orderedp (append (qsort (less (first x) (rest x)))
                  (append (list (first x)) 
                          (qsort (less (first x) (rest x))))))
={L2.3, C5, C10, C11, C8, C9, C16, C17}
t

Thus, Q2 has been proven.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


Q3:
(implies (and (lorp x) (lorp y) (perm x y))
         (equal (len x) (len y)))
         
Lemma for Q3 (L3): 
  (implies (and (listp x) (consp x) (in y x))
           (equal (len (rest x)) (len (del y x))))

This will be proven using the inductions scheme of del.
Proof obligations:

1. (implies (or (not (listp x)) (not (consp x)) (not (in y x))) L3)

C1: (or (not (listp x)) (not (consp x)) (not (in y x)))
-------

L3 
= {MP, C1}
(implies nil (equal (len (rest x)) (len (del y x)))
= {PL}
t

2. (implies (and (listp x) (consp x) 
                 (equal y (first x)) (in y x)) L3)
                 
C1. (listp x)
C2. (consp x)
C3. (equal y (first x))
C4. (in y x)
-------------
 
(implies (and (listp x) (consp x) (in y x))
         (equal (len (rest x)) (len (del y x))))
={MP, C1, C2, C4}
(equal (len (rest x)) (len (del y x)))
={Def del, C2, C3}
(equal (len (rest x)) (len (rest x)))
={equal axiom}
t

3. (implies (and (listp x) (consp x) (not (equal y (first x))) (in y x)
                 (L3 | ((x (rest x)) (y y)))) L3)

C1: (listp x)
C2: (consp x)
C3: (not (equal y (first x)))
C4: (in y x)
C5: (implies (and (listp (rest x)) (consp (rest x)) (in y (rest x))
                  (equal (len (rest (rest x))) (del y (rest x)))))
--------------
C6: (in y (rest x)) {Def in, C2, C3}
C7: (consp (rest x)) {Def in, C6}
C8: (listp (rest x)) (Def listp, C1, C7}
C9: (equal (len (rest (rest x)) (del y (rest x)))) {MP, C5, C8, C7, C6}

(implies (and (listp x) (consp x) (in y x))
         (equal (len (rest x)) (len (del y x))))
={MP, C1, C2, C4}
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

Thus the lemma L3 is finished.


; Now, Q3
(implies (and (lorp x) (lorp y) (perm x y))
         (equal (len x) (len y)))

;; This will be proven using the induction scheme of perm.

Proof obligations:

1. (implies (or (not (lorp x)) (not (lorp y)) (not (perm x y))) Q3)

Finished by a quick reductio ad absurdum.

2. (implies (and (lorp x) (lorp y) (perm x y)
                 (endp x))
            Q3)

C1: (lorp x)
C2: (lorp y)
C3: (perm x y)
C4: (endp x)
-------------
C5: (endp y) {Def perm, C3, C4}

(implies (and (lorp x) (lorp y) (perm x y))
         (equal (len x) (len y)))
={MP, C1, C2, C3}
(equal (len x) (len y))
={C4, C5}
(equal 0 0)
={equal axiom}
t


3. (implies (and (lorp x) (lorp y) (perm x y)
                 (not (endp x)) 
                 (in (first x) y) 
                 (Q3 | ((x (rest x)) (y (del (first x) y)))))
            Q3)

C1: (lorp x)
C2: (lorp y)
C3: (perm x y)
C4: (not (endp x))
C5: (in (first x) y)
C6: (implies (and (lorp (rest x)) 
                  (lorp (del (first (rest x)) y)) 
                  (perm (rest x) (del (first x) y)))
             (equal (len (rest x)) 
                    (len (del (first (rest x)) y))))
--------------------------------
C7: (and (consp x) (lorp (rest x))) {Def lorp, C1, C4}
C8: (lorp (del (first (rest x)) y)) {Contract thm, C2}
C9: (perm (rest x) (del (first x) y)) {Def perm, C3, C4, C5}
C10: (equal (len (rest x)) (len (del (first (rest x)) y))) {MP, C6, C7, C8, C9}
C11: (consp y) {in axiom, C5}
C12: (equal (len (rest y))
            (len (del (first (rest x)) y))) {L3, C2, C11, C5}

(implies (and (lorp x) (lorp y) (perm x y))
         (equal (len x) (len y)))
={MP, C1, C2, C3}
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Q4
(implies (lorp x)
         (perm x x))

This will be proven using the inductive scheme of perm

Proof obligations:
1. (implies (not (lorp x)) Q4)

Reductio ad absurdum. Done.

2. (implies (and (lorp x) (endp x)) Q4)

C1. (lorp x)
C2. (endp x)
------------

(implies (lorp x) (perm x x))
={MP, C1}
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
Q5:

(implies (and (lorp x) (lorp y) (perm x y))
         (perm y x))
         
         
First Lemma for Q5 (L5.1):

(implies (and (listp x) (listp y) (consp y) (perm x y))
         (in (first y) x))
         
This will be proven using the induction scheme of perm:

Proof obligations:
1. (implies (or (not (listp x)) (not (listp y)) (not (consp y)) (not (perm x y)))
            L5.1)
Reductio ad absurdum. Done.

2. (implies (and (listp x) (listp y) (consp y) (perm x y)
                 (endp x))
            L5.1)
            
C1. (listp x)
C2. (listp y)
C3. (consp y)
C4. (perm x y)
C5. (endp x)
-------------------
C6. (endp y) {Def perm, C5}
C7. False {C3, C6}
C8. L5.1 {Reductio ad absurdum, C7}

L5.1
={C8}
t
            
3. (implies (and (listp x) (listp y) (consp y) (perm x y)
                 (consp x))
            L5.1)
C1. (listp x)
C2. (listp y)
C3. (consp y)
C4. (perm x y)
C5. (consp x)
-------------------
C6. (and (in (first x) y) (perm (rest x) (del (first x) y))) {Def perm, C4, C5}


(implies (and (listp x) (listp y) (consp y) (perm x y))
         (in (first y) x))
={MP, C1, C2, C3, C4}
(in (first y) x)
={C6}
t

Second Lemma for Q5 (L5.2):

(implies (and (lorp x) (lorp y) (rationalp z)
              (in z x) (in z y) (perm x y))
              (perm (del z x) (del z y)))

This will be proven using the induction scheme of (del z x) and (perm x y)

1. (implies (not (and (lorp x) (lorp y) (rationalp z)
                 (in z x) (in z y) (perm x y)))
            L5.2)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (lorp y) (rationalp z)
                 (in z x) (in z y) (perm x y) (endp x))
            L5.2)
Reductio ad absurdum (because z is in nil). Done.

3. (implies (and (lorp x) (lorp y) (rationalp z)
                 (in z x) (in z y) (perm x y) (not (endp x))
                 (equal (first x) z))
            L5.2)
C1. (lorp x)
C2. (lorp y)
C3. (rationalp z)
C4. (in z x)
C5. (in z y)
C6. (perm x y)
C7. (not (endp x))
C8. (equal (first x) z)
--------------------

(implies (and (lorp x) (lorp y) (rationalp z)
              (in z x) (in z y) (perm x y))
              (perm (del z x) (del z y)))
={MP, C1 - 6}
(perm (del z x) (del z y))
={Def del, C7, C8}
(perm (rest x) (del z y))
={C8}
(perm (rest x) (del (first x) y))
={Def perm, C6, C7}
t

4. (implies (and (lorp x) (lorp y) (rationalp z)
                 (in z x) (in z y) (perm x y) (not (endp x))
                 (not (equal (first x) z))
                 (L5.2 | ((x (rest x)) (y (del (first x) y)))))
            L5.2)
C1. (lorp x)
C2. (lorp y)
C3. (rationalp z)
C4. (in z x)
C5. (in z y)
C6. (perm x y)
C7. (not (endp x))
C8. (not (equal (first x) z))
C9. (implies (and (lorp (rest x)) (lorp (del (first x) y)) (rationalp z)
             (in z (rest x)) (in z (del (first x) y)) (perm (rest x) (del (first x) y)))
             (perm (del z (rest x)) (del z (del (first x) y))))
--------------------            
C10. (and (rationalp (first x)) (lorp (rest x))) {Def lorp, C1, C7}
C11. (lorp (del (first x) y)) {Contract thm, C10, C2}
C12. (in z (rest x)) {Def in, C4, C7, C8}
C13. (in z (del (first x) y)) {L6 (proven below), C6, C12}
C14. (perm (rest x) (del (first x) y)) {Def perm, C6, C7}
C15. (perm (del z (rest x)) (del z (del (first x) y))) {MP, C9, C10, C11, C12, C13, C14}
C16. (equal (del z (del (first x) y)) (del (first x) (del z y))) {L5.3, C2, C3, C10}
C17. (perm (del z (rest x)) (del (first x) (del z y))) {Transitivity of perm, C15, C16}
C18. (perm (cons (first x) (del z (rest x))) (del z y)) {Def perm, C17}

(implies (and (lorp x) (lorp y) (rationalp z)
              (in z x) (in z y) (perm x y))
              (perm (del z x) (del z y)))
={MP, C1 - 6}
(perm (del z x) (del z y))
={Def del, C7, C8}
(perm (cons (first x) (del z (rest x))) (del z y))
={C18}
t

Third Lemma for Q5 (L5.3)

(implies (and (lorp x) (rationalp y) (rationalp z))
         (equal (del y (del z x)) (del z (del y x))))
         
This will be proven using the induction schemes from (del y x) and (del z x).


1. (implies (not (and (lorp x) (rationalp y) (rationalp z)))
            L5.3)
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
            
3. (implies (and (lorp x) (rationalp y) (rationalp z) (not (endp x))
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

Now, Q5:
This will be proven using the induction scheme of (perm x y)

1. (implies (not (and (lorp x) (lorp y) (perm x y))) Q5)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (lorp y) (perm x y) (endp y)) Q5)

C1. (lorp x)
C2. (lorp y)
C3. (perm x y)
C4. (endp y)
--------------
C5. (endp x) {Q3, C4, C3}

(implies (and (lorp x) (lorp y) (perm x y)) (perm y x))
={MP, C1, C2, C3}
(perm y x)
={C4}
(endp x)
={C5}
t

3. (implies (and (lorp x) (lorp y) (perm x y) (not (endp y))
                 (Q5 | ((y (rest y)) (x (del (first y) x)))))
            Q5)
            
C1. (lorp x)
C2. (lorp y)
C3. (perm x y)
C4. (not (endp y))
C5. (implies (and (lorp (del (first y) x)) (lorp (rest y)) 
                  (perm (del (first y) x) (rest y)))
             (perm (rest y) (del (first y) x)))
----------------------
C6. (not (endp x)) {Q3, C3, C4}
C7. (in (first y) x) {L5.1, C1, C2, C3, C5}
C8. (equal (del (first y) y) (rest y)) {Def del, C4}
C9. (perm (del (first y) x) (del (first y) (cons (first y) (rest y)))) {L5.2, C3, C7}
C10. (perm (del (first y) x) (rest y)) {C9, C8}
C11. (and (rationalp (first y)) (lorp (rest y)))
C12. (lorp (del (first y) x)) {Contract thm, del, C1, C11}
C13. (perm (rest y) (del (first y) x)) {MP, C12, C11, C5}
C14. (perm y x) {Def perm, C13, C7, C6}

(implies (and (lorp x) (lorp y) (perm x y)) (perm y x))
={MP, C1, C2, C3}
(perm y x)
={C14}
t

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
|#
(defunc ind-L6 (x y z)
  :input-contract (and (lorp x) (lorp y))
  :output-contract (booleanp (ind-L6 x y z))
  (cond ((endp x) (endp y))
        ((equal (first x) z) (in z y))
        (t (ind-L6 (rest x) (del (first x) y) z))))#|ACL2s-ToDo-Line|#

#|
Lemma for Q6 (L6):

(implies (and (lorp x) (lorp y) (perm x y) (in z x)) (in z y))

This will be done using the induction scheme of (ind-L6 x y z):

Proof obligations:

1. (implies (and (not (lorp x)) (not (lorp y))) 
            L6)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (lorp y) (endp x)) 
            L6)
Reductio ad absurdum. Done.

3. (implies (and (lorp x) (not (endp x)) (lorp y) (equal (first x) z)) L6)

C1. (lorp x)
C2. (not (endp x))
C3. (equal (first x) z)
C4. (lorp y)
C5. (perm x y)
C6. (in z x)
-------------
C7. (and (in (first x) y) (perm (rest x) (del (first x) y))) {Def perm, C5, C2}

(in z y)
={C3}
(in (first x) y)
={C7}
t

4. (implies (and (lorp x) (not (endp x)) (not (equal (first x) z))
                 (L6 | ((x (rest x)) (y (del (first x) y))))) L6)

C1. (lorp x)
C2. (not (endp x))
C3. (not (equal (first x) z))
C4. (implies (and (lorp (rest x)) (lorp (del (first x) y)) (in z (rest x)))
             (in z (del (first x) y)))
C5. (lorp y)
C6. (perm x y)
C7. (in z x)
-------------
C7. (and (rationalp (first x)) (lorp (rest x))) {Def lorp, C1, C2}
C8. (lorp (del (first x) y)) {Contract thm, del, C5, C7}
C9. (in z (rest x)) {Def in, C7, C2, C3}
C10. (in z (del (first x) y)) {MP, C4, C7, C8, C9}
C11. (in z y) {L6.1, C3, C7, C10} (proven below)

(in z y)
={C11}
t

Lemma for L6 (L6.1)

(implies (and (lorp y) (rationalp x) (not (equal x z)) (in z (del x y)))
         (in z y))
         
This will be proven using the induction scheme of (in z y)

Obligations:

1. (implies (not (lorp y))
            L6)
Reductio ad absurdum. Done.

2. (implies (and (lorp y) (endp y)) L6)
Reductio ad absurdum. Done.

3. (implies (and (lorp y) (not (endp y)) (equal (first y) z)) L6)

C1. (lorp y)
C2. (not (endp y))
C3. (equal (first y) z)
C4. (in z (del x y))
C5. (not (equal x z))
-----------------
C6. (in z y) {Def in, C1, C3}

(in z y)
={C6}
t

4. (implies (and (lorp y) (not (endp y)) (not (equal (first y) z))
                 (L6 | (y (rest y)))) 
            L6)
            
C1. (lorp y)
C2. (not (endp y))
C3. (not (equal (first y) z))
C4. (implies (and (lorp (rest y)) (rationalp x) (in z (del x (rest y))))
             (in z (rest y)))
C5. (in z (del x y))
C6. (not (equal x z))
C7. (rationalp x)
-----------------
C8. (lorp (rest y)) {Def lorp, C1, C2}
C9. (or (equal (first y) x) (not (equal (first y) x))) {PL}
C10. (implies (equal (first y) x)
             (equal (del x y) (rest y))) {Def del}
C11. (implies (equal (first y) x)
              (in z (rest y))) {C10, C5}
C12. (implies (not (equal (first y) x))
              (equal (del x y) (cons (first y) (del x (rest y)))))
     {Def del, C2, C3}
C13. (implies (not (equal (first y) x))
              (in z (cons (first y) (del x (rest y)))) {C5, C13}
C14. (implies (not (equal (first y) x))
              (in z (del x (rest y)))) {Def del, C13, C3}
C15. (implies (not (equal (first y) x))
              (in z (rest y))) {MP, C4, C7, C8, C14}
C16. (in z (rest y)) {Or-elim, C9, C11, C15}
C17. (in z y) {Def in, C3, C16}

(in z y)
={C17}
t

Thus, L6.1 and L6 have been proven
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
; Now, Q6
(implies (and (lorp x) (lorp y) (lorp z) (perm x y) (perm y z))
         (perm x z))
         
Obligations, using the induction scheme of (perm-2 x y z):


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
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Q7
(implies (lorp x)
         (perm (isort x) x))
         
Lemma for Q7 (L7.1):

(implies (lorp x) (in z (insert z x)))

This will be done using the induction scheme of insert

Proof obligations:

1. (implies (not (lorp x)) L7.1)
Reductio ad absurdum. done.

2. (implies (and (lorp x) (endp x)) L7.1)

C1. (lorp x)
C1. (endp x)
------------

(implies (lorp x) (in z (insert z x)))
={MP, C1}
(in z (insert z x))
={Def insert, C2}
(in z (list z))
={equal axiom}
(in z (cons z nil))
={Def in}
t

3. (implies (and (lorp x) (consp x) (<= z (first x))) L7.1)

C1. (lorp x)
C2. (consp x)
C3. (<= z (first x))
------------------

(implies (lorp x) (in z (insert z x)))
={MP, C1}
(in z (insert z x))
={Def insert, C2, C3}
(in z (cons z x))
={Def in}
t

4. (implies (and (lorp x) (consp x) (> z (first x)) (L7.1 | (x (rest x)))) L7.1)

C1. (lorp x)
C2. (consp x)
C3. (> z (first x))
C4. (implies (lorp (rest x)) (in z (insert z (rest x))))
----------------------------
C5. (lorp (rest x)) {Def lorp, C1, C2}
C6. (in z (insert z (rest x))) {MP, C4, C5}

(implies (lorp x) (in z (insert z x)))
={MP, C1}
(in z (insert z x))
={Def insert, C2, C3}
(in z (cons (first x) (insert z (rest x))))
={Def in, C2, C3}
(in z (insert z (rest x)))
={C6}
t

Second Lemma for Q7 (L7.2):

(implies (lorp x) (equal x (del z (insert z x))))

This will be proven using the induction scheme of insert

Proof obligations:

1. (implies (not (lorp x)) Q7)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (endp x)) Q7)

C1. (lorp x)
C2. (endp x)
------------

(implies (lorp x) (equal x (del z (insert z x))))
={MP, C1}
(equal x (del z (insert z x)))
={def insert, C2}
(equal x (del z (list z)))
={def del}
(equal x ())
={C2, C3}
t

3. (implies (and (lorp x) (consp x) (<= z (first x))) Q7)

C1. (lorp x)
C2. (consp x)
C3. (<= z (first x))
-----------------------

(implies (lorp x) (equal x (del z (insert z x))))
={MP, C1}
(equal x (del z (insert z x)))
={Def insert, C2, C3}
(equal x (del z (cons z x)))
={Def del}
(equal x x)
={equal axiom}
t

4. (implies (and (lorp x) (consp x) (> z (first x)) (Q7 | ((x (rest x))))) Q7)

C1. (lorp x)
C2. (consp x)
C3. (> z (first x))
C4. (implies (lorp (rest x)) (equal (rest x) (del z (insert z (rest x)))))
-----------------------
C5. (lorp (rest x)) {Def lorp, C1, C2}
C6. (equal (rest x) (del z (insert z (rest x)))) {MP, C4, C5}


(implies (lorp x) (equal x (del z (insert z x))))
={MP, C1}
(equal x (del z (insert z x)))
={Def insert, C2, C3}
(equal x (del z (cons (first x) (insert z (rest x)))))
={Def del, C2, C3}
(equal x (cons (first x) (del z (insert z (rest x)))))
={C6}
(equal x (cons (first x) (rest x)))
={cons axiom, C2}
t

Q7 will be proven using the induction scheme of perm

Proof obligations:

1. (implies (not (lorp x)) Q7)
Reductio ad absurdum. done.

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

Thus, Q7 has been proven.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Q8
(implies (lorp x) (perm (qsort x) x))

First Lemma for Q8 (L8.1):
(implies (and (lorp x)
              (lorp y)
              (lorp z)
              (perm x y))
         (perm (append x z) (append y z)))

This will be proven using the induction scheme for perm.

1. (implies (not (and (lorp x) (lorp y) (lorp z) (perm x y))) L8.1)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (lorp y) (lorp z) (perm x y) (endp (append x z)))
            L8.1)
C1. (lorp x)
C2. (lorp y)
C3. (lorp z)
C4. (perm x y)
C5. (endp (append x z))
-----------------------
C6. (endp x) {append axiom, C5}
C7. (endp z) {append axiom, C5}
C8. (endp y) {Def perm, C6}
C9. (endp (append y z)) {Def append, C7, C8}
C10. (perm (append x z) (append y z))

(implies (and (lorp x) (lorp y) (lorp z) (perm x y))
         (perm (append x z) (append y z)))
={MP, C1, C2, C3, C4}
(perm (append x z) (append y z))
={C10}
t

2. (implies (and (lorp x) (lorp y) (lorp z) (perm x y) 
                 (consp (append x z)) 
                 (in (first (append x z)) (append y z))
                 (L8.1 | ((append x z) (rest (append x z))) ((append y z) (del (first (append x z)) (append y z)))))
            L8.1)

C1. (lorp x)
C2. (lorp y)
C3. (lorp z)
C4. (perm x y)
C5. (consp (append x z))
C6. (in (first (append x z)) (append y z))
C7. (implies (and (lorp x) (lorp y) (lorp z) (perm x y)) 
                  (perm (rest (append x z)) (del (first (append x z)) (append y z))))
---------------
C8. (perm (rest (append x z)) (del (first (append x z)) (append y z))) {MP, C7, C1, C2, C3, C4}

(implies (and (lorp x) (lorp y) (lorp z) (perm x y)) (perm (append x z) (append y z)))
={MP, C1, C2, C3, C4}
(perm (append x z) (append y z))
={Def perm, C5, C6}
(perm (rest (append x z)) (del (first (append x z)) (append y z)))
={C8}
t
     
Thus, L8.1 has been proven


Second Lemma for Q8 (L8.2):
(implies (and (lorp x)
              (lorp y)
              (lorp z)
              (perm x y))
         (perm (append z x) (append z y)))

This will amount to essentially the same proof as L8.1.

Third Lemma for Q8 (L8.3):
(implies (and (lorp x) (rationalp z))
         (perm (append (less z x) (notless z x)) x))

         
Fourth Lemma for Q8 (L8.4):
(implies (and (lorp x) (lorp y) (lorp z) (lorp w) 
              (perm (append x (append y z)) w))
         (perm (append y (append x z)) w))
         
Now, Q8:         
This will be proven using the induction scheme of qsort.

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
                 (Q8 | (x (notless (first x) (rest x))))) Q8)

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
                           (qsort (notless (first x) (rest x)))))) {L8.2}
C14. (perm (append (less (first x) (rest x))
                   (notless (first x) (rest x)))
           (rest x)) {L8.3}
C13. (perm (append (list (first x))
                   (append (less (first x) (rest x))
                           (notless (first x) (rest x))))
           x) {Def append, perm, C2, C14}
C14. (perm (append (less (first x) (rest x))
                   (append (list (first x))
                           (notless (first x) (rest x))))
           x) {L8.4, C13}
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

Thus, Q8 is proven.

;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;

; Q9 (extra credit) -- not done, but it's close.
(implies (lorp x) (equal (qsort x) (isort x)))

Lemma for Q9 (L9.1)

(implies (and (lorp x)
              (lorp y)
              (orderedp x)
              (orderedp y)
              (perm x y))
          (equal x y))

Lemma for L9.1.2 (L9.1.1)
(implies (and (lorp x)
              (rationalp y)
              (orderedp x))
         (orderedp (del y x)))
         
This will be proven using the induction scheme of (orderedp x)

1. (implies (not (and (lorp x) (rationalp y) (orderedp x))) L9.1.1)

Reductio ad absurdum. Done.

2. (implies (and (lorp x) (rationalp y) (orderedp x) (endp x)) L9.1.1)

C1. (lorp x)
C2. (rationalp y)
C3. (orderedp x)
C4. (endp x)
-------------
C5. (endp (del y x)) {Def del, C1, C2, C4}

(implies (and (lorp x) (rationalp y) (orderedp x)) (orderedp (del y x)))
={MP, C1, C2, C3}
(orderedp (del y x))
={C5}
t

3. (implies (and (lorp x) (rationalp y) (orderedp x) (not (endp x))
                 (endp (rest x))) L9.1.1)

C1. (lorp x)
C2. (rationalp y)
C3. (orderedp x)
C4. (not (endp x))
C5. (endp (rest x))
-------------     
C6. (or (equal (first x) y) (not (equal (first x) y))) {PL}
C7. (implies (equal (first x) y) (endp (del y x))) {Def del, C1, C2, C5}
C8. (implies (equal (first x) y) (orderedp (del y x))) {Def orderedp, C7}
C9. (implies (not (equal (first x) y))
             (equal (del y x) x)) {Def del, C1, C2, C5}
C10. (implies (not (equal (first x) y)) (orderedp (del y x))) {C9, C3}
C11. (orderedp (del y x)) {Or-elimination, C6, C8, C10}

(implies (and (lorp x) (rationalp y) (orderedp x)) (orderedp (del y x)))
={MP, C1, C2, C3}
(orderedp (del y x))
={C11}
t

4. (implies (and (lorp x) (rationalp y) (orderedp x) (not (endp x))
                 (not (endp (rest x)))
                 (< (first x) (second x))
                 (L9.1.1 | ((x (rest x))))) L9.1.1)

C1. (lorp x)
C2. (rationalp y)
C3. (orderedp x)
C4. (not (endp x))
C5. (not (endp (rest x)))
C6. (< (first x) (second x))
C7. (implies (and (lorp (rest x)) (rationalp y) (orderedp (rest x))) 
             (orderedp (del y (rest x))))
--------
C8. (lorp (rest x)) {Def lorp, C1, C4}
C9. (orderedp (rest x)) {Def orderedp, C3, C4, C6}
C10. (orderedp (del y (rest x))) {MP, C7, C8, C2, C9}
C11. (and (< (first (rest x)) (second (rest x))) (orderedp (rest (rest x)))) 
     {Def orderedp, C9, C5}
C12. (or (equal (first x) y) (not (equal (first x) y))) {PL, C4}
C13. (implies (equal (first x) y) (equal (del y x) (rest x)))
C14. (implies (equal (first x) y) (orderedp (del y x))) {C13, C9}
C15. (implies (not (equal (first x) y))
              (equal (del y x) (cons (first x) (del y (rest x))))) {Def del, C4}
C16. (< (first x) (third x)) {Arith, C6, C11}
C17. (or (equal (second x) y) (not (equal (second x) y))) {Arith, C5}
C18. (implies (equal (second x) y) 
              (equal (del y (rest x)) (rest (rest x))))
C19. (implies (equal (second x) y) 
              (orderedp (cons (first x) (del y (rest x)))))
     {C18, C11, C16}
C20. (implies (not (equal (second x) y)) 
              (equal (del y (rest x)) (cons (second x) (del y (rest (rest x)))))) 
     {Def del, C5}
C21. (implies (not (equal (second x) y))
              (< (first x) (first (del y (rest x))))) {C20, C6}           
C23. (implies (not (equal (second x) y))
              (orderedp (cons (first x) (del y (rest x)))))
      {Def orderedp, C10, C21}
C24. (orderedp (cons (first x) (del y (rest x)))) {Or-elim, C17, C19, C23}
C25. (implies (not (equal (first x) y))
              (orderedp (del y x))) {C15, C24}
C26. (orderedp (del y x)) {Or-elim, C12, C14, C25}

(implies (and (lorp x) (rationalp y) (orderedp x)) (orderedp (del y x)))
={MP, C1, C2, C3}
(orderedp (del y x))
={C26}
t

Second Lemma for L9 (L9.1.2)          
(implies (and (lorp x)
              (lorp y)
              (consp x)
              (consp y)
              (orderedp x)
              (orderedp y)
              (perm x y))
         (equal (first x) (first y)))

This will be proven by induction on (perm x y).

Proof obligations:

1. (implies (not (and (lorp x) (lorp y) (consp x) (consp y)
                      (orderedp x) (orderedp y) (perm x y)))
            L9.1.2)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (lorp y) (consp x) (consp y)
                 (orderedp x) (orderedp y) (perm x y)
                 (endp x))
            L9.1.2)
Reductio ad absurdum. Done.

3. (implies (and (lorp x) (lorp y) (consp x) (consp y)
                 (orderedp x) (orderedp y) (perm x y)
                 (L9.1.2 | (x (rest x)) (y (del (first x) y)))))
            L9.1.2)

C1. (lorp x)
C2. (lorp y)
C3. (consp x)
C4. (consp y)
C5. (orderedp x)
C6. (orderedp y)
C7. (perm x y)
C8. (not (endp x))
C9. (implies (and (lorp (rest x)) (lorp (del (first x) y)) (consp (rest x)) (consp (del (first x) y))
                  (orderedp (rest x)) (orderedp (del (first x) y)) (perm (rest x) (del (first x) y)))
             (equal (first (rest x)) (first (del (first x) y))))
------------------
C10. (and (rationalp (first x)) (lorp (rest x))) {Def lorp, C1, C3}
C11. (lorp (del (first x) y)) {Contract thm del, C2, C3}
C12. (and (in (first x) y) (perm (rest x) (del (first x) y))) {Def perm, C7, C8}
C13. (consp y) {in axiom, C10}
C14. (or (endp (rest x)) (and (consp (rest x)) (lorp (rest x)))) {Def lorp, C1, C10}
C15. (or (endp (rest y)) (and (consp (rest y)) (lorp (rest y)))) {Def lorp, C2, C11}
C16. (implies (endp (rest x)) (endp (del (first x) y))) {Def perm, C12}
C17. (implies (endp (rest x)) (endp (rest y))) {Def del, C12, C13, C16}
C18. (implies (endp (rest x)) (equal x y)) {C12, C17}
C19. (implies (and (consp (rest x)) (lorp (rest x))) 
              (in (first (rest x)) (del (first x) y))) {Def perm, C7}
C20. (implies (and (consp (rest x)) (lorp (rest x))) 
              (consp (del (first x) y))) {in axiom, C19}
C21. (implies (and (consp (rest x)) (lorp (rest x))) 
              (and (<= (first x) (first (rest x))) (orderedp (rest x))))
     {Def orderedp C5, C8}
C22. (orderedp (del (first x) y)) {L9.1.1, C10, C2, C6}
C23. (implies (and (consp (rest x)) (lorp (rest x))) 
              (equal (first (rest x)) (first (del (first x) y)))) 
     {MP, C9, C10, C11, C22, C12}
C24. (implies (and (consp (rest x)) (lorp (rest x)))
              (<= (first x) (first (del (first x) y))))
     {equal axiom, C21, C23}
C25. (implies (and (consp (rest x)) (lorp (rest x)))
              (<= (first y) (first (rest y)))



Now, L9.1:   

(implies (and (lorp x)
              (lorp y)
              (orderedp x)
              (orderedp y)
              (perm x y))
          (equal x y))
          
          
This will be proven using the induction scheme of orderedp.

Proof obligations:

1. (implies (not (and (lorp x) (lorp y) (orderedp x) (orderedp y) (perm x y))) L9.1)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (lorp y) (orderedp x) (orderedp y) (perm x y) (endp x)) L9.1)

C1. (lorp x)
C2. (lorp y)
C3. (orderedp x)
C4. (orderedp y)
C5. (perm x y)
C6. (endp x)
-------------
C7. (endp y) {Def perm, C5, C6}

(implies (and (lorp x) (lorp y) (orderedp x) (orderedp y) (perm x y)) (equal x y))
={MP, C1, C2, C3, C4, C5}
(equal x y)
={C6, C1}
(equal nil y)
={C7, C2}
(equal nil nil)
={equal axiom}
t

3. (implies (and (lorp x) (lorp y) (orderedp x) (orderedp y) (perm x y) 
                 (consp x) (endp (rest x))
                 (L9.1 | ((x (rest x)) (y (rest y))))) 
            L9.1)

C1. (lorp x)
C2. (lorp y)
C3. (orderedp x)
C4. (orderedp y)
C5. (perm x y)
C6. (consp x)
C7. (endp (rest x)) -- unused
C8. (implies (and (lorp (rest x)) (lorp (rest y)) 
                  (orderedp (rest x)) (orderedp (rest y)) 
                  (perm (rest x) (rest y)))
              (equal (rest x) (rest y)))
-------------
C9. (and (rationalp (first x)) (lorp (rest x))) {Def lorp, C1, C6}
C10. (consp y) {in axiom, C7}
C11. (and (rationalp (first y)) (lorp (rest y))) {Def lorp, C2, C10}
C12. (orderedp (rest x)) {Def orderedp, C3, C6}
C13. (orderedp (rest y)) {Def orderedp, C3, C10}
C14. (in (first x) y) {Def perm C5, C6}
C15. (perm (rest x) (del (first x) y)) {Def perm, C5, C6, C14}
C16. (equal (first x) (first y)) {L9.1.2, C1, C2, C3, C4, C5}
C17. (equal (del (first x) y) (del (first y) y)) {equal axiom, C16}
C18. (equal (del (first x) y) (rest y)) {Def del, C17}
C19. (perm (rest x) (rest y)) {equal axiom, C14, C18}
C20. (equal (rest x) (rest y)) {MP, C8, C9, C11, C12, C13, C17}
C21. (equal x y) {equal axiom C16, C20}

(implies (and (lorp x)
              (lorp y)
              (orderedp x)
              (orderedp y)
              (perm x y))
          (equal x y))
={MP, C1, C2, C3, C4, C5}
(equal x y)
={C20}
t

4. (implies (and (lorp x) (lorp y) (orderedp x) (orderedp y) (perm x y) 
                 (consp x) (consp (rest x)) (<= (first x) (first (rest x)))
                 (L9.1 | ((x (rest x)) (y (rest y))))) 
            L9.1)

The proof for 3. above will work here as well -- the facts about (rest x) are unimportant.


Now, Q9. 
With L9.1, this won't even need induction!

(implies (lorp x) (equal (qsort x) (isort x)))

C1. (lorp x)
-----------
C2. (lorp (isort x)) {Contract thm isort, C1}
C3. (lorp (qsort x)) {Contract thm qsort, C1}
C4. (orderedp (isort x)) {Q1, C1}
C5. (perm x (isort x)) {Q7, C1}
C6. (orderedp (qsort x)) {Q2, C1}
C7. (perm x (qsort x)) {Q3, C1}
C8. (perm (qsort x) x) {Q5, C7}
C9. (perm (qsort x) (isort x)) {Q6, C8, C5}
C10. (equal (qsort x) (isort x)) {L9.1, C2, C3, C4, C5, C9}

(implies (lorp x) (equal (qsort x) (isort x)))
={MP, C1}
(equal (qsort x) (isort x))
={C10}
t
          

Extra credit:

Define a function, induction-scheme, that given a defunc function
definition and a conjecture as input generates the induction scheme
corresponding to the function definition and the conjecture.  You have
a lot of flexibility in how to go about doing this. This is on
purpose, so that you can identify and resolve the issues that come up
on your own.

Here is an example.

(induction-scheme
 '(defunc app (x y)
    :input-contract (and (listp x) (listp y))
    :output-contract (listp (app x y))
    (if (endp x)
        y
      (cons (first x) (app (rest x) y))))
 '(implies (and (listp x) (listp y) (listp z))
           (equal (app (app x y)) (app x (app y z)))))

should return something equivalent to:

(and 
 (implies (not (and (listp x) (listp y)))
          (implies (and (listp x) (listp y) (listp z))
                   (equal (app (app x y)) (app x (app y z)))))
 (implies (and (listp x) (listp y) (endp x)) 
          (implies (and (listp x) (listp y) (listp z))
                   (equal (app (app x y)) (app x (app y z)))))
 (implies (and (listp x) (listp y) (not (endp x)) 
               (implies (and (listp (rest x)) (listp y) (listp z))
                        (equal (app (app (rest x) y)) 
                               (app (rest x) (app y z)))))
          (implies (and (listp x) (listp y) (listp z))
                   (equal (app (app x y)) (app x (app y z))))))

The exact syntax is not important and it is OK for you to require that
cond is used instead of if, etc. Also, you don't have to worry about
whether the argument to induction-scheme corresponds to a terminating
function. You can assume that the function definition is admissible
and that the conjecture is well-formed.

I recommend that everyone at least try this because the attempt will
help you better understand induction.

|#

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

(acl2::set-guard-checking :none)

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
#|
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
|#

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
           (perm x y)))
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