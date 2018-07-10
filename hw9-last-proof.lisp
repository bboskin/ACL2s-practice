; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "custom" :dir :acl2s-modes :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
;;;;;; 
; Function definitions
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
#|
These definitions aren't needed!

(defunc del (e x)
  :input-contract (and (rationalp e) (lorp x))
  :output-contract (lorp (del e x))
  (cond ((endp x) nil)
        ((equal e (first x)) (rest x))
        (t (cons (first x) (del e (rest x))))))

(defunc in (a l)
  :input-contract (and (rationalp a) (lorp l))
  :output-contract (booleanp (in a l))
  (cond ((endp l) nil)
        ((equal (first l) a) t)
        (t (in a (rest l)))))

(defunc perm (x y)
  :input-contract (and (lorp x) (lorp y))
  :output-contract (booleanp (perm x y))
  (if (endp x)
      (endp y)
    (and (in (first x) y)
         (perm (rest x) (del (first x) y)))))
|#

;; Lemma 0: the result of insertion sort is ordered

(defthm insert-correct
  (implies (and (rationalp x)
                (lorp xs)
                (orderedp xs))
           (orderedp (insert x xs))))

(defthm isort-ordered
  (implies (lorp xs)
           (orderedp (isort xs))))

;; Now we know that (isort x) is ordered. 

;; Lemma 1: that 'less' and 'isort' are associative

;; helpers...
(defthm L1.1
  (implies (and (rationalp a) (rationalp b) (lorp x) 
                (orderedp x) (>= b a))
           (equal (less a (insert b x))
                  (less a x))))

(defthm L1.2
  (implies (and (rationalp a) (rationalp b) (lorp x) 
                (orderedp x) (< b a))
           (equal (less a (insert b x))
                  (insert b (less a x)))))

(defthm L1
  (implies (and (rationalp a) (lorp x))
           (equal (isort (less a x))
                  (less a (isort x)))))
;;;;;;;;;;;;

;; Lemma 2: that 'notless' and 'isort' are associative

(defthm L2.1
  (implies (and (rationalp a) (rationalp b) (lorp x) 
                (orderedp x) (< b a))
           (equal (notless a (insert b x))
                  (notless a x))))

(defthm L2.2
  (implies (and (rationalp a) (rationalp b) (lorp x) 
                (orderedp x) (>= b a))
           (equal (notless a (insert b x))
                  (insert b (notless a x)))))

(defthm L2
  (implies (and (rationalp a) (lorp x))
           (equal (isort (notless a x))
                  (notless a (isort x)))))

;;;;;;;;;;;;;

;; Lemma 3: that the appending and consing that quicksort does
;; is the same as inserting, for ordered lists

;; some interesting things came up here relating to re-write rules

;; alternatives to less and notless for ordered lists
(defunc get-before (x l)
  :input-contract (and (rationalp x) (lorp l))
  :output-contract (lorp (get-before x l))
  (cond ((endp l) nil)
        ((<= x (first l)) nil)
        (t (cons (first l) (get-before x (rest l))))))

(defunc get-after (x l)
  :input-contract (and (rationalp x) (lorp l))
  :output-contract (lorp (get-after x l))
  (cond ((endp l) nil)
        ((<= x (first l)) l)
        (t (get-after x (rest l)))))

(defthm before-less
  (implies (and (lorp x) (orderedp x) (rationalp a))
           (equal (less a x)
                  (get-before a x))))

(defthm after-notless
  (implies (and (lorp x) (orderedp x) (rationalp a))
           (equal (notless a x)
                  (get-after a x))))

(defthm L3
  (implies (and (lorp x) (orderedp x) (rationalp z))
           (equal (append (less z x)
                          (cons z (notless z x)))
                  (insert z x))))

;;;;;;;;;;;;;;;

(defthm qsort=isort
  (implies (lorp x)
           (equal (qsort x) (isort x)))
  :hints (("Goal"
           :in-theory (disable before-less after-notless))))#|ACL2s-ToDo-Line|#


#|

Pencil & Paper proof, without lemmas done by hand 
(since they are all proven above):

Thm: (implies (lorp x) (equal (qsort x) (isort x)))

Using the induction scheme of (qsort x):

1. (implies (not (lorp x)) Thm)
Reductio ad absurdum. Done.

2. (implies (and (lorp x) (endp x)) Thm)

C1. (lorp x)
C2. (endp x)
------------

(equal (qsort x) (isort x))
={Def qsort, C2}
(equal nil (isort x))
={Def isort, C2}
(equal nil nil)
={equal axiom}
t

3. (implies (and (lorp x) (not (endp x))
                 (Thm | (x (less (first x) (rest x))))
                 (Thm | (x (notless (first x) (rest x)))))
            Thm)
            
C1. (lorp x)
C2. (not (endp x))
C3. (implies (lorp (less (first x) (rest x)))
             (equal (qsort (less (first x) (rest x)))
                    (isort (less (first x) (rest x)))))
C4. (implies (lorp (notless (first x) (rest x)))
             (equal (qsort (notless (first x) (rest x)))
                    (isort (notless (first x) (rest x)))))
----------------------------------------------------------
C5. (rationalp (first x)) {Def lorp, C1, C2}
C6. (lorp (rest x)) {Def lorp, C1, C2}
C7. (lorp (less (first x) (rest x))) {Contract thm, less, C5, C6}
C8. (lorp (notless (first x) (rest x))) {Contract thm, notless, C5, C6}
C9. (equal (qsort (less (first x) (rest x)))
           (isort (less (first x) (rest x)))) {MP, C3, C7}
C10. (equal (qsort (notless (first x) (rest x)))
            (isort (notless (first x) (rest x)))) {MP, C4, C8}
C11. (lorp (isort (rest x))) {Contract thm isort, C6}
C12. (orderedp (isort (rest x))) {isort-ordered, C6}
            
(equal (qsort x) (isort x))
={Def quicksort, isort, C2}
(equal (app (qsort (less (first x) (rest x)))
        (cons (first x) (qsort (notless (first x) (rest x)))))
   (insert (first x) (isort (rest x))))
={C9, C10}
(equal (app (isort (less (first x) (rest x)))
        (cons (first x) (isort (notless (first x) (rest x)))))
   (insert (first x) (isort (rest x))))     
={L1, C5, C11}
(equal (app (less (first x) (isort (rest x)))
        (cons (first x) (isort (notless (first x) (rest x)))))
   (insert (first x) (isort (rest x))))    
={L2, C5, C11}
(equal (app (less (first x) (isort (rest x)))
        (cons (first x) (notless (first x) (isort (rest x)))))
   (insert (first x) (isort (rest x)))) 
={L3, C11, C12, C5}
t
|#



