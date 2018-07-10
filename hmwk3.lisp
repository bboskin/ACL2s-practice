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
(defdata gender (enum '(M F)))

(defdata lonat (listof nat))

(defdata rec
  (record (id . nat)
          (name . string)
          (gend . gender)
          (birthdate . string)
          (deathdate . string)
          (mother . nat)
          (father . nat)
          (children . lonat)))

(acl2::in-theory
 (acl2::disable
  rec-id rec-name rec-gend rec-birthdate rec-deathdate rec-mother rec-father rec-children))

(defunc fin (x y i acc)
  :input-contract (and (listp y) (posp i) (listp acc))
  :output-contract (booleanp (fin x y i acc))
  (cond ((endp y) nil)
        ((and (equal x (first y))
              (not (in i acc)))
         t)
        (t (fin x (rest y) (+ 1 i) acc))))

(defunc index (x y i acc)
  :input-contract (and (listp y) (posp i) (listp acc))
  :output-contract (natp (index x y i acc))
  (cond ((endp y) 0)
        ((and (equal x (first y))
              (not (in i acc)))
         i)
        (t (index x (rest y) (+ i 1) acc))))

(defunc fa (x y acc)
  :input-contract (and (listp x) (listp y) (listp acc))
  :output-contract (listp (fa x y acc))
  (cond ((endp x) (rev acc))
        ((fin (first x) y 1 acc)
         (fa (rest x) y
             (cons (index (first x) y 1 acc) acc)))
        (t nil)))

(defunc find-arrangement (x y)
  :input-contract (and (listp x) (listp y))
  :output-contract (listp (find-arrangement x y))
  (if (equal (len x) (len y))
    (fa x y nil)
    nil))

(defdata lop (listof pos))

(defunc shift-large-down (max ls)
  :input-contract (and (posp max) (lopp ls))
  :output-contract (lopp (shift-large-down max ls))
  (cond ((endp ls) ())
        (t (let ((a (first ls))
                    (res (shift-large-down max (rest ls))))
             (if (> a max) (cons (- a 1) res)
               (cons a res))))))

(defunc remove-nth (i ls)
  :input-contract (and (natp i) (listp ls))
  :output-contract (listp (remove-nth i ls))
  (cond ((endp ls) ())
        ((equal i 0) (rest ls))
        (t (cons (first ls) (remove-nth (- i 1) ls)))))

(defunc valid-arr? (a n)
  :input-contract (and (lopp a) (natp n))
  :output-contract (booleanp (valid-arr? a n))
  (cond ((endp a) t)
        ((>= (first a) n) nil)
        (t (valid-arr? (rest a) n))))

(defunc no-duplicates? (a)
  :input-contract (listp a)
  :output-contract (booleanp (no-duplicates? a))
  (cond ((endp a) t)
        ((in (first a) (rest a)) nil)
        (t (no-duplicates? (rest a)))))

(defdata rec-nil (oneof rec nil))

(defdata database (listof rec))

(defconst *database*
  (list
   (rec 1  "John Jones"     'M "1932-10-11" "2008-01-03" 0  0 '(3))
   (rec 2  "Linda Adams"    'F "1934-03-05" ""           0 10 '(3))
   (rec 3  "Davis Jones"    'M "1956-08-04" ""           2  1 '(6 7 8))
   (rec 4  "Susan Scott"    'F "1960-12-09" ""           0  0 '(6 7))
   (rec 5  "Barbara Haris"  'F "1970-09-03" ""           0  0 '(8))
   (rec 6  "Mark Jones"     'M "1985-03-03" ""           4  3 '())
   (rec 7  "Dorothy Jones"  'F "1983-04-01" ""           4  3 '(9))
   (rec 8  "Kevin Haris"    'M "1989-07-06" ""           5  3 '())
   (rec 9  "Maria Smith"    'F "2008-04-08" ""           7  11 '())
   (rec 10  "Martin Walker" 'M "1901-01-04" "1977-10-08" 0  0 '(2))
   (rec 11 "John Smith"     'M "1981-02-11" ""           0  0 '(9))))

(defunc lookup (key d)
  :input-contract (and (natp key) (databasep d))
  :output-contract (or (recp (lookup key d)) (equal (lookup key d) nil))
  (cond ((endp d) nil)
        ((equal key (rec-id (first d))) (first d))
        (t (lookup key (rest d)))))

(defunc union (l1 l2)
  :input-contract (and (listp l1) (listp l2))
  :output-contract (listp (union l1 l2))
  (cond ((endp l1) l2)
        ((in (first l1) l2) (union (rest l1) l2))
        (t (cons (first l1) (union (rest l1) l2)))))

(defunc share-mother (id d mom)
  :input-contract (and (and (natp id) (natp mom)) (databasep d))
  :output-contract (databasep (share-mother id d mom))
  (cond ((endp d) ())
        ((and (equal (rec-mother (first d)) mom) 
              (not (equal (rec-id (first d)) id)))
         (cons (first d) (share-mother id (rest d) mom)))
        (t (share-mother id (rest d) mom))))

(defunc share-father (id d dad)
  :input-contract (and (and (natp id) (natp dad)) (databasep d))
  :output-contract (databasep (share-father id d dad))
  (cond ((endp d) ())
        ((and (equal (rec-father (first d)) dad) 
              (not (equal (rec-id (first d)) id)))
         (cons (first d) (share-father id (rest d) dad)))
        (t (share-father id (rest d) dad))))

(defunc db-union (l1 l2)
  :input-contract (and (databasep l1) (databasep l2))
  :output-contract (databasep (db-union l1 l2))
  (cond ((endp l1) l2)
        ((in (first l1) l2) (db-union (rest l1) l2))
        (t (cons (first l1) (db-union (rest l1) l2)))))

(defunc format-rec (r)
  :input-contract (recp r)
  :output-contract (listp (format-rec r))
  (list (rec-id r) (rec-name r) (rec-gend r) (rec-birthdate r) 
        (rec-deathdate r) (rec-mother r) (rec-father r) (rec-children r)))

(defunc format-db (d)
  :input-contract (databasep d)
  :output-contract (listp (format-db d))
  (cond ((endp d) ())
        (t (cons (format-rec (first d))
                 (format-db (rest d))))))

:program

(acl2s-defaults :set testing-enabled nil)

(defunc ancestors (id d)
  :input-contract (and (natp id) (databasep d))
  :output-contract (databasep (ancestors id d))
  (let ((r (lookup id d)))
    (if (equal r nil) ()
      (let ((mom (rec-mother r))
            (dad (rec-father r)))
        (let ((mom-rec (lookup mom d))
              (dad-rec (lookup dad d)))
          (app (list mom-rec dad-rec)
               (app (ancestors mom d)
                    (ancestors dad d))))))))

(defunc ancestors2 (id d)
  :input-contract (and (natp id) (databasep d))
  :output-contract (databasep (ancestors2 id d))
  (let ((r (lookup id d)))
    (if (equal r nil) ()
      (let ((mom (rec-mother r))
            (dad (rec-father r)))
        (let ((mom-rec (lookup mom d))
              (dad-rec (lookup dad d)))
          (cond
           ((equal mom-rec nil) 
            (if (equal dad-rec nil) ()
              (cons dad-rec (ancestors2 dad d))))
           (t (cons mom-rec (app (ancestors2 mom d)
                                 (if (equal dad-rec nil) ()
                                   (cons dad-rec (ancestors2 dad d))))))))))))

(defunc db-remove (id d)
  :input-contract (and (natp id) (databasep d))
  :output-contract (databasep (db-remove id d))
  (cond ((endp d) ())
        ((equal id (rec-id (first d))) (rest d))
        (t (cons (first d) (db-remove id (rest d))))))

(defunc siblings (id d)
  :input-contract (and (natp id) (databasep d))
  :output-contract (databasep (siblings id d))
  (let ((r (lookup id d)))
    (if (equal r nil) ()
      (let ((mom (rec-mother r))
            (dad (rec-father r)))
        (let ((new-db1 (db-remove mom d))
              (new-db2 (db-remove dad d)))
          (let ((msiblings (share-mother id new-db1 mom))
                (dsiblings (share-father id new-db2 dad)))
            (db-union msiblings dsiblings)))))))

(defunc subset? (l1 l2)
  :input-contract (and (listp l1) (listp l2))
  :output-contract (booleanp (subset? l1 l2))
  (cond ((endp l1) t)
        ((in (first l1) l2) (subset? (rest l1) l2))
        (t nil)))

(defunc listEQ (l1 l2)
  :input-contract (and (listp l1) (listp l2))
  :output-contract (booleanp (listEQ l1 l2))
  (and (subset? l1 l2) (subset? l2 l1)))#|ACL2s-ToDo-Line|#



(set-defunc-termination-strictp nil)
(set-defunc-function-contract-strictp nil)
(set-defunc-body-contracts-strictp nil)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Part I: What's my grade?
;;

;; Question 1a
;; Define a list of rationals.

(defdata lor (listof rational))

;; Question 1b
;; Define a non-empty list of rationals.
;; Add a test? form characterizing nlor in terms of lor

(defdata nlor (cons rational lor))

(check= (nlorp '()) nil)
(check= (nlorp '(1/2 -2)) t)

;; added tests
(test? (equal (nlorp (cons x ls)) (lorp (cons x ls))))
(test? (equal (and (rationalp x) (lorp ls)) (nlorp (cons x ls))))
(test? (equal (and (not (endp ls)) (lorp ls)) (nlorp ls)))


;; Question 1c
;; Define sum-all, a function that given a list of rationals
;; returns their sum.

(defunc sum-all (l)
  :input-contract (lorp l)
  :output-contract (rationalp (sum-all l))
  (if (endp l) 0
    (+ (first l) (sum-all (rest l)))))

;; tests
(check= (sum-all (list)) 0)
(check= (sum-all (list 1/2 1/2 2/4)) 3/2)
(check= (sum-all (list -1 1 -1 1 1/9)) 1/9)
(test? (equal (sum-all (cons 0 l)) (sum-all l)))
(test? (equal (sum-all (cons a (cons b ()))) (+ a b)))


;; Question 1d
;; Define course-grade, a function that takes as input the following arguments:
;;   hwks, a non-empty list of rationals numbers corresponding to your
;;         homework grades (the maximum homework grade is 100)
;;   e1, a rational corresponding to your exam 1 grade
;;   e2, a rational corresponding to your exam 2 grade
;;   quizzes, a non-empty list of rationals numbers corresponding to your
;;       quiz grades (the maximum quiz grade is 24)
;; The function returns a rational, which is your grade for the course.
;; Recall that the syllabus tells you what the formula is.
;; In more detail, use this formula from the syllabus:
;;
;; Homeworks: 20%
;; Exam 1 : 30%
;; Exam 2 : 30%
;; Quizzes : 20%
;;
;; To use this function during the semester use any homework grades
;; you currently have that you expect to be in the top 10 (we expect
;; to give you 12 homework assignments) and use the top 90% of your
;; quiz grades. Similarly, you can experiment with various grades for
;; exams you have not taken.
;;
;; You can use this function to calculate your grade during the
;; semester under various what-if conditions. For example, to see what
;; the highest grade you might get is, use 100 for all missing exam &
;; hwk grades and 24 for all missing quiz grades. You can assume you
;; will have 10 grades homeworks and 20 graded quizzes.

(defunc course-grade (hwks e1 e2 quizzes)
  :input-contract (and (nlorp hwks) (rationalp e1) (rationalp e2) (nlorp quizzes))
  :output-contract (rationalp (course-grade hwks e1 e2 quizzes))
  (+ (* 1/5 (/ (sum-all hwks) (len hwks)))
     (+ (+ (* 3/10 e1) (* 3/10 e2))
     (* 1/5 (* 100/24 (/ (sum-all quizzes) (len quizzes)))))))

(check= (course-grade '(100) 100 100 '(24)) 100)
(check= (course-grade '(100 100 100 100) 100 100 '(24 24 24 24 24 24)) 100)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Part II: Property-based testing
;;
;;
;; Consider the following buggy solution for find-arrangements
;; from the last homerk.

;; fin checks to see if x is in y but not in any of the indices
;; in acc, starting with index i. It should be called with i=1.
;; For example 1 is in (1 2 3 1 4) in indices 1 and 4.
(defunc fin (x y i acc)
  :input-contract (and (listp y) (posp i) (listp acc))
  :output-contract (booleanp (fin x y i acc))
  (cond ((endp y) nil)
        ((and (equal x (first y))
              (not (in i acc)))
         t)
        (t (fin x (rest y) (+ 1 i) acc))))

;; If x is in y starting at some index which is >= i and not in acc,
;; then the index function returns the first such index. Otherwise, it
;; returns 0.
(defunc index (x y i acc)
  :input-contract (and (listp y) (posp i) (listp acc))
  :output-contract (natp (index x y i acc))
  (cond ((endp y) 0)
        ((and (equal x (first y))
              (not (in i acc)))
         i)
        (t (index x (rest y) (+ i 1) acc))))

;; fa is a helper function for find-arrangement. It is called only if
;; x and y are lists of the same length. It finds an arrrangement if 
;; one exists, otherwise it returns nil.
(defunc fa (x y acc)
  :input-contract (and (listp x) (listp y) (listp acc))
  :output-contract (listp (fa x y acc))
  (cond ((endp x) (rev acc))
        ((fin (first x) y 1 acc)
         (fa (rest x) y
             (cons (index (first x) y 1 acc) acc)))
        (t nil)))

(defunc find-arrangement (x y)
  :input-contract (and (listp x) (listp y))
  :output-contract (listp (find-arrangement x y))
  (if (equal (len x) (len y))
    (fa x y nil)
    nil))

(check= (find-arrangement '(a b c) '(a b b)) nil)
(check= (find-arrangement '(a b c) '(a c b)) '(1 3 2))
(check= (find-arrangement '(a a) '(a a)) '(1 2))

;; Notice that all the check= forms pass. However, the definition of
;; find-arrangement is buggy.
;;
;; We will use property-based testing to more thoroughly test this and
;; other implementations of find-arrangement.  We start by defining a
;; function to apply an arrangement to a list, thereby obtaining a
;; permutation of the list.

;; First, an arrangement has to be a list of positive integers (but
;; not every list of positive integers is an arrangement!)

(defdata lop (listof pos))

;; Question 2a
;;
;; Define apply-arrangement, a function that takes a list, l, and an
;; arrangement, a, (of type lop) as arguments and, assuming that a is
;; really an arrangement (see HWK2), then it returns the result of
;; applying the arrangement a to the list l.  You might find the
;; function nth useful. If finds the nth number in a list, using
;; 0-indexing, so (nth 0 '(0 1 2 3)) is 0, (nth 3 '(0 1 2 3)) is 3 and
;; if the number is too big, nil is returned, e.g.,
;; (nth 10 '(0 1 2  3)) is nil.

(defunc shift-large-down (max ls)
  :input-contract (and (posp max) (lopp ls))
  :output-contract (and (lopp (shift-large-down max ls))
                        (equal (len ls) (len (shift-large-down max ls))))
  (cond ((endp ls) ())
        (t (let ((a (first ls))
                    (res (shift-large-down max (rest ls))))
             (if (> a max) (cons (- a 1) res)
               (cons a res))))))

(test? (equal (shift-large-down n nil) nil))
(test? (if (in n (shift-large-down n ls)) 
         (or (in n ls) (in (+ 1 n) ls))
         t))
(check= (shift-large-down 5 (list 1 2 3)) (list 1 2 3))
(check= (shift-large-down 4 (list 2 3 9)) (list 2 3 8))
(check= (shift-large-down 1 (list 2 4 3)) (list 1 3 2))

(defunc remove-nth (i ls)
  :input-contract (and (natp i) (listp ls))
  :output-contract (listp (remove-nth i ls))
  (cond ((endp ls) ())
        ((equal i 0) (rest ls))
        (t (cons (first ls) (remove-nth (- i 1) ls)))))

(defunc valid-arr? (a n)
  :input-contract (and (lopp a) (natp n))
  :output-contract (booleanp (valid-arr? a n))
  (cond ((endp a) t)
        ((>= (first a) n) nil)
        (t (valid-arr? (rest a) n))))

(defunc no-duplicates? (a)
  :input-contract (listp a)
  :output-contract (booleanp (no-duplicates? a))
  (cond ((endp a) t)
        ((in (first a) (rest a)) nil)
        (t (no-duplicates? (rest a)))))

(defunc apply-arrangement (l a)
  :input-contract (and (and (listp l) 
                            (and (lopp a) 
                                 (and (valid-arr? a (len l))
                                      (no-duplicates? a))))
                       (equal (len l) (len a)))
  :output-contract (listp (apply-arrangement l a))
  (if (endp l) ()
    (cons (nth (- (first a) 1) l)
          (apply-arrangement (remove-nth (- a 1) l) 
                             (shift-large-down a (rest a))))))
         

(check= (apply-arrangement '(a b c) '(1 3 2))
        '(a c b))

;; Question 2b
;;
;; Recall that in HWK2, we required that find-arrangement
;; work as follows.
;;
;; Define the function find-arrangement that given two lists, either
;; returns nil if they are not permutations of one another or returns an
;; arrangement such that applying the arrangement to the first list
;; yields the second list.
;;
;; Turn the statement above into a test? that relates find-arrangement
;; with apply-arrangement, but assume that the arguments to
;; apply-arrangement are of the type losyms, defined below.
;; Your test? should check that if find-arrangement returns an
;; arrangement then applying it to the first list yields the second.

;; Ask ACL2s to try hard
(acl2s-defaults :set num-trials 50000)

(defdata syms (enum '(a b c)))
(defdata losyms (listof syms))

(test? (if (and (losymsp a) (losymbp b))
         (let ((arr (find-arrangement a b)))
           (if arr
             (equal (apply-arrangement a arr) b)
             t))
         t))

;; Question 2c
;; 
;; You should have found some counterexamples. Use them to fix the
;; definition of fa (do not modify any other definitions).  You will
;; have to move the line back past fa, then modify fa and then move
;; the line forward to recheck the test? form.


;; Let's reset this value
(acl2s-defaults :set num-trials 1000)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Part 3: Genealogy Database
; 
; You and some friends have created ACL2s-Family.com, to help busy ACL2s hackers
; remember their family obligations. The website is not very popular yet, but
; you are busy adding new functionality in anticipation of a traffic boom. 
;
; We keep track of people with the following database structure:
;
; record ::= (list id
;                  full-name
;                  gender
;                  birth-date
;                  death-date
;                  mother-id
;                  father-id
;                  (list child-id)
;
; id, child-id ::= nat
; mother-id, father-id ::= nat 
; full-name ::= string
; gender ::= 'M | 'F
; 
; database ::= listof record
;
; mother-id and father-id are 0 if the corresponding person is not
; in our database.
;

; Question 3a
;
; Define the type gender, which is either the symbol M or F.
; 
; Notice the *database* defconst below, which you can use
; to check your definition.

(defdata gender (enum '(M F)))

; Question 3b
;
; Define lonat, a list of natural numbers.

(defdata lonat (listof nat))

; Question 3c
;
; Define rec, a record whose fields are id, name, gend, birthdate,
; deathdate, mother, father and children.
;
; Notice the *database* defconst below, which you can use
; to check your definition.

(defdata rec
  (record (id . nat)
          (name . string)
          (gend . gender)
          (birthdate . string)
          (deathdate . string)
          (mother . nat)
          (father . nat)
          (children . lonat)))
; If you used the names specified above, this should go through
(acl2::in-theory
 (acl2::disable
  rec-id rec-name rec-gend rec-birthdate rec-deathdate rec-mother rec-father rec-children))

; Question 3d
;
; Define database, a list of rec's

(defdata database (listof rec))

; Make sure your data definitions work.  Defconst defines a constant. In this
; case, it is a database that we will use below.

(defconst *database*
  (list
   (rec 1  "John Jones"     'M "1932-10-11" "2008-01-03" 0  0 '(3))
   (rec 2  "Linda Adams"    'F "1934-03-05" ""           0 10 '(3))
   (rec 3  "Davis Jones"    'M "1956-08-04" ""           2  1 '(6 7 8))
   (rec 4  "Susan Scott"    'F "1960-12-09" ""           0  0 '(6 7))
   (rec 5  "Barbara Haris"  'F "1970-09-03" ""           0  0 '(8))
   (rec 6  "Mark Jones"     'M "1985-03-03" ""           4  3 '())
   (rec 7  "Dorothy Jones"  'F "1983-04-01" ""           4  3 '(9))
   (rec 8  "Kevin Haris"    'M "1989-07-06" ""           5  3 '())
   (rec 9  "Maria Smith"    'F "2008-04-08" ""           7  11 '())
   (rec 10  "Martin Walker" 'M "1901-01-04" "1977-10-08" 0  0 '(2))
   (rec 11 "John Smith"     'M "1981-02-11" ""           0  0 '(9))))

(check= (databasep *database*) t)

; Question 3e
; 
; Define rec-nil, a datatype that recognizes rec's or nil.

(defdata rec-nil (oneof rec nil))

(check= (rec-nilp nil) t)
(check= (rec-nilp
         (rec 1  "John Jones"     'M "1932-10-11" "2008-01-03" 0  0 '(3)))
        t)

; Question 3f
; 
; Define lookup, a function which given a key (natp) and a
; database. If the database contains a record whose id is key then the
; first such record is returned; otherwise nil is returned.

(defunc lookup (key d)
  :input-contract (and (natp key) (databasep d))
  :output-contract (or (recp (lookup key d)) (equal (lookup key d) nil))
  (cond ((endp d) nil)
        ((equal key (rec-id (first d))) (first d))
        (t (lookup key (rest d)))))

(check= (lookup 2 *database*) (rec 2  "Linda Adams"    'F "1934-03-05" ""           0 10 '(3)))
(check= (lookup 100 *database*) nil)
(test? (equal (lookup n nil) nil))
; Question 3g
;
; Define siblings, a function which given a key and a database returns
; the records of the person's siblings. Siblings are people who have
; the same mother or the same father (or both).  If there is no record
; in the database with the key, return the empty list.

(defunc db-union (l1 l2)
  :input-contract (and (databasep l1) (databasep l2))
  :output-contract (databasep (db-union l1 l2))
  (cond ((endp l1) l2)
        ((in (first l1) l2) (db-union (rest l1) l2))
        (t (cons (first l1) (db-union (rest l1) l2)))))

(defunc db-remove (id d)
  :input-contract (and (natp id) (databasep d))
  :output-contract (databasep (db-remove id d))
  (cond ((endp d) ())
        ((equal id (rec-id (first d))) (rest d))
        (t (cons (first d) (db-remove id (rest d))))))

(defunc share-mother (id d mom)
  :input-contract (and (and (natp id) (natp mom)) (databasep d))
  :output-contract (databasep (share-mother id d mom))
  (cond ((endp d) ())
        ((and (equal (rec-mother (first d)) mom) 
              (not (equal (rec-id (first d)) id)))
         (cons (first d) (share-mother id (rest d) mom)))
        (t (share-mother id (rest d) mom))))

(defunc share-father (id d dad)
  :input-contract (and (and (natp id) (natp dad)) (databasep d))
  :output-contract (databasep (share-father id d dad))
  (cond ((endp d) ())
        ((and (equal (rec-father (first d)) dad) 
              (not (equal (rec-id (first d)) id)))
         (cons (first d) (share-father id (rest d) dad)))
        (t (share-father id (rest d) dad))))

(defunc siblings (id d)
  :input-contract (and (natp id) (databasep d))
  :output-contract (databasep (siblings id d))
  (let ((r (lookup id d)))
    (if (equal r nil) ()
      (let ((mom (rec-mother r))
            (dad (rec-father r)))
        (let ((new-db1 (db-remove mom d))
              (new-db2 (db-remove dad d)))
          (let ((msiblings (share-mother id new-db1 mom))
                (dsiblings (share-father id new-db2 dad)))
            (db-union msiblings dsiblings)))))))
        

;; for testing:
(defunc subset? (l1 l2)
  :input-contract (and (listp l1) (listp l2))
  :output-contract (booleanp (subset? l1 l2))
  (cond ((endp l1) t)
        ((in (first l1) l2) (subset? (rest l1) l2))
        (t nil)))

(defunc listEQ (l1 l2)
  :input-contract (and (listp l1) (listp l2))
  :output-contract (booleanp (listEQ l1 l2))
  (and (subset? l1 l2) (subset? l2 l1)))

(check= (siblings 12 *database*) nil)
(check= (siblings 3 *database*) nil)
(test? (listEQ (siblings 4 *database*) 
               (list (rec 1  "John Jones"     'M "1932-10-11" "2008-01-03" 0  0 '(3))
                     (rec 2  "Linda Adams"    'F "1934-03-05" ""           0 10 '(3))
                     (rec 4  "Susan Scott"    'F "1960-12-09" ""           0  0 '(6 7))
                     (rec 5  "Barbara Haris"  'F "1970-09-03" ""           0  0 '(8))
                     (rec 10  "Martin Walker" 'M "1901-01-04" "1977-10-08" 0  0 '(2))
                     (rec 11 "John Smith"     'M "1981-02-11" ""           0  0 '(9)))))

; Question 3h
;
; You notice that when you tested siblings using *database* the output
; generated was hard to read, so you are going to define formatting
; functions to format records and databases using the check= form
; below as guide. You can just use listp for the output contracts of
; the two functions.

(defunc format-rec (r)
  :input-contract (recp r)
  :output-contract (listp (format-rec r))
  (list (rec-id r) (rec-name r) (rec-gend r) (rec-birthdate r) 
        (rec-deathdate r) (rec-mother r) (rec-father r) (rec-children r)))

(check= (format-rec (lookup 1 *database*))
        '(1 "John Jones" M "1932-10-11" "2008-01-03" 0 0 (3)))

; Question 3i
;
; format-db format a database, using format-rec

(defunc format-db (d)
  :input-contract (databasep d)
  :output-contract (listp (format-db d))
  (cond ((endp d) ())
        (t (cons (format-rec (first d))
                 (format-db (rest d))))))

(check= (format-db (list (lookup 1 *database*)))
        '((1 "John Jones" M "1932-10-11" "2008-01-03" 0 0 (3))))

; We are switching to program mode and turning off testing

:program
(acl2s-defaults :set testing-enabled nil)

; Question 3j
;
; Given a person's id and a database, return the records that
; correspond to person's ancestors. You can assume that no person in
; the database can be their own ancestor. The result returned should
; not have duplicate records.

(defunc ancestors2 (id d)
  :input-contract (and (natp id) (databasep d))
  :output-contract (databasep (ancestors2 id d))
  (let ((r (lookup id d)))
    (if (equal r nil) ()
      (let ((mom (rec-mother r))
            (dad (rec-father r)))
        (let ((mom-rec (lookup mom d))
              (dad-rec (lookup dad d)))
          (cond
           ((equal mom-rec nil) 
            (if (equal dad-rec nil) ()
              (cons dad-rec (ancestors2 dad d))))
           (t (cons mom-rec (app (ancestors2 mom d)
                                 (if (equal dad-rec nil) ()
                                   (cons dad-rec (ancestors2 dad d))))))))))))
(check= (len (ancestors2 9 *database*)) 7)
(check= (len (ancestors2 6 *database*)) 5)

; Now a challenge question. This is entirely optional, but you are
; encouraged to at least try. Don't ask if you get extra credit.
; Learning is its own reward.

; Challenge Question 3k
;
; Dorothy Jones and John Smith are now the happy parents of a second child.
; Due to a bug in the web application, the record that was entered in the
; database is
;
;    (rec 12 "Donald Smith"  'M "2017-12-12" ""          7   11  '(1))
;
; The records for Dorothy, John Smith and John Jones were updated by a
; database trigger to reflect the change. These records are now:
;
;    (rec  7 "Dorothy Jones" 'F "1983-04-01" ""           4 3  '(9 12))
;    (rec 11 "John Smith"    'M "1981-02-11" ""           0 0  '(9 12))
;    (rec  1 "John Jones"    'M "1932-10-11" "2008-01-03" 0 11 '(3))
;
; Here is the updated database

(defconst *n-db*
  (list
   (rec 1  "John Jones"     'M "1932-10-11" "2008-01-03" 0  0 '(3))
   (rec 2  "Linda Adams"    'F "1934-03-05" ""           0 10 '(3))
   (rec 3  "Davis Jones"    'M "1956-08-04" ""           2  1 '(6 7 8))
   (rec 4  "Susan Scott"    'F "1960-12-09" ""           0  0 '(6 7))
   (rec 5  "Barbara Haris"  'F "1970-09-03" ""           0  0 '(8))
   (rec 6  "Mark Jones"     'M "1985-03-03" ""           4  3 '())
   (rec 7  "Dorothy Jones"  'F "1983-04-01" ""           4  3 '(9 12))
   (rec 8  "Kevin Haris"    'M "1989-07-06" ""           5  3 '())
   (rec 9  "Maria Smith"    'F "2008-04-08" ""           7  11 '())
   (rec 10  "Martin Walker" 'M "1901-01-04" "1977-10-08" 0  0 '(2))
   (rec 11 "John Smith"     'M "1981-02-11" ""           0  0 '(9 12))
   (rec 12 "Donald Smith"   'M "2017-12-12" ""           7  11 '(1))))


; Implement a function that given a person's id and a database returns
; the person's descendants. The function should terminate even in the
; presence of inconsistencies like the one above for Donald. The
; result returned should not have duplicate records.

(defunc descendants (id d)
  ...)

(check= (len (descendants 1 *n-db*)) 7)
(check= (len (descendants 5 *n-db*)) 1)