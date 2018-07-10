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
(defunc my-unary-- (n)
  :input-contract (and (natp n) (not (equal n 0)))
  :output-contract (natp (my-unary-- n))
  (+ n -1))

(defunc my-unary-/ (n)
  :input-contract (and (rationalp n) (not (equal n 0)))
  :output-contract (rationalp (my-unary-/ n))
  (/ 1 n))

(defunc my-integerp (x)
  :input-contract t
  :output-contract (booleanp (my-integerp x))
  (and (rationalp x)
       (equal 0 (acl2::mod x 1))))

(defunc find-one (x ls n)
  :input-contract (and (listp ls) (natp n))
  :output-contract (or (equal (find-one x ls n) nil)
                       (natp (find-one x ls n)))
  (if (endp ls) nil
    (if (equal x (first ls)) n
      (find-one x (rest ls) (+ n 1)))))

(defdata lon (listof nat))

(defunc member (x ls)
  :input-contract (listp ls)
  :output-contract (booleanp (member x ls))
  (if (endp ls) nil
    (if (equal x (first ls)) t
      (member x (rest ls)))))

(defunc find-loc (x ys ans i)
  :input-contract (and (listp ys) (and (lonp ans) (natp i)))
  :output-contract t
  (if (endp ys) nil
    (if (and (equal x (first ys)) (not (member i ans))) i
        (find-loc x (rest ys) ans (+ i 1)))))

(defunc find (x ys ans i)
  :input-contract (and (listp ys) (and (lonp ans) (natp i)))
  :output-contract (or (natp (find x ys ans i)) (equal (find x ys ans i) nil))
  (if (endp ys) nil
    (if (and (equal x (first ys)) (not (member i ans))) i
        (find x (rest ys) ans (+ i 1)))))

(defunc arrange (xs ys ans)
  :input-contract (and (and (listp xs) (listp ys)) 
                       (lonp ans))
  :output-contract (lonp (arrange xs ys ans))
  (if (endp xs) ans
    (let ((do (find (first xs) ys ans 1)))
      (if (equal do nil) nil
        (arrange (rest xs) ys  (app ans (list do)))))))

(defunc find-arrangement (x y)
  :input-contract (and (and (listp x) (listp y)))
  :output-contract (lonp (find-arrangement x y))
  (arrange x y ()))#|ACL2s-ToDo-Line|#


#|

CS 2800 Homework 2 - Spring 2018
Ben Boskin
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

For this homework you will need to use ACL2s.

Technical instructions:

- Open this file in ACL2s as hwk2.lisp

- Make sure you are in BEGINNER mode. This is essential! Note that you can
  only change the mode when the session is not running, so set the correct
  mode before starting the session.

- Insert your solutions into this file where indicated (usually as "...")

- Only add to the file. Do not remove or comment out anything pre-existing.

- Make sure the entire file is accepted by ACL2s. In particular, there must
  be no "..." left in the code. If you don't finish all problems, comment
  the unfinished ones out. Comments should also be used for any English
  text that you may add. This file already contains many comments, so you
  can see what the syntax is.

- When done, save your file and submit it as hwk2.lisp

- Do not submit the session file (which shows your interaction with the theorem
  prover). This is not part of your solution. Only submit the lisp file.

Instructions for programming problems:

For each function definition, you must provide both contracts and a body.

You must also ALWAYS supply your own tests. This is in addition to the
tests sometimes provided. Make sure you produce sufficiently many new test
cases. This means: cover at least the possible scenarios according to the
data definitions of the involved types. For example, a function taking two
lists should have at least 4 tests: all combinations of each list being
empty and non-empty.

Beyond that, the number of tests should reflect the difficulty of the
function. For very simple ones, the above coverage of the data definition
cases may be sufficient. For complex functions with numerical output, you
want to test whether it produces the correct output on a reasonable
number of inputs.

Use good judgment. For unreasonably few test cases we will deduct points.

We will use ACL2s' check= function for tests. This is a two-argument
function that rejects two inputs that do not evaluate equal. You can think
of check= roughly as defined like this:

(defunc check= (x y)
  :input-contract (equal x y)
  :output-contract (equal (check= x y) t)
  t)

That is, check= only accepts two inputs with equal value. For such inputs, t
(or "pass") is returned. For other inputs, you get an error. If any check=
test in your file does not pass, your file will be rejected.

Since this is our first programming exercise, we will simplify the interaction
with ACL2s somewhat. Instead of requiring ACL2s to prove termination and
contracts, we allow ACL2s to proceed even if a proof fails.  However, if a
counterexample is found, ACL2s will report it.  See section 2.17 of the lecture
notes for more information.  This is achieved using the following directives (do
not remove them):

|#

(set-defunc-termination-strictp nil)
(set-defunc-function-contract-strictp nil)
(set-defunc-body-contracts-strictp nil)

#| 

 Part I:
 Function definitions.

 In this part, you will be given a set of programming exercises. Since you
 already took a fantastic course on programming (CS2500), the problems are not
 entirely trivial. Make sure you give yourselves enough time to develop
 solutions and feel free to define helper functions as needed.

|# 

#|
Define the function rr.
rr: List x Nat -> List

(rr l n) rotates the list l to the right n times.
|#

(defunc all-but-last (l)
  :input-contract (and (listp l) (not (endp l)))
  :output-contract (and (listp (all-but-last l))
                        (equal (len (all-but-last l)) (- (len l) 1)))
  (if (endp (rest l)) nil
    (cons (first l) (all-but-last (rest l)))))

(defunc last (l)
  :input-contract (and (listp l) (not (endp l)))
  :output-contract t
  (if (endp (rest l)) (first l)
    (last (rest l))))

(defunc rr (l n)
  :input-contract (if (listp l) (natp n) nil)
  :output-contract (listp (rr l n))
  (if (equal n 0) l
    (if (equal l nil) l
      (rr (cons (last l) (all-but-last l)) (- n 1)))))

(check= (rr '(1 2 3) 1) '(3 1 2))
(check= (rr '(1 2 3) 2) '(2 3 1))
(check= (rr '(1 2 3) 3) '(1 2 3))

; added tests:
(check= (rr '() 4) '())
(check= (rr '() 0) '())
(check= (rr '(1 2 3) 0) '(1 2 3))
(check= (rr '(1 2 3) 4) '(3 1 2))


#|
Define the function err, an efficient version of rr.
err: List x Nat -> List

(err l n) returns the list obtained by rotating l to the right n times
but it does this efficiently because it actually never rotates more than
(len l) times.
You can use acl2::mod in your answer. For example (acl2::mod 11 3) = 2
because 11 mod 3 = 2.
|#

(defunc err (l n)
  :input-contract (and (listp l) (natp n))
  :output-contract (and (listp (err l n)))
  (if (endp l) nil
    (rr l (acl2::mod n (len l)))))

(check= (err '(1 2 3) 1) '(3 1 2))
(check= (err '(1 2 3) 2) '(2 3 1))
(check= (err '(1 2 3) 3) '(1 2 3))

; added tests:
(check= (err '() 4) '())
(check= (err '() 0) '())
(check= (err '(1 2 3) 0) '(1 2 3))
(check= (err '(1 2 3) 4) '(3 1 2))
#|
Make sure that err is efficient by timing it with a large n
and comparing the time with rr.

Replace the ...'s in the string below with the times you 
observed.
|#

(acl2::time$ (rr '(a b c d e f g) 10000000))
(acl2::time$ (err '(a b c d e f g) 10000000))

"rr took 2.22 seconds but err took 0.00 seconds"             

;; Here is a data definition for a list of Booleans. See Section 2.14 of the
;; lecture notes.

(defdata lob (listof boolean))

;; For example

(check= (lobp '(t nil t)) t)
(check= (lobp '(nil 1 t)) nil)

#|
We can use list of Booleans to represent natural numbers as follows.
The list

(nil nil t)

corresponds to the number 4 because the first nil is the "low-order"
bit of the number which means it corresponds to 2^0=1 if t and 0
otherwise. The next Boolean corresponds to 2^1=2 if t and 0 otherwise
and so on. So the above number is:

0 + 0 + 2^2 = 4.

As another example, 31 is

(t t t t t)

or

(t t t t t nil nil)

or ...

Define the function n-to-b that given a natural number, returns a list of
Booleans, of minimal length, corresponding to that number.
|#
(defunc haf (n)
  :input-contract (natp n)
  :output-contract (natp (haf n))
  (if (equal 0 (acl2::mod n 2))
    (/ n 2)
    (/ (- n 1) 2)))

(defunc n-to-b (n)
  :input-contract (natp n)
  :output-contract (lobp (n-to-b n))
  (if (equal n 0)
    ()
    (let ((digit (equal 1 (acl2::mod n 2))))
      (cons digit (n-to-b (haf n))))))
    

(check= (n-to-b 10) '(nil t nil t)) 
(check= (n-to-b 7) '(t t t)) 
(check= (n-to-b 4) '(nil nil t)) 
(check= (n-to-b 31) '(t t t t t)) 
(check= (n-to-b 0) ())

#|
Define the function b-to-n that given a list of Booleans, returns
the natural number corresponding to that list.
|#

(defunc b-to-n (l)
  :input-contract (lobp l)
  :output-contract (natp (b-to-n l))
  (if (endp l)
    0
    (+ (if (first l) 1 0) 
       (* 2 (b-to-n (rest l))))))

(check= (b-to-n '(nil t nil t)) 10)  
(check= (b-to-n '(t t t)) 7) 
(check= (b-to-n '(nil nil t)) 4) 
(check= (b-to-n '(t t t t t)) 31) 
(check= (b-to-n ()) 0)

#|

The permutations of a list are all the list you can obtain by swapping any two
of its elements. For example, starting with the list

(1 2 3)

I can obtain

(3 2 1)

by swapping 1 and 3.

So the permutations of (1 2 3) are

(1 2 3) (1 3 2) (2 1 3) (2 3 1) (3 1 2) (3 2 1)

Notice that if the list is of length n and all of its elements are distinct, it
has n! (n factorial) permutations.

Given a list, say (a b c d e), we can define any of its permutations using a
list of *distinct* positive integers from 1 to the length of the list, which
tell us how to reorder the elements of the list.  Let us call this list of
distinct positive integers an arrangement.  For example applying the
arrangement (5 1 3 2 4) to the list (a b c d e) yields (e a c b d).

Define the function find-arrangement that given two lists, either returns nil if
they are not permutations of one another or returns an arrangement such that
applying the arrangement to the first list yields the second list. Note that if
the lists have repeated elements, then more than one arrangement will work. In
such cases, it does not matter which of these arrangements you return.

|#
(defdata lon (listof nat))

(defunc member (x ls)
  :input-contract (listp ls)
  :output-contract (booleanp (member x ls))
  (if (endp ls) nil
    (if (equal x (first ls)) t
      (member x (rest ls)))))

(defunc find (x ys ans i)
  :input-contract (and (listp ys) (and (lonp ans) (natp i)))
  :output-contract (or (natp (find x ys ans i)) (equal (find x ys ans i) nil))
  (if (endp ys) nil
    (if (and (equal x (first ys)) (not (member i ans))) i
        (find x (rest ys) ans (+ i 1)))))

(defunc arrange (xs ys ans)
  :input-contract (and (and (listp xs) (listp ys)) 
                       (lonp ans))
  :output-contract (lonp (arrange xs ys ans))
  (if (endp xs) ans
    (let ((do (find (first xs) ys ans 1)))
      (if (equal do nil) nil
        (arrange (rest xs) ys  (app ans (list do)))))))

(defunc find-arrangement (x y)
  :input-contract (and (and (listp x) (listp y)))
  :output-contract (lonp (find-arrangement x y))
  (arrange x y ()))

(check= (find-arrangement '(a b c) '(a b b)) nil)
(check= (find-arrangement '(a b c) '(a c b)) '(1 3 2))
(check= (find-arrangement '(a a) '(a a)) '(1 2))
;; in the above check= you can use '(2 1) instead of '(1 2) if you wish
;; since both arrangements work

;; added tests
(check= (find-arrangement '() '()) nil)
(check= (find-arrangement '(1) '()) nil)
(check= (find-arrangement '() '(a b c)) nil)
(check= (find-arrangement '(a b b c) '(a b c)) nil)
(check= (find-arrangement '(a b c d e) '(e c d b a)) '(5 4 2 3 1))

#| 

 Part II:
 Exploring the ACL2s language.

 In this section, we are going to explore the ACL2s language as defined in the
 lecture notes. We are going to revisit some of the decisions made and we will
 consider certain "what if" scenarios. Make sure you read and understand the
 lecture notes really well.

|# 

#|

The built-in functions introduced in Section 2.2 are if and equal.
Without using if, but using equal, booleanp and the constants, which
of the following functions can you define?

and, implies, or, not, iff, xor

For each of the functions you can define, provide a definition using
the names

band, bimplies, bor, bnot, biff, bxor

If you cannot define one of the above functions, you do not need to do
anything.

The restriction on not using if applies only to the body of your function
definitions. You can use all the functions in the lecture notes (including
booleanp, if and and) for the input and output contracts.

|#

;; I don't think you can do and, implies, or

;; bnot
(defunc bnot (b)
  :input-contract (booleanp b)
  :output-contract (booleanp (bnot b))
  (equal b nil))

(check= (bnot t) nil)
(check= (bnot nil) t)

;; biff
(defunc biff (b1 b2)
  :input-contract (and (booleanp b1) (booleanp b2))
  :output-contract (booleanp (biff b1 b2))
  (equal b1 b2))

(check= (biff t t) t)
(check= (biff t nil) nil)
(check= (biff nil t) nil)
(check= (biff nil nil) t)

; bxor
(defunc bxor (b1 b2)
  :input-contract (and (booleanp b1) (booleanp b2))
  :output-contract (booleanp (bxor b1 b2))
  (bnot (equal b1 b2)))

(check= (bxor t t) nil)
(check= (bxor t nil) t)
(check= (bxor nil t) t)
(check= (bxor nil nil) nil)

#|
Consider the following function definition.
|#

(defunc iif (a b c)
  :input-contract (booleanp a)
  :output-contract t
  (if a b c))

#|
This is accepted by ACL2s. Suppose I define iif. Is it the case
that I can always use iif instead of if for subsequent function
definitions? Explain why or why not.

Yes, you can always use iif.

if has the signature: Bool x Any x Any -> Any
iff has the same signature, and since it calls if on the
same arguments, it will behave the same in every case
(iff is an eta-expansion of if)

|#

#|
In the lecture notes, unary-- was provided as a built-in function.
Explain why it is required or show that it is not really required.

When we say that unary-- is required, we mean that you cannot define
it in the ACL2s language (Bare Bones mode) using the built-in
functions in the lecture notes upto the end of Section 2.5, except
that you cannot use unary-- (obviously). You can define helper
functions, if needed.

If you think it is really required, then argue that it allows you to
do things that the other built-in functions do not. You do not need a
proof here, just a good argument in English.

If you think it is not required, show how to define it using the other
built-in functions.  Do this by providing a definition of my-unary--
that only uses the other built-in functions (except unary--) or
functions defined based on the other built-in functions.
You will do this in Beginner mode, as per the instructions above.

|#
(defunc my-unary-- (n)
  :input-contract (rationalp n)
  :output-contract (rationalp (my-unary-- n))
  (- 0 n))

(check= (my-unary-- -2/8) 1/4)
(check= (my-unary-- 5/6) -5/6)
(check= (my-unary-- 1) -1)
(check= (my-unary-- -81) 81)

#|

In the lecture notes, unary-/ was provided as a built-in function.
Explain why it is required or show that it is not really required.
Follow the instructions for unary--.

|#

(defunc my-unary-/ (n)
  :input-contract (and (rationalp n) (not (equal n 0)))
  :output-contract (rationalp (my-unary-/ n))
  (/ 1 n))

(check= (my-unary-/ 1) 1)
(check= (my-unary-/ -2/8) -4) 

#|

In the lecture notes, integerp was provided as a built-in function.
Explain why it is required or show that it is not really required.
Follow the instructions for unary--.

|#

(defunc my-integerp (x)
  :input-contract t
  :output-contract (booleanp (my-integerp x))
  (and (rationalp x)
       (equal 0 (acl2::mod x 1))))

(check= (my-integerp 0) t)
(check= (my-integerp 3) t)
(check= (my-integerp -30) t)
(check= (my-integerp 1/2) nil)
(check= (my-integerp t) nil)
(check= (my-integerp (my-integerp 0)) nil)
(check= (my-integerp (cons 2 nil)) nil)
(check= (my-integerp nil) nil)
(check= (my-integerp ()) nil)
(check= (my-integerp nil) nil)

#|
In the lecture notes, denominator was provided as a built-in function.
Explain why it is required or show that it is not really required.
Follow the instructions for unary--.
|#

;; This was my best attempt at a solution, but ACL2s wo't prove termination...
(defunc find-denom (rat i)
  :input-contract (and (rationalp rat) (natp i))
  :output-contract (natp (find-denom rat i))
  (if (my-integerp (* rat i)) i
    (find-denom rat (+ i 1))))

(defunc my-denominator (rat)
  :input-contract (rationalp rat)
  :output-contract (natp (my-denominator rat))
  (find-denom rat 1))


