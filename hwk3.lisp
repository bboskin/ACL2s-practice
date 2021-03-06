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

Instructions for programming problems:

For each function you define, you must provide a purpose statement,
contracts, a body, check= tests *and* test? forms (property-based
testing).  For each data definition you define, you must provide a
purpose statement, check= tests *and* test?  forms (property-based
testing).  This is in addition to the tests sometimes provided. Make
sure you produce sufficiently many new test cases and at least two
interesting test? forms. If we provide a purpose statement for you,
you do not need to provide another one.

For function definitions, make sure to provide as many tests as the
data definitions dictate. For example, a function taking two lists
should have at least 4 tests: all combinations of each list being
empty and non-empty.  Beyond that, the number of tests should reflect
the difficulty of the function. For very simple ones, the above
coverage of the data definition cases may be sufficient. For complex
functions with numerical output, you want to test whether it produces
the correct output on a reasonable number of inputs.

Use good judgment. For unreasonably few test cases and properties we
will deduct points.

We use the following ASCII character combinations to represent the Boolean
connectives:

  NOT     ~

  AND     &
  OR      v

  IMPLIES =>

  EQUIV   <=>
  XOR     +

The binding powers of these functions are listed from highest to lowest
in the above table. Within one group (no blank line), the binding powers
are equal. This is the same as in class.


|#

; not, and, or, implies, iff are already defined, but xor is not.
; This is a definition for xor.
(defunc xor (a b)
  :input-contract (and (booleanp a) (booleanp b))
  :output-contract (booleanp (xor a b))
  (not (equal a b)))

#|

PART I: PROPOSITIONAL LOGIC BASICS

A. Construct the truth table for the following Boolean formulas. Use
   alphabetical order for the variables in the formula, and create
   columns for all variables occurring in the formula AND for all
   intermediate subexpressions. For example, if your formula is

   (p => q) v r

   your table should have 5 columns: for p, q, r, p => q, and (p => q) v r .

For each formula, you also have to:

B. Indicate if is satisfiable, unsatisfiable, valid, or
   falsifiable (exactly two of these characterizations will hold!).

C. Indicate how many assignments satisfy the formula.

D. Simplify the formula: provide an alternative formula that is equivalent to
   the original formula and show equivalence by constructing a truth table for
   your formula whose final column has to be equal to the final column of the
   original truth table. If you wind up simplifying away a variable, include it
   in the truth table anyway so that you can compare the new truth table with
   the previous one. Your simplification should be minimal: that is,
   the number of symbols in your simplification should be as small as
   possible. 

E. Write a test? stating that the original formula and the simplified
   formula are equivalent. This should *not* be in a comment. ACL2s
   includes a decision procedure for validity, so you can use it as a
   SAT/validity solver to check your work. For example, you can use 
   it to check your characterization of formulas (part B, above).

Example question: p & (q v ~q)

A: (Notice that we place T's and F's under the operator associated with the
   column, e.g., in the final column, we are taking a conjunction.)

p | q | ~q | q v ~q | p & (q v ~q)
-----------------------------
T | T | F  |   T    |   T
T | F | T  |   T    |   T
F | T | F  |   T    |   F
F | F | T  |   T    |   F

B: satisfiable and falsifiable

C: 2

D: p 

p | q | p 
----------
T | T | T
T | F | T
F | T | F
F | F | F

E:
|#

(test? (implies (and (booleanp p)
                     (booleanp q))
                (equal (and p (or q (not q)))
                       p)))

#|
Question 1a: p v q <=> p <=> q

same as:((p v q) <=> p) <=> q
A:
p | q | (p v q) | (p v q) <=> p | ((p v q) <=> p) <=> q
F | F |    F    |      T        |         F
F | T |    T    |      F        |         F
T | F |    T    |      T        |         F
T | T |    T    |      T        |         T

B: satisfiable and falsifiable
C: 2
D: q (truth table above works)
E
|#

(test? (implies (and (booleanp p)
                     (booleanp q))
                (equal (equal (equal (or p q) p) q)
                       (and p q))))

#|
Question 1b: (p + q) & (r <=> ~q) => ~(~r & p)

A:
p | q | r | (p + q) | (r <=> ~q) | (~r & p) | (p + q) & (r <=> ~q) | (p + q) & (r <=> ~q) => ~(~r & p)
F | F | F |    F    |     F      |     F    |         F            |                T 
F | F | T |    F    |     T      |     F    |         F            |                T
F | T | F |    T    |     T      |     F    |         T            |                F
F | T | T |    T    |     F      |     F    |         F            |                T
T | F | F |    T    |     F      |     T    |         F            |                T
T | F | T |    T    |     T      |     F    |         T            |                F
T | T | F |    F    |     T      |     T    |         F            |                T
T | T | T |    F    |     F      |     F    |         F            |                T


B: satisfiable and falsifiable
C: 6
D: (p + r) v (p <=> q)
E:
|#

#|
Question 1c: ((p => q) + r) + (q <=> p v ~q)

A:...
B:...
C:...
D:...
E
|#


#| 

PART II: SECURITY

Consider a very old problem, secure communication.  This field is
called "cryptography" whose etymology originates from the Greek
words "crypto", meaning hidden, and "graphy", meaning writing.  For
example, various city-states in Ancient Greece were known to use
cryptographic methods to send secure messages in the presence of
adversaries.

We will formalize one-time pads, as described in Section 3.2 of the
lecture notes "The Power of Xor."  This involves writing code for
encrypting and decrypting messages, as well as formalizing and testing
properties that the code should enjoy.

One-time pads allow us to encrypt messages with "perfect" secrecy.
What this means is that if an adversary intercepts an encoded message,
they gain no information about the message, except for an upper bound
on the length of the message. 

If you look at most other types of encryption, e.g., RSA, then with
enough computational resources, an adversary can decrypt encoded
messages. The best known methods for breaking such encryption schemes
take time exponential in the size of the keys used. However, whether
this can be done in polynomial time is an open question.

Many movies have a red telephone that is used to connect the Pentagon
with the Kremlin. While there was no such red telephone, there was a
teletype-based encryption mechanism in place between the US and USSR,
which used one-time pads. This connection was established after the
Cuban missile crisis.

You can read more about the advantages and disadvantages of one-time
pads by searching online. We will see how to break one-time pads if
one is not careful. 

In fact, the ultimate goal of this exercise is for you to decrypt the
following intercepted communication that was sent from one hostile
actor to another. We can't reveal who the actors are, since you don't
yet have a high-enough clearance level.

|#

; We intercepted this message and want to decode it. A message is just
; a bit-vector, i.e., a sequence of bits which we represent as a list
; of Booleans.
(defconst *secret-message*
  '(NIL NIL T NIL T T T NIL NIL NIL NIL T T NIL NIL NIL T NIL NIL T NIL
    NIL T NIL NIL NIL T T NIL NIL T T NIL NIL T NIL T NIL T T T NIL
    T NIL NIL T NIL NIL T NIL T T NIL NIL NIL T NIL NIL T NIL T T T
    T NIL T T T NIL T T T T NIL T NIL NIL NIL T T NIL NIL NIL NIL T
    NIL T NIL T T NIL T NIL NIL T NIL T T T NIL NIL T T NIL T NIL
    NIL NIL T T NIL NIL NIL T NIL T NIL NIL T NIL NIL NIL NIL T NIL
    T T T NIL NIL T NIL T NIL T NIL T NIL T NIL T NIL NIL T T NIL
    NIL NIL T NIL T NIL NIL T NIL T NIL T NIL NIL T NIL NIL NIL T T
    T NIL T T NIL NIL T T T NIL NIL NIL T NIL T T NIL T T T NIL T
    NIL NIL T NIL NIL NIL T NIL T T T NIL NIL NIL NIL T T NIL NIL
    NIL T NIL NIL T NIL NIL T NIL NIL NIL NIL NIL T T T NIL NIL T T
    NIL T T T T T T T T T T T NIL NIL T NIL NIL T NIL T T T NIL T T
    T NIL T NIL NIL NIL T NIL NIL NIL NIL NIL NIL T T NIL T T T T
    NIL T NIL NIL NIL T NIL NIL T NIL T T T T NIL T T NIL NIL T T
    NIL T NIL NIL T NIL NIL T NIL T T NIL NIL NIL T T NIL T NIL NIL
    T NIL NIL T NIL NIL T T T T T NIL NIL T T NIL NIL T T NIL NIL T
    NIL T NIL NIL T T NIL T NIL NIL NIL T NIL T NIL NIL T NIL NIL T
    T NIL NIL T NIL T NIL T NIL T NIL T T NIL T T NIL T T NIL NIL T
    NIL T NIL NIL NIL T NIL NIL T NIL NIL T NIL NIL NIL T NIL T NIL
    T T NIL NIL T NIL T NIL T NIL T T T T NIL T NIL T NIL T NIL NIL
    T NIL NIL NIL T NIL NIL T T NIL NIL NIL T NIL T T NIL T T T T
    NIL NIL T T NIL NIL T T NIL T NIL)) 

; This is a data definition for a list of Booleans. 
(defdata lob (listof boolean))

; Question 2a
;
; Use check= to check that *secret-message* is of type lob.
; Use test? to check that *secret-message* is of type lob.
(check= (lobp *secret-message*) T)
(test? (lobp *secret-message*))

; Question 2b
;
; Notice that test? is more general than check=, as we can always turn
; a check= form into a test? form. Show this: given the form
; (check= X Y), what is an equivalent test?  form? Fill in the ... below.
; 
; (test? (equal X Y))

; Luckily our human intelligence has learned that the encrypted
; message is comprised of the following characters.
(defconst *chars*
  '(#\a #\b #\c #\d #\e #\f #\g #\h #\i #\j #\k #\l #\m #\n 
    #\o #\p #\q #\r #\s #\t #\u #\v #\w #\x #\y #\z
    #\A #\B #\C #\D #\E #\F #\G #\H #\I #\J #\K #\L #\M #\N 
    #\O #\P #\Q #\R #\S #\T #\U #\V #\W #\X #\Y #\Z #\Space 
    #\: #\- #\* #\/ #\Newline #\? #\, #\. #\' #\( #\)))

; This is a data definition for the legal characters. 
(defdata char (enum *chars*)) 

; Once decoded, a message will be a list of characters.  This is a
; data definition for a list of legal characters.
(defdata lochar (listof char))

; Our human intelligence has also learned how these characters are
; encoded as bit vectors.  First, since there are 64 characters that
; satisfy charp, any such character is represented by a list of 6
; Booleans.  Here is a data definition.  The name bv is an
; abbreviation of BitVector.
(defdata bv (list boolean boolean boolean boolean boolean boolean))

; This is a data definition for a list of BitVectors.
(defdata lobv (listof bv))

; We will generate a mapping from chars to bvs.  This mapping will be
; represented as a list of pairs.  Here are the data definitions.
; This is a data definition for a list whose first element is a char
; and whose second element if a bv.
(defdata pair (list char bv))

; This is a data definition for a list of pairs.
(defdata plist (listof pair))

; We will use program mode.
:program

; Question 2c
; 
; Define a function, char->bv-map that given chars, a list of type
; lochar, and bv, a bitvector (type bvp), returns a plist. The
; function works as follows: it creates a list of pairs whose first
; element contains the first element of chars and bv; its second
; element contains the second element of chars and bv+1; and so
; on. Given a bv, the first boolean in it is the high-order bit, e.g.,
; adding 1 to
;
; '(nil nil nil nil nil nil) yields
;
; '(nil nil nil nil nil t).
;
; Also adding 1 to '(t t t t t t) results in
;
; '(nil nil nil nil nil nil) (since bv's have six bits).

(defunc reverse (ls)
  :input-contract (listp ls)
  :output-contract (listp (reverse ls))
  (cond ((endp ls) nil)
        (t (app (reverse (rest ls)) (list (first ls))))))

(defunc bv-add1-aux (bits)
  :input-contract (listp bits)
  :output-contract (listp (bv-add1-aux bits))
  (cond ((equal bits nil) ())
        ((first bits) (cons nil (bv-add1-aux (rest bits))))
        ((not (first bits)) (cons t (rest bits)))
        (t bits)))

(defunc bv-add1 (bits)
  :input-contract (bvp bits)
  :output-contract (bvp (bv-add1 bits))
  (reverse (bv-add1-aux (reverse bits))))

(check= (bv-add1 '(t t t t t t)) '(nil nil nil nil nil nil))
(check= (bv-add1 '(t t nil nil nil t)) '(t t nil nil t nil))
(check= (bv-add1 '(t nil t nil t t)) '(t nil t t nil nil))

(defunc char->bv-map (chars bv)
   :input-contract (and (locharp chars) (bvp bv))
   :output-contract (plistp (char->bv-map chars bv))
   (cond ((endp chars) ())
         (t (cons (list (first chars) bv) (char->bv-map (rest chars) (bv-add1 bv))))))

(check= (first (char->bv-map *chars* '(nil nil nil nil nil nil)))
        '(#\a (nil nil nil nil nil nil)))

(check= (nth 54 (char->bv-map *chars* '(nil nil nil nil nil nil)))
        '(#\- (t t nil t t nil)))

(check= (nth 48 (char->bv-map *chars* '(t nil t nil t nil)))
        '(#\W (nil t t nil t nil)))

; Here is the mapping between chars and bvs.
(defconst *bv-char-map*
  (char->bv-map *chars* '(nil nil nil nil nil nil)))

; We often define functions that may return some type, say a pair, but
; they can also return a non-pair default value, often nil. Instead of
; using complex input/output contracts, we can use contracts
; containing just recognizers by defining an appropriate data type.
; This is a data type that is either ni or a pair.
(defdata pair-nil (oneof nil pair))

; Question 2d
; 
; Define a function, find-char, that given a char, c, and a plist, p,
; returns a pair that has c as its first element or nil if no such
; pair exists. Make sure that the recognizer you use for the output
; contract is the strongest recognizer that works, that is it
; recognizes as few elements from the universe as possible.

(defunc find-char (c p)
  :input-contract (and (charp c) (plistp p))
  :output-contract (pair-nilp (find-char c p))
  (cond ((endp p) nil)
        ((equal (first (first p)) c) (first p))
        (t (find-char c (rest p)))))

(check= (find-char #\W *bv-char-map*)
        '(#\W (t t nil nil nil nil)))

; Question 2e
; 
; Define a function, find-bv, that given a bv, b, and a plist, p,
; returns a pair that has b as its second element or nil if no such
; pair exists. Make sure that the recognizer you use for the output
; contract is the strongest recognizer that works, that is it
; recognizes as few elements from the universe as possible.

(defunc find-bv (b p)
  :input-contract (and (bvp b) (plistp p))
  :output-contract (pair-nilp (find-bv b p))
  (cond ((endp p) nil)
        ((equal (first (rest (first p))) b) (first p))
        (t (find-bv b (rest p)))))

(check= (find-bv '(t t nil nil nil nil) *bv-char-map*)
        '(#\W (t t nil nil nil nil)))

; Next we want to define functions that given a char return the
; corresponding bv and the other way around. These functions will use
; find-char and find-bv and will use the constant *bv-char-map*.

; Question 2f
;
; Define char-bv, a function that given a char as input returns the
; corresponding bv, under *bv-char-map*. Notice that a bv must be
; returned (there is no nil option).

(defunc char-bv (c)
   :input-contract (charp c)
   :output-contract (bvp (char-bv c))
   (first (rest (find-char c *bv-char-map*)))) 

(check= (char-bv #\W) '(t t nil nil nil nil))

; Question 2g
;
; Define bv-char, a function that given a bv as input returns the
; corresponding char, under *bv-char-map*. Notice that a char must be
; returned (there is no nil option).

(defunc bv-char (b)
  :input-contract (bvp b)
  :output-contract (charp (bv-char b))
  (first (find-bv b *bv-char-map*)))

(check= (bv-char '(t t nil nil nil nil)) #\W)

; Our human intelligence has determined that the hostile actors are
; using one-time pads, so we will define functions to help us encrypt
; and decrypt one-time pads.

; Question 2h
; 
; Define a function that xor's bit vectors.  Function xor-bv takes 2
; lob's (b1 and b2) as input and returns an lob as output. It works by
; xor'ing the nth bit of b1 with the nth bit of b2. The length of the
; output should be equal to the minimum of the lengths of the inputs,
; i.e., once one of b1, b2 are empty, we stop recurring.
(defunc xor-bv (b1 b2)
  :input-contract (and (lobp b1) (lobp b2))
  :output-contract (lobp (xor-bv b1 b2))
  (cond ((endp b1) nil)
        ((endp b2) nil)
        (t (let ((p (first b1)) (q (first b2)) (res (xor-bv (rest b1) (rest b2))))
             (cond ((and p q) (cons nil res))
                   ((and (not p) (not q)) (cons nil res))
                   (t (cons t res)))))))

(check= (xor-bv '(t nil t nil t t) '(t t nil nil nil t))
        '(nil t t nil t nil))
(check= (xor-bv '(t nil t nil t t nil t) '(t t nil nil nil t))
        '(nil t t nil t nil))

; Question 2i
;
; Even though xor-bv takes as input lob's as input, if we give it
; bv's an input it should return bv's as output. Write a test
; to check this. Also, make sure you understand why we did not
; use bv in the input/output contracts (try it).

(test? (implies (and (bvp b1) (bvp b2))
                (bvp (xor-bv b1 b2))))

; Question 2j
; 
; Now let's define a function to encrypt a single character,
; given a bitvector. Function encrypt-char, given c, a char, and b, a
; bv, returns the bv obtained by turning c into a bitvector and xor'ing
; it with b.

(defunc encrypt-char (c b)
  :input-contract (and (charp c) (bvp b))
  :output-contract (bvp (encrypt-char c b))
  (xor-bv (char-bv c) b))

(check= (encrypt-char #\B '(nil t nil t nil t)) '(nil nil t t t nil))

; Question 2k
; 
; We will now define a function that given, m, of type lochar (think
; of m as our message, which is a list of chars) and s, of type lobv
; (think of s as our secret key, a list of bvs), returns an lobv, the
; result of encrypting every character in the message with the
; corresponing bit vector in s. We will require that s, the secret
; key, is at least as long as m, the message. The output contract
; should state that what we return is of type lobv and has the same
; length as the original message.

(defunc encrypt (m s)
  :input-contract (and (and (locharp m) (lobvp s))
                       (>= (len s) (len m)))
  :output-contract (lobvp (encrypt m s))
  (cond ((endp m) nil)
        (t (cons (encrypt-char (first m) (first s))
                 (encrypt (rest m) (rest s))))))

; Question 2l
; 
; Now let's define a function to decrypt a bitvector, given a
; bitvector. Function decrypt-bv, given b, a bv, and s, a bv (the
; secret), returns the char obtained by xor'ing b with s and turning
; that into a char.

(defunc decrypt-bv (b s)
  :input-contract (and (bvp b) (bvp s))
  :output-contract (charp (decrypt-bv b s))
  (bv-char (xor-bv b s)))

; Question 2m
; 
; We will now define a function that given, e, of type lobv (think of
; e as the encrypted message, which is a list of bv's) and s, of type
; lobv (think of s as our secret key, a list of bvs), returns an
; lochar, the result of decrypting every character in the message with
; the corresponing bit vector in s. We will require that s, the secret
; key, is at least as long as e, the encrypted message. The output
; contract should state that what we return is an lochar and has the
; same length as e, similarly to what we did with encrypt.
(defunc decrypt (e s)
  :input-contract (and (and (lobvp e) (lobvp s))
                       (>= (len s) (len e)))
  :output-contract (locharp (decrypt e s))
  (cond ((endp e) nil)
        (t (cons (decrypt-bv (first e) (first s))
                 (decrypt (rest e) (rest s))))))

; Question 2n
; 
; Write a test? to make sure encrypt and decrypt work as expected:
; that if m (the message) is a lochar and s is a lobv (the secret)
; then if we use s to encrypt m and then use s to decrypt that, we get
; the original message back. Add any other hypotheses you may need.
(test? (implies (and (locharp m) (lobvp s) (>= (len s) (len m)))
                (equal m (decrypt (encrypt m s) s))))

; Question 2o
; 
; Write a test? to see that one-time pads provide "perfect" secrecy:
; if we have an lobv, e, which is an encrypted message, then for every
; lochar m, an arbitrary message of the same length, there is some
; secret s that when used to decode e gives us m. That is, without the
; secret, we have no information about the contents of the message.
; We haven't seen how to say "there exists", so instead, construct
; the secret using existing functions.
(test? (implies (and (lobvp e) (locharp m) (lobvp s)
                     (equal (len e) (len m))
                     (equal (len e) (len s))
                     (equal s (encrypt m e)))
                (equal m (decrypt e s))))
; Question 2o shows that even thought we know that the
; hostile actors are using one-time pads and each sequence of 6 bits
; corresponds to a character, then without the secret, we cannot
; determine what the message says.
; 
; All hope is not lost. Human intelligence tells us that the hostile
; actors did not take CS 2800, and weren't trained to think carefully
; about the correctness of their code, so they did not recognize that
; their secret cannot be reused. What they are doing is using the same
; 6 bit secret to encrypt all the characters in their message.
;
; Human intelligence tried, but was not able to determine what the
; secret is, so you have to figure out how to break their encyption.

; Question 2p
;
; The first thing to do is to turn *secret-message* from a lob into a
; lobv, so that we can operate on a character at a time.  Write a
; function lob->lobv that takes as input l, a lob, and returns an lobv
; as output. The function takes six Booleans at a time and turns them
; into a bv. If we're left with less than 6 Booleans, after processing
; all but the last sequence of Booleans, then we add nils at the end to
; create a bv.
; 
; Define a function lob->lobv that takes as input l, a lob, and
; returns a lobv, as described above. 
;
; Feel free to use the copy function below as a helper function.

(defunc copy (e n)
  :input-contract (natp n)
  :output-contract t
  (if (equal n 0)
    nil
    (cons e (copy e (- n 1)))))

(defunc take (l c)
  :input-contract (and (listp l) (natp c))
  :output-contract (and (listp (take l c))
                        (<= (len (take l c)) c))
  (cond ((endp l) nil)
        ((equal c 0) nil)
        (t (cons (first l) (take (rest l) (- c 1))))))

(defunc drop (l c)
  :input-contract (and (listp l) (natp c))
  :output-contract (listp (drop l c))
  (cond ((endp l) nil)
        ((equal c 0) l)
        (t (drop (rest l) (- c 1)))))

(defunc lob->lobv (l)
  :input-contract (lobp l)
  :output-contract (lobvp (lob->lobv l))
  (if (endp l) nil
    (let ((n (len l)))
      (if (< n 6) (list (append l (copy nil (- 6 n))))
        (cons (take l 6) (lob->lobv (drop l 6)))))))
             
  
(check= (lob->lobv '())
        '())

(check= (lob->lobv '(t t t t t t nil nil nil nil nil nil))
        '((t t t t t t) (nil nil nil nil nil nil)))

(check= (lob->lobv '(t))
        '((t nil nil nil nil nil)))

(defconst *secret-message-in-chars*
  (lob->lobv *secret-message*))

; Question 2q
;
; Here's the plan for breaking the encryption. You are going to
; generate all possible secrets (there are 2^6=64 of them). Then, you
; will decode *secret-message* with each of these secrets. To do
; that, you will create a list containing (len *secret-message*)
; copies of the potential secret. All but one of those should be
; gibberish. To make it easier to read the messages, we will convert
; them to strings. Here is an example of how you can do that in ACL2s.

(acl2::coerce
 (decrypt *secret-message-in-chars*
          (copy '(nil nil nil nil nil nil) (len *secret-message-in-chars*)))
 'string)

; Define game-over, a function that decrypts *secret-message-in-chars*
; using all possible values for the secret. It should return a list of
; pairs consisting of the value of s under consideration and the
; decoded string (see above).  Hint: define a helper function that is
; called with '(nil nil nil nil nil nil) and creates the pair
; corresponding to its input and if its input is not '(t t t t t t),
; it adds 1 to it and recurs.  Adding 1 to a bv is described in
; Question 2c. You do not have to provide any check= or test?  forms
; for this definition.
(defdata lores (listof (cons lobv string)))

(defunc game-over-aux (c)
  :input-contract (bvp c)
  :output-contract (loresp (game-over-aux c))
  (if (equal c '(t t t t t t)) nil
    (cons (let ((s (copy c (len *secret-message-in-chars*))))
            (cons s (acl2::coerce
                     (decrypt *secret-message-in-chars* s)
                     'string)))
          (game-over-aux (bv-add1 c)))))

(defunc game-over ()
  :input-contract t
  :output-contract t
  (game-over-aux '(nil nil nil nil nil nil)))

; Let's see the fruit of our labor.
(game-over)#|ACL2s-ToDo-Line|#


; Question 2r
;
; Well, what is the secret message?
;
; The message is

;"The Quick Brown Fox Jumped Over The Lazy Dog's Back. 
;Quaecumque Sunt Vera."


; Question 2s
;
; Human intelligence indicated that the hostile actors may have
; been recruited from a US university. Can you tell which one?
;
; The university is
; Northwestern!

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Feedback (5 points)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|

Each week we will ask a couple questions to monitor how the course is
progressing and to solicit suggestions for improvement.

Please fill out the following form.

https://docs.google.com/forms/d/e/1FAIpQLScZ-HpeLPfVq3QdwosiiCqiHnpSYYiOlAU4ZVc_1Bv6T2_cZA/viewform

Feedback is anonymous and each team member should fill out
the form (only once per person).

After you fill out the form, write your name below in this file, but
not on the questionnaire. We have no way of checking if you submitted
the file, but by writing your name below you are claiming that you
did, and we'll take your word for it.

The questionnaire is worth 5 points (hence the rest of the homework
problems are worth 95 points). 

The following team members filled out the feedback survey provided by
the link above (replace the ...'s with the names of the team members
who filled out the questionnaire).

<Firstname> <LastName>
---------------------------------------------
...

|#
