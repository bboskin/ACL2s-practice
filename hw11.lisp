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
#|
For this homework you will need to use ACL2s and you will need
to be in ACL2s mode.

IMPORTANT: Since we are in ACL2s mode, there are a few things we have
to understand.

1. We can construct cons pairs such as (cons 1 2)
   and we will take advantage of that.

2. The functions car and cdr are used to extract the 
   first and second parts of a cons, e.g.,

   (car (cons 1 2)) = 1
   (cdr (cons 1 2)) = 2

3. We have access to a collection of macros such as

  (cddr x) = (cdr (cdr x))
  (cadr x) = (car (cdr x))
  (caaddr x) = (car (car (cdr (cdr x))))

  and so on.

4. Do not use listp. Instead you have to use true-listp

Technical instructions:
 
- Open this file in ACL2s as hwk11.lisp

- Make sure you are in ACL2s mode. This is essential! Note that you
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

- When done, save your file and submit it as hwk11.lisp

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

THE GOAL

The goal of this homework is to develop a compiler that takes
expressions like this:

(sq ((inc x) * ((sq 12) + (sq y))))

and generates an equivalent program for a stack machine, say

((LOAD X)
 (PUSH 1)
 (ADD)
 (PUSH 12)
 (DUP)
 (MUL)
 (LOAD Y)
 (DUP)
 (MUL)
 (ADD)
 (MUL)
 (DUP)
 (MUL))

What we want to prove is that no matter what input is given to the
compiler, as long as it is a well-formed expression, then the compiler
generates an equivalent well-formed program.

So, notice that we have to define well-formed expressions and
programs. This is the *syntax* of expressions and programs.

What does it mean that the expression and the program are equivalent?
This is harder to answer and it requires that we define the semantics
of expressions and programs. Here's how we do that. 

We mean that given any assignment, a mapping from variables to values,
evaluating the expression under that assignment gives us a number and
if we evaluate the compiler-generated program on the empty stack, we
get a stack with one element in it, the same number.

You will be asked to come up with the specification as part of this
homework.

We start by defining expressions. Notice how I do this. I use a
mutually recursive data definition because it makes function
definitions nicer later.

|#

(defdata 
  (expr (oneof integer 
               symbol 
               inc-expr
               sq-expr
               +-expr
               *-expr))
  (inc-expr (list 'inc expr))
  (sq-expr  (list 'sq expr))
  (+-expr   (list expr '+ expr))
  (*-expr   (list expr '* expr)))

#|

Gain some familiarity with exprp. Try the following and your own
examples (you do not have to submit them as part of the homework).

(exprp 12)
(exprp 'a)
(exprp '(inc x))
(exprp '(sq (inc 12)))
(exprp '((inc 12) * (sq x)))

Here are some basic relationships between the data definitions.  These
require proof. The forms below state that various data definitions are
disjoint. You do not have to do anything here.

|#

(defdata-disjoint inc-expr sq-expr)
(defdata-disjoint inc-expr +-expr
  :hints (("goal" :expand (inc-exprp defdata::x))))
(defdata-disjoint inc-expr *-expr
  :hints (("goal" :expand (inc-exprp defdata::x))))
(defdata-disjoint sq-expr +-expr
  :hints (("goal" :expand (sq-exprp defdata::x))))
(defdata-disjoint sq-expr *-expr
  :hints (("goal" :expand (sq-exprp defdata::x))))
(defdata-disjoint +-expr *-expr
  :hints (("goal" :expand (*-exprp defdata::x))))

#|

Here's my plan. I want to turn off the definitions of the types, so I
want to collect together a number of rules that allow the theorem
prover to reason at a higher level, i.e., to not have to expand out
definitions to reason about the types I defined. This is part of my
theorem proving strategy.

How did I come up with the theorems?  I let ACL2s show me what it
needed, but I also thought about my rewrite strategy, e.g., I wrote
theorems that should apply before destructor elimination.  The details
are not relevant for this assignment. I include them here for those of
you that want to learn how to use the theorem prover.

|#

(defthm exprp-car
  (implies (and (exprp x)
                (not (equal (car x) 'inc))
                (not (equal (car x) 'sq)))
           (exprp (car x)))
  :rule-classes :type-prescription)
 
(defthm exprp-car-2
  (implies (and (exprp x)
                (consp (cddr x)))
           (exprp (car x)))
  :rule-classes :type-prescription)
 
(defthm consp-exprp
  (implies (and (exprp x)
                (not (atom x))
                (not (inc-exprp x))
                (not (sq-exprp x)))
           (consp (cddr x)))
  :rule-classes :type-prescription)
 
(defthm consp-*-exprp
  (implies (*-exprp x)
           (consp (cddr x)))
  :rule-classes :type-prescription)
 
(defthm consp-+-exprp
  (implies (+-exprp x)
           (consp (cddr x)))
  :rule-classes :type-prescription)
 
(defthm +-exprp-car
  (implies (+-exprp x)
           (exprp (car x)))
  :rule-classes :type-prescription)
 
(defthm +-exprp-caddr
  (implies (+-exprp x)
           (exprp (caddr x)))
  :rule-classes :type-prescription)
 
(defthm *-exprp-car
  (implies (*-exprp x)
           (exprp (car x)))
  :rule-classes :type-prescription)
 
(defthm *-exprp-caddr
  (implies (*-exprp x)
           (exprp (caddr x)))
  :rule-classes :type-prescription)
 
(defthm sq-exprp-cadr
  (implies (sq-exprp x)
           (exprp (cadr x)))
  :rule-classes :type-prescription)
 
(defthm inc-exprp-cadr
  (implies (inc-exprp x)
           (exprp (cadr x)))
  :rule-classes :type-prescription)
 
(defthm exprp-cases
  (implies (and (exprp x)
                (not (integerp x))
                (not (symbolp x))
                (not (inc-exprp x))
                (not (sq-exprp x))
                (not (*-exprp x)))
           (+-exprp x))
  :rule-classes :type-prescription)
 
(defthm exprp-expand
  (equal (exprp x)
         (or (integerp x)
             (symbolp x)
             (inc-exprp x)
             (sq-exprp x)
             (*-exprp x)
             (+-exprp x)))
  :rule-classes ((:compound-recognizer) (:rewrite)))

; I now disable the definitions
(in-theory (disable exprp inc-exprp sq-exprp *-exprp +-exprp))

#|

Next, we define an assignment, which is a mapping from
symbols (variables) to integers.

|#

(defdata assignment (alistof symbol integer))

; Notice that an alist is a list of cons pairs!

(check= (assignmentp '((x . 3) (y . 5) (z . 2))) t)
(check= (assignmentp '((x . 3) (y . 5) (2 . z))) nil)

#|
Q1.

Define the function lookup that given a symbol (a variable) and an
assignment, looks up the value of the variable in an assignment.  If
the variable is not in the assignment, return a default value of 0.

Note you can use any of the following if you think
you have a valid definition and ACL2s can't prove it.

(set-defunc-termination-strictp nil)
(set-defunc-function-contract-strictp nil)
(set-defunc-body-contracts-strictp nil)
(program)

|#

(defunc lookup (x alist)
  :input-contract (and (symbolp x) (assignmentp alist))
  :output-contract (integerp (lookup x alist))
  (cond ((endp alist) 0)
        ((equal (caar alist) x) (cdar alist))
        (t (lookup x (cdr alist)))))

(check= (lookup 'z '((x . 3) (y . 5) (z . 2))) 2)
(check= (lookup 'a '((x . 3) (y . 5) (z . 2))) 0)

#|
Q2.

Now define a function to evaluate an expression under an assignment.

Notice how we are doing this.  We use the data types defined above to
check what kind of expression we have.

|#

(defunc evaluate (x alist)
  :input-contract (and (exprp x) (assignmentp alist))
  :output-contract (integerp (evaluate x alist))
  (cond
   ((integerp x) x)
   ((symbolp x) (lookup x alist))
   ((inc-exprp x) (+ 1 (evaluate (cadr x) alist)))
   ((sq-exprp x) (expt (evaluate (cadr x) alist) 2))
   ((*-exprp x) (* (evaluate (car x) alist)
                   (evaluate (caddr x) alist)))
   ;; Added a case for +
   ((+-exprp x) (+ (evaluate (car x) alist)
                   (evaluate (caddr x) alist)))
   (t 0)))

(check= (evaluate 3 '((a . 2))) 3)
(check= (evaluate 'a '((a . 2))) 2)
(check= (evaluate '(sq a) '((a . 2))) 4)
(check= (evaluate '(inc a) '((a . 2))) 3)
(check= (evaluate '(4 + a) '((a . 2))) 6)
(check= (evaluate '(4 * a) '((a . 2))) 8)
(check= (evaluate '((3 * b) + a)   '((a . 7) (b . 4))) 19)


#|

We defined what an expression is and what it means.

Next, we define a stack-based machine.

|#

(defdata stack (listof integer))
(defdata non-empty-stack (cons integer stack))
(defdata empty-stack nil)


(check= (stackp '()) t)
(check= (empty-stackp '()) t)
(check= (non-empty-stackp '()) nil)

(check= (stackp '(1 2 -11 4)) t)
(check= (empty-stackp '(1 2 -11 4)) nil)
(check= (non-empty-stackp '(1 2 -11 4)) t)

(check= (stackp '(1 2/3 -11 4)) nil)
(check= (empty-stackp '(1 2/3 -11 4)) nil)
(check= (non-empty-stackp '(1 2/3 -11 4)) nil)

; property-based testing examples
(test? (implies (non-empty-stackp x)
                (stackp x)))

(test? (implies (empty-stackp x)
                (stackp x)))

; Here are some properties that are theorems
(defdata-subtype non-empty-stack stack)
(defdata-subtype empty-stack stack)
(defdata-disjoint empty-stack non-empty-stack)

; Notice that I will allow one to pop an empty stack.
; The cdr of nil is nil.
(defunc pop-stack (stk) 
  :input-contract (stackp stk)
  :output-contract (stackp (pop-stack stk))
  (cdr stk))

; Notice that the top of an empty stack is 0
(defunc top-stack (stk)
  :input-contract (stackp stk)
  :output-contract (integerp (top-stack stk))
  (if (consp stk) (car stk) 0))

; Notice the output contract
(defunc push-stack (val stk) 
  :input-contract (and (stackp stk) (integerp val))
  :output-contract (non-empty-stackp (push-stack val stk))
  (cons val stk))

#|

Next, we define what an instruction is.  Again, we use multiple
data definitions.

|#

(defdata load-instr (list 'load symbol))
(defdata push-instr (list 'push integer))
(defdata dup-instr '(dup))
(defdata add-instr '(add))
(defdata mul-instr '(mul))
(defdata instr (oneof load-instr push-instr dup-instr add-instr mul-instr))

(check= (instrp '(load x)) t)
(check= (instrp '(push x)) nil)
(check= (instrp '(push 10)) t)
(check= (instrp '(dup)) t)
(check= (instrp '(mul x y)) nil)

#|
Q3.

Define how to execute a single instruction, given a memory (an
assignment) and a stack. 

Again, note that we will use our data-definitions to make this easy
note the last case of the cond.

Only use the stack-modifying functions we defined above, e.g., instead
of cons, use push-stack. That gives us confidence that we are not
manipulating a stack in a way that violates the contracts of the
stack-modifying functions.

A load instruction pushes the value of the variable onto the stack.

A push instruction pushes the integer onto the stack.

A dup instruction duplicates the top of the stack.

An add instruction replaces the two top elements of the stack with
their sum.

A mul instruction replaces the two top elements of the stack with 
their product.
|#

(defunc execute (instr alist stk)
  :input-contract (and (instrp instr) (assignmentp alist) (stackp stk))
  :output-contract (stackp (execute instr alist stk))
  (cond
   ((load-instrp instr)
    (push-stack (lookup (cadr instr) alist) stk))
   ((push-instrp instr)
    (push-stack (cadr instr) stk))
   ((dup-instrp instr)
    (push-stack (top-stack stk) stk))
   ((add-instrp instr)
    (let ((n (top-stack stk))
          (s1 (pop-stack stk)))
      (let ((m (top-stack s1))
            (s2 (pop-stack s1)))
        (push-stack (+ n m) s2))))
   (t
    (let ((n (top-stack stk))
          (s1 (pop-stack stk)))
      (let ((m (top-stack s1))
            (s2 (pop-stack s1)))
        (push-stack (* n m) s2))))))

(check= (execute '(load a)  '((a . 7) (b . 4))   '(3 2 1))
        '(7 3 2 1))
(check= (execute '(push 5)  '((a . 7) (b . 4))   '(3 2 1))
        '(5 3 2 1))
(check= (execute '(dup)     '((a . 7) (b . 4))   '(3 2 1))
        '(3 3 2 1))
(check= (execute '(add)     '((a . 7) (b . 4))   '(3 2 1))
        '(5 1))
(check= (execute '(mul)     '((a . 7) (b . 4))   '(3 2 1))
        '(6 1))

#|

Next, we define a function that runs a program, but first, we need to
define what a program is: it is a list of instructions.

|#

(defdata program (listof instr))

#|
Q4.

Define m, a function that runs a program.  Just execute all of the
instructions.

|#
(defunc m (program alist stk)
  :input-contract (and (programp program)
                       (assignmentp alist)
                       (stackp stk))
  :output-contract (stackp (m program alist stk))
  (cond ((endp program) stk)
        (t (m (cdr program) alist (execute (car program) alist stk)))))

(check=
 (m '((load a) (dup) (add)) '((a . 7) (b . 4))  '(1 2 3))
 '(14 1 2 3))

#|

Q5.

Now, define the  compiler.

|#

(defunc compile-expression (x)
  :input-contract (exprp x)
  :output-contract (programp (compile-expression x))
  (cond
   ((integerp x) (list (list 'push x)))
   ((symbolp x) (list (list 'load x)))
   ((inc-exprp x)
    (append (compile-expression (cadr x)) '((push 1) (add))))
   ((sq-exprp x)
    (append (compile-expression (cadr x)) '((dup) (mul))))
   ((+-exprp x)
    (append (compile-expression (car x)) 
            (compile-expression (caddr x))
            '((add))))
   (t 
    (append (compile-expression (car x)) 
            (compile-expression (caddr x))
            '((mul))))))

(check=
 (compile-expression '(sq (inc (a + (3 * b)))))
 '((load a)
   (push 3)
   (load b)
   (mul)
   (add)
   (push 1)
   (add)
   (dup)
   (mul)))

#|
Q6.

Now, what does it mean for the compiler to be correct?

Informally it means that if:

   x is an expr
   a is an assignment
   s is an empty stack

Then if I run the compiler on x to generate a program
and then I run that program, I back a stack
with a single element in it: the result of evaluating
x under a.

Formalize this conjecture.
|#

;; A useful fact about m
(defthm m-append-dist
  (implies (and (programp p1)
                (programp p2)
                (assignmentp a)
                (stackp s))
           (equal (m (append p1 p2) a s)
                  (m p2 a (m p1 a s)))))

#|


(implies (and (exprp x) (assignmentp a) (empty-stackp s))
         (let ((res (m (compile-expression x) a s)))
           (and (equal (evaluate x a)
                       (top-stack res))
                (empty-stackp (pop-stack res)))))
    
Extra Credit. (Hard)

Prove the conjecture above using a paper-pencil proof.

You can also submit an ACL2s proof, but we recommend that you come up
with a plan, as I showed in class if you want to try this.

Theorem 1 (easier): performing m on a compiled 
expression yeilds a stack with 1 more element than
the initial stack

(implies (and (exprp x) (assignmentp a) (stackp s))
              (equal (stack-len (m (compile-expression x) a s))
                     (+ 1 (stack-len s))))

This will be proven using the induction scheme of (evaluate x a).

1. (implies (integerp x) T1)

C1. (integerp x)
C2. (assignmentp a)
C3. (stackp s)
--------------------

(equal (stack-len (m (compile-expression x) a s))
       (+ 1 (stack-len s)))
={Def compile-expression, C1}
(equal (stack-len (m (list (list 'push x)) a s))
       (+ 1 (stack-len s)))
={Def m}
(equal (stack-len (m nil a (execute (list 'push x) a s)))
       (+ 1 (stack-len s)))
={Def m}
(equal (stack-len (execute (list 'push x) a s))
       (+ 1 (stack-len s)))
={Def execute}
(equal (stack-len (push-stack x s))
       (+ 1 (stack-len s)))
={Def push-stack}
(equal (stack-len (cons x s)) (+ 1 (stack-len s)))
={Def stack-len}
(equal (+ 1 (stack-len s)) (+ 1 (stack-len s)))
={equal axiom}
t
|#

(defthm integer-case1
  (implies (and (exprp x) (integerp x) (assignmentp a) (stackp s))
           (equal (len (m (compile-expression x) a s))
                  (+ 1 (len s)))))

#|
2. (implies (symbolp x) T1)

C1. (symbolp x)
C2. (assignmentp a)
C3. (stackp s)
--------------------

(equal (stack-len (m (compile-expression x) a s))
       (+ 1 (stack-len s)))
={Def compile-expression, C1}
(equal (stack-len (m (list (list 'load x)) a s))
       (+ 1 (stack-len s)))
={Def m}
(equal (stack-len (m nil a (execute (list 'load x) a s)))
       (+ 1 (stack-len s)))
={Def m}
(equal (stack-len (execute (list 'load x) a s))
       (+ 1 (stack-len s)))
={Def execute}
(equal (stack-len (push-stack (lookup x a) s))
       (+ 1 (stack-len s)))
={Def push-stack}
(equal (stack-len (cons (lookup x a) s)) (+ 1 (stack-len s)))
={Def stack-len}
(equal (+ 1 (stack-len s)) (+ 1 (stack-len s)))
={equal axiom}
t
|#

(defthm symbol-case1
  (implies (and (exprp x) (symbolp x) (assignmentp a) (stackp s))
           (equal (len (m (compile-expression x) a s))
                  (+ 1 (len s)))))
#|
3. (implies (not (exprp x)) T1)
Reductio ad absurdum. Done.
|#
(defthm unsat-case1
  (implies (and (exprp x) (not (exprp x)) (assignmentp a) (empty-stackp s))
           (equal (len (m (compile-expression x) a s)) 
                  (+ 1 (len s)))))
#|
3. (implies (and (inc-exprp x) 
                 (T1 | ((x (cadr x))))) 
            T1)
  
C1. (exprp x)            
C2. (inc-exprp x)
C3. (assignmentp a)
C4. (stackp s)
C5. (implies (and (exprp (cadr x))
                  (assignmentp a)
                  (stackp s))
             (let ((r (m (compile-expression (cadr x)) a s)))
               (equal (stack-len r) (+ 1 (stack-len s)))))
--------------------
C6. (exprp (cadr x)) {Def C1, C2}
C7. (equal (stack-len (m (compile-expression (cadr x)) a s)) 
           (+ 1 (stack-len s))) {MP, C6, C3, C4}
C8. (programp (compile-expression (cadr x))) 
    {Contract thm, compile-expression, C6}
C9. (>= (stack-len (m (compile-expression (cadr x)) a s)) 1) {Arith, C7}

(equal (stack-len (m (compile-expression x) a s))
       (+ 1 (stack-len s)))
={Def compile-expression, C2}
(equal (stack-len (m (append (compile-expression (cadr x)) 
                             '((push 1) (add))) 
                     a s))
       (+ 1 (stack-len s)))
={push-add, C8, C3, C4, C9}
(equal (stack-len (m (compile-expression (cadr x)) a s))
       (+ 1 (stack-len s)))
={C7}
t

|#
(defthm push-add
  (implies (and (programp p)
                (assignmentp a)
                (stackp s)
                (>= (len (m p a s)) 1))
           (equal (len (m (append p '((push 1) (add))) a s))
                  (len (m p a s)))))

(defthm m-nil-a-s=s
  (implies (and (assignmentp a)
                (stackp s))
           (equal (m nil a s)
                  s)))

(defthm push-incr
  (implies (and (integerp i)
                (stackp s))
           (equal (len (push-stack i s))
                  (+ 1 (len s)))))

(defthm cdr-1
  (implies (and (stackp s1)
                (stackp s2)
                (equal (len s1) (+ 1 (len s2))))
           (equal (len (cdr s1)) (len s2))))
(defthm stack-car
  (implies (and (consp s)
                (stackp s))
           (integerp (car s))))
#|
docs proof-builder
|#
(defthm Lemma-incr
  (implies (and (inc-exprp e)
                (assignmentp a)
                (stackp s)
                (implies (exprp (cadr e))
                         (equal (len (m (compile-expression (cadr e)) 
                                              a s))
                                (+ 1 (len s)))))
           (equal (len (m (compile-expression e) a s))
                  (+ 1 (len s))))
  :hints
  (("Goal"
    :do-not-induct t)))

#|
4. (implies (and (sq-exprp x) 
                 (T1 | ((x (cadr x))))) 
            T1)

C1. (exprp x)            
C2. (sq-exprp x)
C3. (assignmentp a)
C4. (stackp s)
C5. (implies (and (exprp (cadr x))
                  (assignmentp a)
                  (stackp s))
             (let ((r (m (compile-expression (cadr x)) a s)))
               (equal (stack-len r) (+ 1 (stack-len s)))))
--------------------
C6. (exprp (cadr x)) {Def C1, C2}
C7. (equal (stack-len (m (compile-expression (cadr x)) a s)) 
           (+ 1 (stack-len s))) {MP, C6, C3, C4}
C8. (programp (compile-expression (cadr x))) 
    {Contract thm, compile-expression, C6}
C9. (>= (stack-len (m (compile-expression (cadr x)) a s)) 1) {Arith, C7}

(equal (stack-len (m (compile-expression x) a s))
       (+ 1 (stack-len s)))
={Def compile-expression, C2}
(equal (stack-len (m (append (compile-expression (cadr x)) 
                             '((dup) (mul))) 
                     a s))
       (+ 1 (stack-len s)))
={dup-mul, C8, C3, C4, C9}
(equal (stack-len (m (compile-expression (cadr x)) a s))
       (+ 1 (stack-len s)))
={C7}
t
|#

(defthm dup-mul
  (implies (and (programp p)
                (assignmentp a)
                (stackp s)
                (>= (len (m p a s)) 1))
           (equal (len (m (append p '((dup) (mul))) a s))
                  (len (m p a s)))))

(defthm nonzero-len-cons
  (implies (and (stackp s1)
                (stackp s2)
                (equal (len s1)
                       (+ 1 (len s2))))
           (consp s1)))
#|
(defthm Lemma-sq
  (implies (and (sq-exprp e)
                (assignmentp a)
                (stackp s)
                (implies (exprp (cadr e))
                         (equal (len (m (compile-expression (cadr e)) a s))
                                (+ 1 (len s)))))
           (equal (len (m (compile-expression e) a s))
                  (+ 1 (len s))))
  :hints
  (("Goal"
    :do-not-induct t)))

5. (implies (and (+-exprp x) 
                 (T1 | ((x (car x))))
                 (T1 | ((x (caddr x)))))
            T1)

C1. (exprp x)            
C2. (+-exprp x)
C3. (assignmentp a)
C4. (stackp s)
C5. (implies (and (exprp (car x))
                  (assignmentp a)
                  (stackp s))
             (equal (stack-len (m (compile-expression (car x)) a s))
                    (+ 1 (stack-len s))))
C5. (implies (and (exprp (caddr x))
                  (assignmentp a)
                  (stackp s))
             (equal (stack-len (m (compile-expression (caddr x)) a s))
                    (+ 1 (stack-len s))))
----------------------------------------------------                    
C7. (exprp (car x)) {Def exprp, C1, C2}
C8. (exprp (caddr x)) {Def exprp, C1, C2}
C9. (programp (compile-expression (car x))) 
     {Contract thm, compile-expression, C7}
C10. (programp (compile-expression (caddr x))) 
     {Contract thm, compile-expression, C8}
C11. (stackp (m (compile-expression (car x)) a s)) {Contract thm, m, C9, C3, C4}     
C12. (equal (stack-len (m (compile-expression (car x)) a s))
           (+ 1 (stack-len s))) {MP, C5, C7, C3, C4}
C13. (equal (stack-len (m (compile-expression (caddr x)) a 
                          (m (compile-expression (car x)) a s)))
            (+ 1 (stack-len (m (compile-expression (car x)) a s)))) {MP, C5, C8, C3, C11}    
C14. (equal (stack-len (m (compile-expression (caddr x)) a 
                          (m (compile-expression (car x)) a s)))
            (+ 2 (stack-len s))) {Arith, C13, C12}
C15. (>= (stack-len 
           (m (compile-expression (caddr x)) a 
              (m (compile-expression (car x)) a s))) 2) {Arith, C14}
C16. (equal (+ 1 (stack-len 
                  (m '((add)) a 
                     (m (compile-expression (caddr x)) a 
                        (m (compile-expression (car x)) a s)))))
            (stack-len
             (m (compile-expression (caddr x)) a 
                (m (compile-expression (car x)) a s))))
     {add-2, C3, C4, C15}
C17. (equal (+ 1 (stack-len 
                  (m '((add)) a 
                     (m (compile-expression (caddr x)) a 
                        (m (compile-expression (car x)) a s)))))
            (+ 2 (stack-len s))) {C14, C16}
C18. (equal (stack-len 
             (m '((add)) a 
                (m (compile-expression (caddr x)) a 
                   (m (compile-expression (car x)) a s))))
            (+ 1 (stack-len s))) {Arith, C17}


(equal (stack-len (m (compile-expression x) a s))
       (+ 1 (stack-len s)))      
={Def compile-expression, C2}
(equal (stack-len (m (append (compile-expression (car x)) 
                             (compile-expression (caddr x))
                             '((add)))
                     a s))
       (+ 1 (stack-len s)))
={m-append-dist, C9, C10, C3, C4}
(equal (stack-len (m (append (compile-expression (caddr x))
                             '((add)))
                     a (m (compile-expression (car x)) a s)))
       (+ 1 (stack-len s)))
={m-append-dist, C10, C9, C3, C4}
(equal (stack-len (m '((add)) a 
                     (m (compile-expression (caddr x)) a 
                        (m (compile-expression (car x)) a s))))
       (+ 1 (stack-len s)))
={C18}
t
     
|#
(defthm add-2
  (implies (and (assignmentp a)
                (stackp s)
                (>= (len s) 2))
           (equal (+ 1 (len (m '((add)) a s)))
                  (len s))))
#|
(defthm Lemma-+
  (implies (and (+-exprp e)
                (assignmentp a)
                (stackp s)
                (implies (exprp (car e))
                         (equal (len (m (compile-expression (car e)) a s))
                                (+ 1 (len s))))
                (implies (exprp (caddr e))
                         (equal (len (m (compile-expression (caddr e)) a s))
                                (+ 1 (len s)))))
           (equal (len (m (compile-expression e) a s))
                  (+ 1 (len s))))
  :hints
  (("Goal"
    :use m-nil-a-s=s)))
|#

#|
6. (implies (and (*-exprp x) 
                 (T1 | ((x (car x))))
                 (T1 | ((x (caddr x)))))
            T1)  
         

C1. (exprp x)            
C2. (*-exprp x)
C3. (assignmentp a)
C4. (stackp s)
C5. (implies (and (exprp (car x))
                  (assignmentp a)
                  (stackp s))
             (equal (stack-len (m (compile-expression (car x)) a s))
                    (+ 1 (stack-len s))))
C5. (implies (and (exprp (caddr x))
                  (assignmentp a)
                  (stackp s))
             (equal (stack-len (m (compile-expression (caddr x)) a s))
                    (+ 1 (stack-len s))))
----------------------------------------------------               
C7. (exprp (car x)) {Def exprp, C1, C2}
C8. (exprp (caddr x)) {Def exprp, C1, C2}
C9. (programp (compile-expression (car x))) 
     {Contract thm, compile-expression, C7}
C10. (programp (compile-expression (caddr x))) 
     {Contract thm, compile-expression, C8}
C11. (stackp (m (compile-expression (car x)) a s)) {Contract thm, m, C9, C3, C4}    
C12. (equal (stack-len (m (compile-expression (car x)) a s))
           (+ 1 (stack-len s))) {MP, C5, C7, C3, C4}
C13. (equal (stack-len (m (compile-expression (caddr x)) a 
                          (m (compile-expression (car x)) a s)))
            (+ 1 (stack-len (m (compile-expression (car x)) a s)))) {MP, C5, C8, C3, C11}    
C14. (equal (stack-len (m (compile-expression (caddr x)) a 
                          (m (compile-expression (car x)) a s)))
            (+ 2 (stack-len s))) {Arith, C13, C12}
C15. (>= (stack-len 
           (m (compile-expression (caddr x)) a 
              (m (compile-expression (car x)) a s))) 2) {Arith, C14}
C16. (equal (+ 1 (stack-len 
                  (m '((mul)) a 
                     (m (compile-expression (caddr x)) a 
                        (m (compile-expression (car x)) a s)))))
            (stack-len
             (m (compile-expression (caddr x)) a 
                (m (compile-expression (car x)) a s))))
     {mul-2, C3, C4, C15}
C17. (equal (+ 1 (stack-len 
                  (m '((mul)) a 
                     (m (compile-expression (caddr x)) a 
                        (m (compile-expression (car x)) a s)))))
            (+ 2 (stack-len s))) {C14, C16}
C18. (equal (stack-len 
             (m '((mul)) a 
                (m (compile-expression (caddr x)) a 
                   (m (compile-expression (car x)) a s))))
            (+ 1 (stack-len s))) {Arith, C17}    
              
(equal (stack-len (m (compile-expression x) a s))
       (+ 1 (stack-len s)))      
={Def compile-expression, C2}
(equal (stack-len (m (append (compile-expression (car x)) 
                             (compile-expression (caddr x))
                             '((mul)))
                     a s))
       (+ 1 (stack-len s)))
={m-append-dist, C9, C10, C3, C4}
(equal (stack-len (m (append (compile-expression (caddr x))
                             '((mul)))
                     a (m (compile-expression (car x)) a s)))
       (+ 1 (stack-len s)))
={m-append-dist, C10, C9, C3, C4}
(equal (stack-len (m '((mul)) a 
                     (m (compile-expression (caddr x)) a 
                        (m (compile-expression (car x)) a s))))
       (+ 1 (stack-len s)))
={C18}
t              
|#
(defthm mul-2
  (implies (and (assignmentp a)
                (stackp s)
                (>= (len s) 2))
           (equal (+ 1 (len (m '((mul)) a s)))
                  (len s))))
#|
(defthm Lemma-+
  (implies (and (+-exprp e)
                (assignmentp a)
                (stackp s)
                (implies (exprp (car e))
                         (equal (stack-len (m (compile-expression (car e)) a s))
                                (+ 1 (stack-len s))))
                (implies (exprp (caddr e))
                         (equal (stack-len (m (compile-expression (caddr e)) a s))
                                (+ 1 (stack-len s)))))
           (equal (stack-len (m (compile-expression e) a s))
                  (+ 1 (stack-len s)))))
|#

#|
(defthm stack-correct
  (implies (and (exprp x) (assignmentp a) (stackp s))
           (equal (stack-len (m (compile-expression x) a s))
                  (+ 1 (stack-len s)))))
|#

; useful fact, thanks to T1
(defthm res-cons
  (implies (and (exprp e)
                (assignmentp a)
                (stackp s)
                (equal (len (m (compile-expression e) a s))
                       (+ 1 (len s))))
           (consp (m (compile-expression e) a s))))

; another useful fact
(defthm top-pop
  (implies (and (stackp x)
                (consp x))
           (equal (cons (top-stack x) (pop-stack x)) x)))

#|


Theorem 2: the value at the top of the stack for a 
compiled expression = result of direct evaluation of expression.

(implies (and (exprp e)
              (assignmentp a)
              (stackp s))
         (equal (evaluate e a)
                (top-stack (m (compile-expression e) a s))))

This will be proven using the induction scheme of (evaluate e).

1. (implies (integerp e) T2)

C1. (exprp e)
C2. (integerp e)
C3. (assignmentp a)
C4. (stackp s)
-------------------


(equal (evaluate e a)
       (top-stack (m (compile-expression e) a s)))
={Def evaluate, C2}
(equal e (top-stack (m (compile-expresison e) a s)))
={Def compile-expression, C2}
(equal e (top-stack (m (list (list 'push e)) a s)))
={Def m}
(equal e (top-stack (m nil a (execute (list 'push e) a s))))
={Def m}
(equal e (top-stack (execute (list 'push e) a s)))
={Def execute}
(equal e (top-stack (push-stack e s)))
={Def push-stack}
(equal e (top-stack (cons e s)))
={Def top-stack}
(equal e e)
={equal axiom}
t
|#

(defthm int-case2
  (implies (and (exprp e)
                (integerp e)
                (assignmentp a)
                (stackp s))
           (equal (evaluate e a)
                  (top-stack (m (compile-expression e) a s)))))
#|
2. (implies (symbolp e) T2)

C1. (exprp e)
C2. (symbolp e)
C3. (assignmentp a)
C4. (stackp s)
-------------------


(equal (evaluate e a)
       (top-stack (m (compile-expression e) a s)))
={Def evaluate, C2}
(equal (lookup e a) (top-stack (m (compile-expresison e) a s)))
={Def compile-expression, C2}
(equal (lookup e a) (top-stack (m (list (list 'load e)) a s)))
={Def m}
(equal (lookup e a) (top-stack (m nil a (execute (list 'load e) a s))))
={Def m}
(equal (lookup e a) (top-stack (execute (list 'load e) a s)))
={Def execute}
(equal (lookup e a) (top-stack (push-stack (lookup e a) s)))
={Def push-stack}
(equal (lookup e a) (top-stack (cons (lookup e a) s)))
={Def top-stack}
(equal (lookup e a) (lookup e a))
={equal axiom}
t
|#

(defthm symbol-case2
  (implies (and (exprp e)
                (symbolp e)
                (assignmentp a)
                (stackp s))
           (equal (evaluate e a)
                  (top-stack (m (compile-expression e) a s)))))
#|

3. (implies (not (exprp e) T2)
Reductio ad absurdum. Done.
|#
(defthm unsat-case2
  (implies (and (exprp e)
                (not (exprp e))
                (assignmentp a)
                (stackp s))
           (equal (evaluate e a)
                  (top-stack (m (compile-expression e) a s)))))
#|
4. (implies (and (inc-exprp e) 
                 (T2 | ((e (cadr e))))) 
            T2)
C1. (exprp e)
C2. (inc-exprp e)
C3. (assignmentp a)
C4. (stackp s)
C5. (implies (and (exprp (cadr e))
                  (assignmentp a)
                  (stackp s))
             (equal (evaluate (cadr e) a)
                    (top-stack (m (compile-expression (cadr e) a s)))))
----------------------------------------------            
C6. (exprp (cadr e)) {C2}
C7. (equal (evaluate (cadr e) a)
           (top-stack (m (compile-expression (cadr e) a s)))) 
    {MP, C5, C6, C3, C4}
           
(equal (evaluate e a)
       (top-stack (m (compile-expression e) a s)))
={Def evaluate, C2}
(equal (+ 1 (evaluate (cadr e) a))
       (top-stack (m (compile-expression e) a s)))
={Def compile-expression, C2}
(equal (+ 1 (evaluate (cadr e) a))
       (top-stack (m (append (compile-expression (cadr e)) '((push 1) (add))) a s)))
={m-append-dist}
(equal (+ 1 (evaluate (cadr e) a))
       (top-stack (m '((push 1) (add)) a
                     (m (compile-expression (cadr e)) a s))))
={Def m}
(equal (+ 1 (evaluate (cadr e) a))
       (top-stack (m '((add)) a
                     (execute '(push 1) a (m (compile-expression (cadr e)) a s)))))
={Def execute}
(equal (+ 1 (evaluate (cadr e) a))
       (top-stack (m '((add)) a
                     (cons 1 (m (compile-expression (cadr e)) a s)))))
={Def m}
(equal (+ 1 (evaluate (cadr e) a))
       (top-stack (m nil a
                     (execute '(add) a (cons 1 (m (compile-expression (cadr e)) a s))))))
={Def m}
(equal (+ 1 (evaluate (cadr e) a))
       (top-stack (execute '(add) a (cons 1 (m (compile-expression (cadr e)) a s)))))
={Def execute}
(equal (+ 1 (evaluate (cadr e) a))
       (top-stack (push-stack (+ 1 (top-stack (m (compile-expression (cadr e)) a s)))
                              (pop-stack (m (compile-expression (cadr e)) a s)))))
={C7}
(equal (+ 1 (evaluate (cadr e) a))
       (top-stack (push-stack (+ 1 (evaluate (cadr e) a))
                              (pop-stack (m (compile-expression (cadr e)) a s)))))
={Def push-stack}
(equal (+ 1 (evaluate (cadr e) a))
       (top-stack (cons (+ 1 (evaluate (cadr e) a))
                        (pop-stack (m (compile-expression (cadr e)) a s)))))
={Def top-stack}                              
 (equal (+ 1 (evaluate (cadr e) a))
        (+ 1 (evaluate (cadr e) a)))
={equal axiom}
t
|#
(defthm Lemma-incr-2
  (implies (and (inc-exprp e)
                (assignmentp a)
                (stackp s)
                (implies (and (exprp (cadr e))
                              (assignmentp a)
                              (stackp s))
                         (equal (evaluate (cadr e) a)
                                (top-stack (m (compile-expression (cadr e)) a s)))))
           (equal (evaluate e a)
                  (top-stack (m (compile-expression e) a s)))))
           
                

#|
                              
5. (implies (and (sq-exprp x) 
                 (T2 | ((x (cadr x))))) 
            T2)  

C1. (exprp e)
C2. (sq-exprp e)
C3. (assignmentp a)
C4. (stackp s)
C5. (implies (and (exprp (cadr e))
                  (assignmentp a)
                  (stackp s))
             (equal (evaluate (cadr e) a)
                    (top-stack (m (compile-expression (cadr e) a s)))))
----------------------------------------------            
C6. (exprp (cadr e)) {C2}
C7. (equal (evaluate (cadr e) a)
           (top-stack (m (compile-expression (cadr e) a s)))) 
    {MP, C5, C6, C3, C4}
           
(equal (evaluate e a)
       (top-stack (m (compile-expression e) a s)))
={Def evaluate, C2}
(equal (* 1 (evaluate (cadr e) a))
       (top-stack (m (compile-expression e) a s)))
={Def compile-expression, C2}
(equal (* (evaluate (cadr e) a) (evaluate (cadr e) a))
       (top-stack (m (append (compile-expression (cadr e)) '((dup) (mul))) a s)))
={m-append-dist}
(equal (* (evaluate (cadr e) a) (evaluate (cadr e) a))
       (top-stack (m '((dup) (mul)) a
                     (m (compile-expression (cadr e)) a s))))
={Def m}
(equal (* (evaluate (cadr e) a) (evaluate (cadr e) a))
       (top-stack (m '((mul)) a
                     (execute '(dup) a (m (compile-expression (cadr e)) a s)))))
={Def execute}
(equal (* (evaluate (cadr e) a) (evaluate (cadr e) a))
       (top-stack (m '((mul)) a
                     (cons (top-stack (m (compile-expression (cadr e)) a s))
                           (m (compile-expression (cadr e)) a s)))))
={Def m}
(equal (* (evaluate (cadr e) a) (evaluate (cadr e) a))
       (top-stack (m nil a
                     (execute '(mul) a 
                              (cons (top-stack (m (compile-expression (cadr e)) a s))
                                    (m (compile-expression (cadr e)) a s))))))
={Def m}
(equal (* (evaluate (cadr e) a) (evaluate (cadr e) a))
       (top-stack (execute '(mul) a (cons (top-stack (m (compile-expression (cadr e)) a s))
                                          (m (compile-expression (cadr e)) a s)))))
={Def execute}
(equal (* (evaluate (cadr e) a) (evaluate (cadr e) a))
       (top-stack (push-stack (* (top-stack (m (compile-expression (cadr e)) a s))
                                 (top-stack (m (compile-expression (cadr e)) a s)))
                              (pop-stack (m (compile-expression (cadr e)) a s)))))
={C7}
(equal (* (evaluate (cadr e) a) (evaluate (cadr e) a))
       (top-stack (push-stack (* (evaluate (cadr e) a) (evaluate (cadr e) a))
                              (pop-stack (m (compile-expression (cadr e)) a s)))))
={Def push-stack}
(equal (* (evaluate (cadr e) a) (evaluate (cadr e) a))
       (top-stack (cons (* (evaluate (cadr e) a) (evaluate (cadr e) a))
                        (pop-stack (m (compile-expression (cadr e)) a s)))))
={Def top-stack}                              
 (equal (* (evaluate (cadr e) a) (evaluate (cadr e) a))
        (* (evaluate (cadr e) a) (evaluate (cadr e) a)))
={equal axiom}
t
|#
(defthm Lemma-sq-2
  (implies (and (sq-exprp e)
                (assignmentp a)
                (stackp s)
                (implies (and (exprp (cadr e))
                              (assignmentp a)
                              (stackp s))
                         (equal (evaluate (cadr e) a)
                                (top-stack (m (compile-expression (cadr e)) a s)))))
           (equal (evaluate e a)
                  (top-stack (m (compile-expression e) a s)))))
#|
6. (implies (and (+-exprp x) 
                 (T2 | ((x (car x))))
                 (T2 | ((x (caddr x))))) 
            T2)  

C1. (+-exprp x)
C2. (assignmentp a)
C3. (stackp s)
C4. (implies (and (exprp (car x))
                  (assignmentp a)
                  (stackp s))
              (equal (evaluate (car x) a)
                     (top-stack (m (compile-expression (car x)) a s))))
C5. (implies (and (exprp (caddr x))
                  (assignmentp a)
                  (stackp s))
              (equal (evaluate (caddr x) a)
                     (top-stack (m (compile-expression (caddr x)) a s))))
----------------------------------------------------------------                     
C6. (exprp (car x)) {C1}
C7. (exprp (caddr x)) {C1}
C8. (equal (evaluate (car x) a)
           (top-stack (m (compile-expression (car x)) a s))) 
    {MP, C4, C6, C2, C3}
C9. (stackp (m (compile-expression (car x)) a s)) {Contract thm, m, C6, C2, C3}
C10. (equal (evaluate (caddr x) a)
            (top-stack (m (compile-expression (caddr x)) a
                          (m (compile-expression (car x)) a s))))
     {MP, C5, C7, C2, C9}
C11. (consp (m (compile-expression (car x)) a s))
     {res-cons, C6, C2, C3}
C12. (equal (m (compile-expression (car x)) a s)
            (cons (top-stack (m (compile-expression (car x)) a s))
                  (pop-stack (m (compile-expression (car x)) a s))))
     {top-pop, C9, C11}
C13. (equal (m (compile-expression (car x)) a s)
            (cons (evaluate (car x) a)
                  (pop-stack (m (compile-expression (car x)) a s))))
     {C8, C12}
C14. (consp (m (compile-expression (caddr x)) a
               (m (compile-expression (car x)) a s)))
     {res-cons, C7, C2, C3}
C15. (stackp (m (compile-expression (caddr x)) a
                (m (compile-expression (car x)) a s)))
     {Contract thm, m, C7, C2, C3}
C16. (equal (m (compile-expression (caddr x)) a
               (m (compile-expression (car x)) a s))
            (cons
              (top-stack
               (m (compile-expression (caddr x)) a
                  (m (compile-expression (car x)) a s)))
              (pop-stack
               (m (compile-expression (caddr x)) a
                  (m (compile-expression (car x)) a s)))))
     {top-pop, C15}
C17. (equal (m (compile-expression (caddr x)) a
               (m (compile-expression (car x)) a s))
            (cons (evaluate (caddr x) a)
                  (pop-stack
                    (m (compile-expression (caddr x)) a
                       (m (compile-expression (car x)) a s)))))
      {C16, C10, C15}

      
      
(equal (evaluate x a)
       (top-stack (m (compile-expression x) a s)))
={Def evaluate, C1}
(equal (+ (evaluate (car x) a) (evaluate (caddr x) a))
       (top-stack (m (compile-expression x) a s)))
={Def compile-expression, C1}
(equal (+ (evaluate (car x) a) (evaluate (caddr x) a))
       (top-stack (m (append (compile-expression (car x)) 
                             (compile-expression (caddr x))
                             '((add))) a s)))
={m-append-dist}       
(equal (+ (evaluate (car x) a) (evaluate (caddr x) a))       
       (top-stack (m (append (compile-expression (caddr x))
                             '((add))) a
                      (m (compile-expression (car x)) a s))))
={m-append-dist}       
(equal (+ (evaluate (car x) a) (evaluate (caddr x) a))       
       (top-stack (m '((add)) a
                     (m (compile-expression (caddr x)) a 
                        (m (compile-expression (car x)) a s)))))      
={Def m}       
(equal (+ (evaluate (car x) a) (evaluate (caddr x) a))       
       (top-stack (m nil a
                     (execute '(add) a
                              (m (compile-expression (caddr x)) a 
                                 (m (compile-expression (car x)) a s))))))        
={Def m}       
(equal (+ (evaluate (car x) a) (evaluate (caddr x) a))       
       (top-stack (execute '(add) a
                           (m (compile-expression (caddr x)) a 
                              (m (compile-expression (car x)) a s))))) 
={Def execute}
(equal (+ (evaluate (car x) a) (evaluate (caddr x) a))       
       (top-stack (push-stack (+ (top-stack (m (compile-expression (caddr x)) a 
                                               (m (compile-expression (car x)) a s)))
                                 (top-stack (pop-stack (m (compile-expression (caddr x)) a 
                                                          (m (compile-expression (car x)) a s)))))
                              (pop-stack
                               (pop-stack
                                (m (compile-expression (caddr x)) a 
                                   (m (compile-expression (car x)) a s)))))))
={def push-stack}                              
(equal (+ (evaluate (car x) a) (evaluate (caddr x) a))       
       (top-stack (cons (+ (top-stack (m (compile-expression (caddr x)) a 
                                         (m (compile-expression (car x)) a s)))
                            (top-stack (pop-stack (m (compile-expression (caddr x)) a 
                                                     (m (compile-expression (car x)) a s)))))
                              (pop-stack
                               (pop-stack
                                (m (compile-expression (caddr x)) a 
                                   (m (compile-expression (car x)) a s)))))))                         
={Def top-stack}                              
(equal (+ (evaluate (car x) a) (evaluate (caddr x) a))                                   
       (+ (top-stack (m (compile-expression (caddr x)) a 
                        (m (compile-expression (car x)) a s)))
          (top-stack (pop-stack (m (compile-expression (caddr x)) a 
                                   (m (compile-expression (car x)) a s))))))                       
={C10}
(equal (+ (evaluate (car x) a) (evaluate (caddr x) a))                                   
       (+ (evaluate (caddr x) a)
          (top-stack (pop-stack (m (compile-expression (caddr x)) a 
                                   (m (compile-expression (car x)) a s))))))   
={Def pop-stack, C17}
(equal (+ (evaluate (car x) a) 
          (evaluate (caddr x) a))                                   
       (+ (evaluate (caddr x) a)
          (evaluate (caddr x) a)))
={equal axiom}
t
|#
(verify
 (IMPLIES (AND (NOT (CONSP E2))
              (+-EXPRP (CONS E1 E2))
              (ASSIGNMENTP A)
              (STACKP S)
              (CONSP (M (COMPILE-EXPRESSION E1) A S))
              (EQUAL (EVALUATE E1 A)
                     (CAR (M (COMPILE-EXPRESSION E1) A S)))
              (NOT (INC-EXPRP (CONS E1 E2)))
              (NOT (SQ-EXPRP (CONS E1 E2)))
              (CONSP (M (APPEND (COMPILE-EXPRESSION E1)
                                '((LOAD NIL) (ADD)))
                        A S))
              (*-EXPRP (CONS E1 E2))
              (ACL2-NUMBERP (EVALUATE E1 A)))
         (EQUAL (* (LOOKUP NIL A) (EVALUATE E1 A))
                (CAR (M (APPEND (COMPILE-EXPRESSION E1)
                                '((LOAD NIL) (ADD)))
                        A S)))))#|ACL2s-ToDo-Line|#


(defthm Lemma-+-2
  (implies (and (+-exprp e)
                (assignmentp a)
                (stackp s)
                (implies (and (exprp (car e))
                              (assignmentp a)
                              (stackp s))
                         (equal (evaluate (car e) a)
                                (top-stack (m (compile-expression (car e)) a s))))
                (implies (and (exprp (caddr e))
                              (assignmentp a)
                              (stackp s))
                         (equal (evaluate (caddr e) a)
                                (top-stack (m (compile-expression (caddr e)) a s)))))
           (equal (evaluate e a)
                  (top-stack (m (compile-expression e) a s)))))               
#|
7. (implies (and (*-exprp x) 
                 (T2 | ((x (car x))))
                 (T2 | ((x (caddr x))))) 
            T2)              
            |#