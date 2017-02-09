;; #1 right-to-left and left-to-right evaluation of operands==================================================

(define (list-of-values-l2r exps env)
	(if (no-operands? exps)
		'()
		(let ((first (eval (first-operand exps))))
			(cons first 
				  (list-of-values-l2r (rest-operands exps) env)))))

(define (list-of-values-r2l exps env)
	(if (no-operands? exps)
		'()
		(let ((rest (list-of-values-r2l (rest-operands exps) env)))
            (cons (eval (first-operand exps))
            	rest))))

;; #2 a. If Louis Reasoner carries out his plan, many special forms will start being incorrectly========================
;;       interpreted as applications of procedures. To avoid this, some special form for procedure
;;       application needs to be implemented.
;;
;;    b. It could be implemented as follows:
	
(define (call-application? exp) (tagged-list? exp 'call))
(define (operator-call exp) (cadr exp))
(define (operands-call exp) (cddr exp))

;; #3 data-directed evaluation; this programming style permits easy extension of eval special forms==================

(define operation-table (make-table))
(define get (operation-table 'lookup-proc))
(define put (operation-table 'insert-proc!))

(put 'op 'quote text-of-quotation)
(put 'op 'set! eval-assignment)
(put 'op 'define eval-definition)
(put 'op 'if eval-if)
(put 'op 'lambda (lambda (exp env) (make-procedure (lambda-parameters exp) 
												   (lambda-body exp) 
												   env)))
(put 'op 'begin (lambda (exp env) (eval-sequence (begin-sequence exp) env)))
(put 'op 'cond (lambda (exp env) (eval-dd (cond->if exp) env)))
(put 'op 'and eval-and)

(define (eval-dd exp env)
	(cond ((self-evaluating? exp) exp)
		  ((variable? exp) (lookup-variable-value exp env))
		  ((get 'op (car exp)) (apply (get 'op (car exp)) exp env))
		  ((application? expr) (apply (eval-dd (operator exp) env) 
		  	                          (list-of-values (operands exp) env)))
		  (else "Unknown expression type -- EVAL" exp)))

;; #4 'and' and 'or' as special forms and as expressions derived from 'if'==================================

(define (and? exp) (tagged-list? exp 'and))
(define and-clauses cdr)
(define (eval-and exp env)
	(define (eval-and-clauses exps)
		(let ((val (eval-dd (first-exp exps) env)))
		 	 (cond ((last-exp? exps) val)
			   	   (val (eval-and-clauses (rest-exps exps) env))
			       (else #f))))
	(eval-and-clauses (and-clauses exp)))

(define (or? exp) (tagged-list? exp 'or))
(define or-clauses cdr)
(define (eval-or exp env)
	(define (eval-or-clauses exps)
		(let ((val (eval-dd (first-exp exps) env)))
			 (cond ((last-exp? exps) val)
			       (val #t)
			       (else (eval-or-clauses (rest-exps exps) env)))))
	(eval-or-clauses (or-clauses exp)))

(define (and->if exp) (expand-and-clauses (and-clauses exp)))
(define (expand-and-clauses exps)
	(if (null? exps) #t
		(make-if (first-exp exps)
				 (expand-and-clauses (rest-exps exps))
				 #f)))

(define (or->if exp) (expand-or-clauses (or-clauses exp)))
(define (expand-or-clauses exps)
	(if (null? exps) #f
		(make-if (first-exp exps)
				 #t
				 (expand-or-clauses (rest-exps exps)))))

;; #5 dealing with the extended '<test> => <recipient>' cond syntax=============================================


;; Note: this solution does not account for a <test> with side-effects. For example, evaluating an incrementor assignment
;; and then re-evaluating it to pass it as an argument into the <recipient> process will cause it to increment twice.
;; However, accounting for such a problem is beyond the scope of the text's question. It would, most importantly,
;; require rewriting the core evaluator to test for such application clauses, and if found, would then make the cond
;; expression be evaluated normally, and no longer be a type of derived expression.
;;
;; However, if such fringe cases are ignored for the purpose of this assignment, the solution becomes quite simple:

(define (apply-clause? clause)
	(eq? (cadr clause) '=>))

(define (cond-apply-action clause)
	(caddr clause))

(define (cond-actions clause) 
	(if (apply-clause? clause)
		(cons (cond-apply-action clause) (list (cond-predicate clause)))
		(cdr clause)))

;; #6 let expressions as derived lambda combinations=============================================================

(define (let? exp) (tagged-list? exp 'let)) ;; unnecessary with data-directed evaluation
(define (let-bindings exp) (cadr exp))
(define (let-body exp) (caddr exp))
(define (let-binding-var binding) (car binding))
(define (let-binding-exp binding) (cadr binding))

(define (let-binding-vars exp) (map car (cadr exp)))

(define (let-binding-exps exp) (map cadr (cadr exp)))

(define (let->combination exp)
	(cons (make-lambda (let-binding-vars exp) (list (let-body exp))) (let-binding-exps exp)))

(put 'op 'let (lambda (exp env) (eval-dd (let->combination exp) env)))

;; ~#7 let* expressions as nested lets===================================================================================

(define (let*? exp) (tagged-list? exp 'let*)) ;; unnecessary with data-directed evaluation
(define (let-first-binding bindings) (car bindings))
(define (let-rest-bindings bindings) (cdr bindings))

(define (make-let binding body)
	(cons 'let (cons (list binding) (list body))))

(define (let*->nested-lets exp)
	(define (binding->let bindings)
		(if (null? (let-rest-bindings bindings))
			(make-let (let-first-binding bindings) (let-body exp))
			(make-let (let-first-binding bindings) (binding->let (let-rest-bindings bindings)))))
	(binding->let (let-bindings exp)))	

(put 'op 'let* (lambda (exp env) (eval-dd (let*->nested-lets exp) env)))

;; There's a followup question to this: does the following evaluation method work for let* expressions?
;; More specifically, does let* work as a derived expression, or must we explicitly expand it in terms of
;; non-derived expressions?
;; I think it works as a derived expression... the nested lets should be successively converted into
;; lambda expressions, which are in turn converted into procedures, which are in turn applied,
;; at which point their arguments, an internal let expression, is evaluated, and so on recursively. 
;; I have a bit of self-doubt here, so I'll take a look at this question again on a followup readthrough of this text.
;; **************************

;; ~#8 'named' let expressions======================================================================================
;; This is a variant of let that has the form (let <var> <bindings> <body>); the difference being the 'name' <var>.
;; Such statements are useful for creating recursive processes, such as:
;; (define (fib n)
;;  (let fib-iter ((a 1)
;;                 (b 0)
;;                 (count n))
;;    (if (= count 0)
;;        b
;;        (fib-iter (+ a b) a (- count 1)))))

(define (named-let? exp) (symbol? (cadr exp))))
(define (named-let-name exp) (cadr exp))
(define (named-let-bindings) (caddr exp))
(define (named-let-binding-vars exp) (map car (named-let-bindings exp)))
(define (named-let-binding-exps exp) (map cadr (named-let-bindings exp)))
(define (named-let-body) (cadddr exp))

;; This requires modification of the let->combination procedure, as the tag does not differentiate the expression.
;; If the let expression is a 'named let' expression, the evaluator splits it into a define/apply pair
;; This is not ideal behavior, as define changes the current environment, while a let should create its own environment
;; Maybe revise later *****************************

(define (named-let->define exp)
	(list 'define (cons (named-let-name exp) (named-let-binding-vars exp))
		(named-let-body exp)))

(define (let->combination exp)
	(if (named-let? exp)
		(list (named-let->define exp) (cons (named-let-name exp) (named-let-binding-vars exp)))
		(cons (make-lambda (let-binding-vars exp) (list (let-body exp))) (let-binding-exps exp))))

;; >#9 Iteration constructs: while (do, for, until?):

(define (while? exp) (tagged-list? exp 'while))
(define (while-condition exp) (cadr exp))
(define (while-body exp) (caddr exp))

;; >#10 Design and implement a new syntax for scheme by modifying the procedures in this section:

;; >#11 Representing a frame as a list of bindings rather than a pair of lists:

;; >#12 Representing set-variable-value!, define-variable-value!, and lookup-variable-value
;; in terms of more abstract procedures for traversing the environment structure

;; >#13 Removing bindings

;; #14 Including map as a primitive procedure vs. more directly implementing map



;; #15 Halting problem

;; Suppose there was a predicate procedure (halts? p a) that tested whether procedure p halted for input a

(define (run-forever) (run-forever))

(define (try p)
  (if (halts? p p)
      (run-forever)
      'halted))

;; (run-forever) clearly does not halt. Does the expression (try try) halt or not? If (halts? try try) is true
;; then (try try) evaluates to the (run-forever) infinite loop, and does not halt
;; If (halts? try try) is false then (try try) evaluates to 'halted, and does halt
;; Both of these outcomes are incompatible with the definition of halts?

;; #16 Scanning out internal definitions: this section focuses on handling internal definitions which rely on
;;     other internal definitions. For example, in the following definition, the 'even?' process refers to the
;;     'odd?' process, but the 'odd?' process definition is under and thus 'after' the 'even?' process.
;;
;; (define (f x)
;;  (define (even? n)
;;    (if (= n 0)
;;        true
;;        (odd? (- n 1))))
;;  (define (odd? n)
;;   (if (= n 0)
;;        false
;;        (even? (- n 1))))
;;  '(rest of body of f))

;; #16a First, lookup-variable-value must signal an error if an '*unassigned' variable is encountered

(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (if (eq? '*unassigned* (car vals))
             	(error "Unassigned variable" var)
             	(car vals)))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

;; #16b Then, in procedure evaluation, the procedure body must be transformed into one without internal definitions

(define (lambda-body-defines body) (filter definition? body)
(define (lambda-body-not-defines body) (filter (lambda (x) (not (definition? x))) body))
(define (lambda-body-has-defines? body) (not (eq? '() (lambda-body-defines body))))

(define (internal-def-lets body) 
	(list 'let (map (lambda (x) (list (cadr x) '*unassigned*)) (lambda-body-defines body))))
(define (internal-def-sets body)
	(map (lambda (x) (list 'set! (cadr x) (caddr x))) (lambda-body-defines body)))
(define (scan-out-defines body)
	(if (lambda-body-has-defines? body)
		(append (internal-def-lets exp) (internal-def-sets exp) (lambda-body-not-defines exp))
		body)

;; #17 Since let expressions are transformed into lambda expressions, the following transformation occurs:
;;  (lambda <vars>				(lambda <vars>                       (lambda <vars>
;;    (define u <e1>)		      (let ((u '*unassigned)                ((lambda (u v)
;;	  (define v <e2>)		->	     	(v '*unassigned))     ->  	       (set! u <e1>)
;;    <e3>)  						    (set! u <e1>)                      (set! v <e2>)
;;                                      (set! v <e2>)                      <e3>) '*unassigned 
;;                                      <e3>)                                    '*unassigned))
;; This nested lambda introduces an additional frame into the environment, but one that is confined
;; to the nested application, so it will not affect the containing environment

;; ~#18

;; #19 The following process will cause an error, as during the evaluation of (+ a x) a is still '*unassigned
;;     To avoid this error, lazy evaluation i.e. a delay keyword could be used

(let ((a 1))
  (define (f x)
    (define b (+ a x))
    (define a 5)
    (+ a b))
  (f 10))

;; #20 letrec, the recursive let

(define (letrec? exp) (tagged-list? exp 'letrec))
(define (letrec->let exp) )

;; #21 Making recursive procedures without using define


;; THE ANALYZING METACIRCULAR EVALUATOR

;; #22 

;; To incorporate let into the analyzing evaluator, simply add the following line to the case analysis of analyze 
((let? exp) (analyze (let->combination exp))

;; #23 & 24

;; THE LAZY EVALUATOR

;; #25

;; The following process will exceed maximum excursion depth in an applicative-order programming language
;; The lazy evaluator will, of course, solve this problem

(define (factorial n)
  (unless (= n 1)
          (* n (factorial (- n 1)))
          1))

;; ~#26 The virtues of unless as a procedure, and the implementing of unless as a special form

;; ~#27-34

;; THE AMBIGUOUS EVALUATOR : NON-DETERMINISTIC COMPUTING

;; #35 

(define (an-integer-between j k)
	(cond ((= k j) k)
	      ((< k j) (amb))
	      (else (amb j (an-integer-between (+ 1 j) k)))))

(define (a-pythagorean-triple-between low high)
  (let ((i (an-integer-between low high)))
    (let ((j (an-integer-between i high)))
      (let ((k (an-integer-between j high)))
        (require (= (+ (* i i) (* j j)) (* k k)))
        (list i j k)))))

;; #36 Simply replacing 'an-integer-between' with 'an-integer-starting-from' will not generate all pythagorean triples,
;;     because on every failure, the first index will always be incremented, so it will test 1 1 1, 2 1 1, ..., n 1 1

(define (a-triple-from ))

(define (all-pythagorean-triples))