(#%require (only racket/base error))
(define call/cc call-with-current-continuation)
;;; file: s450.scm
;;;
;;; Metacircular evaluator from chapter 4 of STRUCTURE AND
;;; INTERPRETATION OF COMPUTER PROGRAMS (2nd edition)
;;;
;;; Modified by kwn, 3/4/97
;;; Modified and commented by Carl Offner, 10/21/98 -- 10/12/04
;;;
;;; This code is the code for the metacircular evaluator as it appears
;;; in the textbook in sections 4.1.1-4.1.4, with tahe following
;;; changes:
;;;
;;; 1.  It uses #f and #t, not false and true, to be Scheme-conformant.
;;;
;;; 2.  Some function names were changed to avoid conflict with the
;;; underlying Scheme:
;;;
;;;       eval => xeval
;;;       apply => xapply
;;;       extend-environment => xtend-environment
;;;
;;; 3.  The driver-loop is called s450.
;;;
;;; 4.  The booleans (#t and #f) are classified as self-evaluating.
;;;
;;; 5.  These modifications make it look more like UMB Scheme:
;;;
;;;        The define special form evaluates to (i.e., "returns") the
;;;          variable being defined.
;;;        No prefix is printed before an output value.
;;;
;;; 6.  I changed "compound-procedure" to "user-defined-procedure".
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;---------------------------------------
;------ Special forms Table ------------
;---------------------------------------

(define (make-table)
  (list '*table*))

(define special-form-table (make-table))
(define (error x) (display "Error: ") (display x)(newline))

(define (install-special-form key value)
  (define (insert special-form-table)
    (let((record (assoc key (cdr special-form-table))))
      (if record
          (error "cannot reinstall special form")
          (set-cdr! special-form-table
                    (cons (cons key value)
                          (cdr special-form-table))))
      key))
  (insert special-form-table))

(define (lookup-action key)
  (define (lookup table)
    (let ((record (assoc key (cdr table))))
      (if record
          (cdr record)
          #f)))
  (lookup special-form-table))

;write in s450.scm
(define special-form-table (make-table))

;storing special forms into table
(install-special-form 'set! (lambda (exp env)
                                (cond((lookup-action (cadr exp))
                                      "cannot reassign special form")
                                     (else (eval-assessment exp env)))))

(install-special-form 'define (lambda (exp env)
                                (cond((lookup-action (cadr exp))
                                      "cannot reassign special form")
                                     (else (eval-definition exp env)))))

(install-special-form 'if (lambda (exp env) (eval-if exp env)))
(install-special-form 'begin (lambda (exp env) (eval-sequence exp env)))
(install-special-form 'cond (lambda (exp env) (cond->if exp)))
(install-special-form 'lambda  (lambda (exp env) (make-procedure (lambda-parameters exp) (lambda-body exp) env)))
(install-special-form 'quote (lambda (exp env) (text-of-quotation exp) (cadr exp)))
(install-special-form 'defined? (lambda (exp env) (defined? exp env)))
(install-special-form 'locally-defined? (lambda (exp env) (locally-defined? exp env)))
(install-special-form 'locally-make-unbound! (lambda (exp env) (locally-make-unbound! exp env)))
(install-special-form 'make-unbound! (lambda (exp env) (make-unbound! exp env)))
(install-special-form 'delayed (lambda (exp env) (delayed exp env)))
(install-special-form 'cons-stream (lambda (exp env) (cons-stream exp env)))
(install-special-form 'load (lambda (exp env) eval-load))
;--------------------------------
;--- xeval and xapply -----------
;--------------------------------
                 
;we might need quote

(define (xeval exp env)
  ;(newline)(display "expression")(newline)
  ;(display exp)(newline)
  ;(display "-------------------------")
  ;(newline)(display "environment")
  ;(display env)
  (cond ((self-evaluating? exp) exp)
        ((variable? exp)
         (cond((lookup-action exp)
               (display "Special form: ")
               exp)
              (else (lookup-variable-value exp env))))
        ((lookup-action (car exp))
         ((lookup-action (car exp)) exp env))
        ((thunk? exp) (force-it exp))
        ((application? exp)
         (xapply (xeval (operator exp) env)
                 (list-of-values exp env)))
        (else
         (s450error exp))))

(define (xapply procedure arguments)
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure procedure arguments))
         ((user-defined-procedure? procedure)
         (eval-sequence
           (procedure-body procedure)
           (xtend-environment
             (remove-tag (procedure-parameters procedure))
             arguments
             (procedure-environment procedure))))
        (else
         (error
          (s450error exp)))))

(define (remove-tag lst)
  (cond((equal? lst '()) '())
       ((pair? (car lst))
        (cons (car(cdr(car lst)))
              (remove-tag (cdr lst))))
       (else (cons (car lst)
                   (remove-tag (cdr lst))))))
;------------------------------------
;--- Handling procedure arguments ---
;------------------------------------

(define (list-of-values exps env)
  (let* ((proc-name (car exps)))
    (if(not(user-defined-procedure? (lookup-variable-value proc-name env)))
       (old-list-of-vals (cdr exps) env)
       (new-list-of-vals exps env))))

;might need to check for special form

(define (new-list-of-vals exps env)
  (let*((proc-name (car exps))
        (parameters (procedure-parameters (lookup-variable-value proc-name env))))
    (define (list-of-vals-iter new-exp parameters)
      (cond ((no-operands? new-exp) '())
            ((delayed? (car parameters))
             (cons (create-thunk (first-operand new-exp) env)
                   (list-of-vals-iter (rest-operands new-exp) (cdr parameters))))
            (else
             (cons (xeval (first-operand new-exp) env)
                   (list-of-vals-iter (rest-operands new-exp) (cdr parameters))))))
    (list-of-vals-iter (cdr exps) parameters)))

(define (old-list-of-vals exps env)
  (if (no-operands? exps)
      '()
      (cons (xeval (first-operand exps) env)
            (old-list-of-vals (rest-operands exps) env))))

;-------------------------------------
;--- defined? and locally defined? ---
;-------------------------------------
       
;lst is environment
(define (check-env-var exp lst)
  (let*((var (cadr exp)))
    (cond((equal? lst the-empty-environment) #f)
         ((and (symbol? var)
               (equal? var (car lst)))
          #t)
         (else
          (check-env-var exp (cdr lst))))))
  
(define (locally-defined? exp env)
  (let*((var (cadr exp)))
    (cond((and (symbol? var)
               (check-env-var exp (caar env))) #t)
         (else #f))))

(define (defined? exp env)
  (let*((var (cadr exp)))
    (cond((equal? env the-empty-environment) #f)
         ((and (symbol? var)
               (check-env-var exp (caar env))) #t)
         (else
          (defined? exp (cdr env))))))

;These will be helpful in some way to make unbound
;(define (frame-variables frame) (car frame))
;(define (frame-values frame) (cdr frame))

(define (make-unbound! exp env)
  (let*((vars (frame-variables (first-frame env)))
        (vals (frame-values (first-frame env)))
        (expr (cadr exp)))
    (define (local-iter vars vals env)
    (cond((or(equal? vars '())
             (equal? vals '()))
          (local-iter (frame-variables (first-frame (cdr env)))
                      (frame-values (first-frame (cdr env)))
                      (cdr env))) ;when you reach the end of local environemt move to next environement
         ((equal? env the-empty-environment) 'ok)
         ((equal? (car vars) expr)
          (set-car! vars 0)
          (set-car! vals 0))
         (else (local-iter (cdr vars) (cdr vals) env))))
    (local-iter vars vals env)))        

(define (locally-make-unbound! exp env)
  (let*((vars (frame-variables (first-frame env)))
        (vals (frame-values (first-frame env)))
        (expr (cadr exp)))
    (define (local-iter vars vals)
    (cond((or(equal? vars '())
             (equal? vals '()))
          "variable does not exist")
         ((equal? (car vars) expr)   
          (set-car! vars 0)
          (set-car! vals 0)) ; just set to zero 
         (else (local-iter (cdr vars) (cdr vals)))))
    (local-iter vars vals)))
         
   
(define (eval-if exp env)
  (if (true? (xeval (if-predicate exp) env))
      (xeval (if-consequent exp) env)
      (xeval (if-alternative exp) env)))

(define (eval-sequence exps env)
  (cond ((last-exp? exps) (xeval (first-exp exps) env))
        (else (xeval (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))

(define (eval-assignment exp env)
  (let ((name (assignment-variable exp)))
    (set-variable-value! name
			 (xeval (assignment-value exp) env)
			 env)
  name))    ;; A & S return 'ok

(define (eval-definition exp env)
  (let ((name (definition-variable exp)))
    (define-variable! name
      (xeval (definition-value exp) env)
      env)
  name))     ;; A & S return 'ok

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Representing expressions
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Numbers, strings, and booleans are all represented as themselves.
;;; (Not characters though; they don't seem to work out as well
;;; because of an interaction with read and display.)

(define (self-evaluating? exp)
  (or (number? exp)
      (string? exp)
      (boolean? exp)
      ))

;;; variables -- represented as symbols

(define (variable? exp) (symbol? exp))

;;; quote -- represented as (quote <text-of-quotation>)

(define (quoted? exp)
  (tagged-list? exp 'quote))

(define (text-of-quotation exp) (cadr exp))

(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      #f))

;;; assignment -- represented as (set! <var> <value>)

(define (assignment? exp) 
  (tagged-list? exp 'set!))

(define (assignment-variable exp) (cadr exp))

(define (assignment-value exp) (caddr exp))

;;; definitions -- represented as
;;;    (define <var> <value>)
;;;  or
;;;    (define (<var> <parameter_1> <parameter_2> ... <parameter_n>) <body>)
;;;
;;; The second form is immediately turned into the equivalent lambda
;;; expression.

(define (definition? exp)
  (tagged-list? exp 'define))

(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))

(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp)
                   (cddr exp))))
;-------------------------------
;----  Representing Thunks -----
;-------------------------------
  
(define (delayed exp env) (list 'delayed exp env))
(define (create-thunk exp env) (list 'thunk exp env))
(define (thunk-exp thunk) (cadr thunk))
(define (thunk-env thunk) (caddr thunk))
(define (delayed? obj) (tagged-list? obj 'delayed))
(define (thunk? obj) (tagged-list? obj 'thunk))
(define (evaluated-thunk? obj) (tagged-lisit obj 'evaluated))
(define (thunk-val evaluated-thunk) (cadr evaluated-thunk))
(define (force-it thunk) (xeval thunk-exp thunk-env))

;-------------------------------
;--- Representing Streams ------
;-------------------------------

;;stream has format (define ones (cons 1 (delay ones))
;; our expression would be (cons-stream elmt strm)

(define (cons-stream exp env) (cons (cadr exp) (force-it(caddr exp))))
(define (stream-car stream) (car stream))
(define (stream-cdr stream) (force-it (cdr stream)))
(define the-empty-stream '())
(define (stream-null? x) (null? x) )


;-----------------------------------------
;---- Representing Dynamic arguements ----
;-----------------------------------------

;dynamic environment global variable
;this environment is a list of frames
;any time you invoke a function push into to the dynamic environment using cons
;in a last in first out order
;what does xtend environment do and return?

(define the-dynamic-environment '())
(define (dynamic? exp) (tagged-list? exp 'dynamic))
                           
;;; lambda expressions -- represented as (lambda ...)
;;;
;;; That is, any list starting with lambda.  The list must have at
;;; least one other element, or an error will be generated.

(define (lambda? exp) (tagged-list? exp 'lambda))

(define (lambda-parameters exp) (cadr exp))
(define (lambda-body exp) (cddr exp))

(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

;;; conditionals -- (if <predicate> <consequent> <alternative>?)

(define (if? exp) (tagged-list? exp 'if))

(define (if-predicate exp) (cadr exp))

(define (if-consequent exp) (caddr exp))

(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      #f))

(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))


;;; sequences -- (begin <list of expressions>)

(define (begin? exp) (tagged-list? exp 'begin))

(define (begin-actions exp) (cdr exp))

(define (last-exp? seq) (null? (cdr seq)))
(define (first-exp seq) (car seq))
(define (rest-exps seq) (cdr seq))

(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))

(define (make-begin seq) (cons 'begin seq))


;;; procedure applications -- any compound expression that is not one
;;; of the above expression types.

(define (application? exp) (pair? exp))
(define (operator exp) (car exp))
(define (operands exp) (cdr exp))

(define (no-operands? ops) (null? ops))
(define (first-operand ops) (car ops))
(define (rest-operands ops) (cdr ops))


;;; Derived expressions -- the only one we include initially is cond,
;;; which is a special form that is syntactically transformed into a
;;; nest of if expressions.

(define (cond? exp) (tagged-list? exp 'cond))

(define (cond-clauses exp) (cdr exp))

(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))

(define (cond-predicate clause) (car clause))

(define (cond-actions clause) (cdr clause))

(define (cond->if exp)
  (expand-clauses (cond-clauses exp)))

(define (expand-clauses clauses)
  (if (null? clauses)
      #f                          ; no else clause -- return #f
      (let ((first (car clauses))
            (rest (cdr clauses)))
        (if (cond-else-clause? first)
            (if (null? rest)
                (sequence->exp (cond-actions first))
                (error "ELSE clause isn't last -- COND->IF "))
            (make-if (cond-predicate first)
                     (sequence->exp (cond-actions first))
                     (expand-clauses rest))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Truth values and procedure objects
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
;--------------------------
;------Truth values--------
;--------------------------

(define (true? x)
  (not (eq? x #f)))

(define (false? x)
  (eq? x #f))
  
;-----------------------------------
;----- Working with Procedures -----
;-----------------------------------

  
(define (make-procedure parameters body env)
  (list 'procedure parameters body env))

(define (user-defined-procedure? p)
  (tagged-list? p 'procedure))

(define (procedure-parameters p) (cadr p))
(define (procedure-body p) (caddr p))
(define (procedure-environment p) (cadddr p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Representing environments
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; An environment is a list of frames.

;----------------------------------
;----- Environment Selectors ------
;----------------------------------

(define (enclosing-environment env) (cdr env))
(define (first-frame env) (car env))
(define the-empty-environment '())

;;; Each frame is represented as a pair of lists:
;;;   1.  a list of the variables bound in that frame, and
;;;   2.  a list of the associated values.

(define (make-frame variables values)
  (cons variables values))

(define (frame-variables frame) (car frame))
(define (frame-values frame) (cdr frame))

(define (add-binding-to-frame! var val frame)
  (set-car! frame (cons var (car frame)))
  (set-cdr! frame (cons val (cdr frame))))

;;; Extending an environment

;----------------------------------
;---- xtend-environment -----------
;----------------------------------

;creating a new frame with a set of variables and values

(define (xtend-environment vars vals base-env)
  (if (= (length vars) (length vals))
      (cons (make-frame vars vals) base-env)
      (if (< (length vars) (length vals))
          (error "Too many arguments supplied ")
          (error "Too few arguments supplied "))))
  
;---------------------------------------------------
;---- Looking up a variable in an environment ------
;---------------------------------------------------

(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan vars vals)
      ;(display vars)
      ;(display vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (cond((thunk? vals) (force-it vals))
                  (else (car vals))))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable ")
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

;;; Setting a variable to a new value in a specified environment.
;;; Note that it is an error if the variable is not already present
;;; (i.e., previously defined) in that environment.

(define (set-variable-value! var val env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable -- SET! " var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

;;; Defining a (possibly new) variable.  First see if the variable
;;; already exists.  If it does, just change its value to the new
;;; value.  If it does not, define the new variable in the current
;;; frame.

(define (define-variable! var val env)
  (let ((frame (first-frame env)))
    (define (scan vars vals)
      (cond ((null? vars)
             (add-binding-to-frame! var val frame))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (scan (frame-variables frame)
          (frame-values frame))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 The initial environment
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This is initialization code that is executed once, when the the
;;; interpreter is invoked.

(define (setup-environment)
  (let ((initial-env
         (xtend-environment the-empty-environment
                            the-empty-environment
                            the-empty-environment)))
    initial-env))

;could use add-binding-to-frame

(define (install-primitive-procedure tag proc)
  (cond ((lookup-action tag)
         (error "This is a special form"))
        (else
         (set-car! (first-frame the-global-environment)
                   (cons tag (caar the-global-environment)))
         (set-cdr! (first-frame the-global-environment)
                   (cons (list 'primitive proc) (cdar the-global-environment)))
         tag)))

(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))

(define (primitive-implementation proc) (cadr proc))

(define (apply-primitive-procedure proc args)
  (apply (primitive-implementation proc) args))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 The main driver loop
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Note that (read) returns an internal representation of the next
;;; Scheme expression from the input stream.  It does NOT evaluate
;;; what is typed in -- it just parses it and returns an internal
;;; representation.  It is the job of the scheme evaluator to perform
;;; the evaluation.  In this case, our evaluator is called xeval.

(define input-prompt "s450==> ")
(define target '())
(define psswd 'still-here)
  
;---------------------
;---- Main-loop ------
;---------------------
  
(define (s450)
  (prompt-for-input input-prompt)
  (let ((input (read)))
    (call/cc (lambda (here) (set! target here)))
    (cond ((equal? psswd 'leave)
           (set! psswd 'still-here)
           (display "Thanks for using my metacircular evaluator"))
          ((eof-object? input)
           (exit))
          (else
           (let((output (xeval input the-global-environment)))
             (user-print output)
             (s450))))))
                        
(define (prompt-for-input string)
  (newline) (newline) (display string))

(define (exit) (set! psswd 'leave)
  (call/cc target))

(define (s450error args)
  (map (lambda (x) (display "Invalid arguement: ")
         (display x)(newline)) args))
  

;;; Note that we would not want to try to print a representation of the
;;; <procedure-env> below -- this would in general get us into an
;;; infinite loop.

(define (user-print object)
  (if (user-defined-procedure? object)
      (display (list 'user-defined-procedure
                     (procedure-parameters object)
                     (procedure-body object)
                     '<procedure-env>))
      (display object)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Here we go:  define the global environment and invite the
;;;        user to run the evaluator.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(display "... loaded the metacircular evaluator. (s450) runs it.") 
(newline)

(define the-global-environment (setup-environment))
(define tge the-global-environment)
  
;-----------------------------------------
;---- Installing Primtive Procedures -----
;-----------------------------------------

(install-primitive-procedure 'cons cons)
(install-primitive-procedure 'cdr cdr)
(install-primitive-procedure 'car car)
(install-primitive-procedure 'null? null?)
(install-primitive-procedure 'display display)
(install-primitive-procedure '* *)
(install-primitive-procedure '/ /)
(install-primitive-procedure '- -)
(install-primitive-procedure '+ +)
(install-primitive-procedure 'equal? equal?)
(install-primitive-procedure 'exit exit)
(install-primitive-procedure 'stream-car stream-car)
(install-primitive-procedure 'stream-cdr stream-cdr)
;(install-primitive-procedure 'stream-null stream-null)




;(s450)



