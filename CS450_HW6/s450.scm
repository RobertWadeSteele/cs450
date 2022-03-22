(#%require (only racket/base error))
;;; file: s450.scm
;;;
;;; Metacircular evaluator from chapter 4 of STRUCTURE AND
;;; INTERPRETATION OF COMPUTER PROGRAMS (2nd edition)
;;;
;;; Modified by kwn, 3/4/97
;;; Modified and commented by Carl Offner, 10/21/98 -- 10/12/04
;;;
;;; This code is the code for the metacircular evaluator as it appears
;;; in the textbook in sections 4.1.1-4.1.4, with the following
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;      lookup table implementation for special forms
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (make-table) 
  (let ((local-table '())) 
      
    (define (lookup type records) 
      (if (null? records) #f
          (let ((rtype (caar records)))
            (if (equal? type rtype)
                (car records)
                (lookup type (cdr records))))))

    (define (insert dat)
      (let ((record (lookup (type-of dat) local-table)))
        (if (false? record)
            (begin (set! local-table (append (list dat) local-table))
                   (type-of dat)))))
    
    (define (get type)
      (lookup type local-table))

    (define (put type function)
      (insert (cons type function)))

    (define (print)
      (display local-table)
      (newline))
    
    (define (dispatch m) 
      (cond ((eq? m 'get-proc) get)
            ((eq? m 'put-proc) put)
            ((eq? m 'print-proc) print)
            (else (error "Undefined operation -- TABLE " m)))) 
    dispatch))

(define special-forms (make-table))
(define lookup-special-form (special-forms 'get-proc))
(define insert-special-form (special-forms 'put-proc))
(define print-special-forms (special-forms 'print-proc))

; returns what type the expression represents #f if it is not an expression
(define (type-of exp)
  (if (pair? exp) (car exp) #f))

; lookup a type in the special-form table and return its action #f if type is not a special form
(define (lookup-action type)
  (if (false? type) #f
      (let ((action (lookup-special-form type)))
        (if action (cdr action) #f))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 xeval and xapply -- the kernel of the metacircular evaluator
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (xeval exp env)
  (let ((action (lookup-action (type-of exp))))
    (if action
        (action exp env)
        (cond ((special-form? exp) (string-append "Special form: " (symbol->string exp)))
              ((self-evaluating? exp) exp)
              ((variable? exp) (lookup-variable-value exp env))
              ((application? exp)
               (xapply (xeval (operator exp) env)
                       (list-of-values (operands exp) env)))
              (else
               (error "Unknown expression type -- XEVAL " exp))))))

(define (xapply procedure arguments)
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure procedure arguments))
        ((user-defined-procedure? procedure)
         (eval-sequence
          (procedure-body procedure)
          (xtend-environment
           (procedure-parameters procedure)
           arguments
           (procedure-environment procedure))))
        (else
         (error
          "Unknown procedure type -- XAPPLY " procedure))))

; install a special-form in the lookup table
(define (install-special-form name function)
  (cond ((special-form? name) (error "Reinstalling special form -- " name))
        ((defined? name) (error "Installing a special form with a defined name -- " name)))
  (insert-special-form name function))

; expression to check if a name is a special form
(define (special-form? name)
  (if (lookup-action name) #t #f))

;;; Handling procedure arguments

(define (list-of-values exps env)
  (if (no-operands? exps)
      '()
      (cons (xeval (first-operand exps) env)
            (list-of-values (rest-operands exps) env))))

;;; These functions, called from xeval, do the work of evaluating some
;;; of the special forms:

(define (eval-if exp env)
  (if (true? (xeval (if-predicate exp) env))
      (xeval (if-consequent exp) env)
      (xeval (if-alternative exp) env)))

(define (eval-sequence exps env)
  (cond ((last-exp? exps) (xeval (first-exp exps) env))
        (else (xeval (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))

(define (eval-assignment exp env)
  (if (special-form? (cadr exp)) (error "Assigning to a special form name -- " (cadr exp)))
  (let ((name (assignment-variable exp)))
    (set-variable-value! name
                         (xeval (assignment-value exp) env)
                         env)
    name))    ;; A & S return 'ok

(define (eval-definition exp env)
  (let ((var (definition-variable exp)))
    (cond ((special-form? var) (error "Defining a special form name -- " var)))
    (let ((name (definition-variable exp)))  
      (define-variable! name
        (xeval (definition-value exp) env)
        env)
      name)))     ;; A & S return 'ok

(define (eval-lambda exp env)
  (make-procedure (lambda-parameters exp)
                  (lambda-body exp)
                  env))

(define (eval-begin exp env)
  (eval-sequence (begin-actions exp) env))

(define (eval-cond exp env)
  (xeval (cond->if exp) env))

(define (eval-quote exp env)
  (text-of-quotation exp))

(define eval-load
  (lambda (exp env)
    (define (filename exp) (cadr exp))
    (define thunk (lambda ()
                    (readfile)
                    ))
    (define readfile (lambda()
                       (let ((item (read)))
                         (if (not (eof-object? item))
                             (begin
                               (xeval item env)
                               (readfile))))
                       ))
    (with-input-from-file (filename exp) thunk)
    (filename exp)      ; return the name of the file - why not?
    ))

(define (symbol exp) (cadr exp))

(define (eval-defined exp env)
  (let ((var (symbol exp)))
    (define (env-loop env)
      (cond ((eq? env the-empty-environment) #f)
            ((has-binding-in-frame? var (first-frame env)) #t)
            (else (env-loop (enclosing-environment env)))))
    (env-loop env)))

(define (eval-locally-defined exp env)
  (has-binding-in-frame? (symbol exp) (first-frame env)))

(define (eval-make-unbound exp env)
  (let ((var (symbol exp)))
    (define (env-loop env)
      (let ((frame (first-frame env)))
        (cond ((eq? env the-empty-environment) 'ok)
              ((has-binding-in-frame? var frame) (remove-binding-from-frame! var frame))
              (else (env-loop (enclosing-environment env))))))
    (env-loop env)))

(define (eval-locally-make-unbound exp env)
  (remove-binding-from-frame! (symbol exp) (first-frame env)))
  
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
                (error "ELSE clause isn't last -- COND->IF "
                       clauses))
            (make-if (cond-predicate first)
                     (sequence->exp (cond-actions first))
                     (expand-clauses rest))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Truth values and procedure objects
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Truth values

(define (true? x)
  (not (eq? x #f)))

(define (false? x)
  (eq? x #f))


;;; Procedures

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

(define (set-binding-in-frame! var val frame)
  (define (scan vars vals)
    (cond ((null? vars) (error "Cannot change binding - binding does not exist -- " var))
          ((eq? var (car vars)) (set-car! vals val) var)
          (else (scan (cdr vars) (cdr vals)))))
  (scan (frame-variables frame)
        (frame-values frame)))

(define (remove-binding-from-frame! var frame)
  (let ((temp-vars '())
        (temp-vals '()))
    (define (scan var vars vals)
      (cond ((null? vars) (set-car! frame temp-vars) (set-cdr! frame temp-vals))
            ((eq? var (car vars)) (scan var (cdr vars) (cdr vals)))
            (else (set! temp-vars (cons (car vars) temp-vars))
                  (set! temp-vals (cons (car vals) temp-vals))
                  (scan var (cdr vars) (cdr vals)))))
    (scan var
          (frame-variables frame)
          (frame-values frame)))
  'ok)

(define (has-binding-in-frame? var frame)
  (define (scan var vars)
    (cond ((null? vars) #f)
          ((eq? var (car vars)) #t)
          (else (scan var (cdr vars)))))
  (scan var (frame-variables frame)))

;;; Extending an environment

(define (xtend-environment vars vals base-env)
  (if (= (length vars) (length vals))
      (cons (make-frame vars vals) base-env)
      (if (< (length vars) (length vals))
          (error "Too many arguments supplied " vars vals)
          (error "Too few arguments supplied " vars vals))))

;;; Looking up a variable in an environment

(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (car vals))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable " var)
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
         (xtend-environment '()
                            '()
                            the-empty-environment)))
    initial-env))

;;; Define the primitive procedures

(define the-global-environment (setup-environment))

(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))

(define (primitive-implementation proc) (cadr proc))

(define (install-primitive-procedure name action)
  (if (special-form? name)
      (error "Installing a primitive procedure with the name of a special form -- " name)
      (let ((frame (first-frame the-global-environment)))
        (define (scan names actions)
          (cond ((null? names)
                 (add-binding-to-frame! name (list 'primitive action) frame))
                ((eq? name (car names))
                 (set-car! actions (list 'primitive action)))
                (else (scan (cdr names) (cdr actions)))))
        (scan (frame-variables frame)
              (frame-values frame))
        name)))

(define (install-primitive-procedure name action)
  (let ((frame (first-frame the-global-environment))
        (action (list 'primitive action)))
    (cond ((special-form? name) (error "Installing a primitive procedure with the name of a special form -- " name))
          ((has-binding-in-frame? name frame) (set-binding-in-frame! name action frame))
          (else (add-binding-to-frame! name action frame))))
  name)

(define (primitive? name)
  (has-binding-in-frame? name (first-frame the-global-environment)))

;;; Here is where we rely on the underlying Scheme implementation to
;;; know how to apply a primitive procedure.

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

(define (s450)
  (prompt-for-input input-prompt)
  (let ((input (read)))
    (let ((output (xeval input the-global-environment)))
      (user-print output)))
  (s450))

(define (prompt-for-input string)
  (newline) (newline) (display string))

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

(define (defined? name)
  (has-binding-in-frame? name (first-frame the-global-environment)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Here we go:  define the global environment and invite the
;;;        user to run the evaluator.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;(define the-global-environment (setup-environment))

; install special forms
(install-special-form 'if eval-if)
(install-special-form 'begin eval-begin)
(install-special-form 'set! eval-assignment)
(install-special-form 'define eval-definition)
(install-special-form 'lambda eval-lambda)
(install-special-form 'cond eval-cond)
(install-special-form 'quote eval-quote)
(install-special-form 'load eval-load)
(install-special-form 'defined? eval-defined)
(install-special-form 'locally-defined? eval-locally-defined)
(install-special-form 'make-unbound! eval-make-unbound)
(install-special-form 'locally-make-unbound! eval-locally-make-unbound)

; install primitives
(install-primitive-procedure 'car car)
(install-primitive-procedure 'cdr cdr)
(install-primitive-procedure 'cons cons)
(install-primitive-procedure 'null? null?)
(install-primitive-procedure '+ +)
(install-primitive-procedure '- -)
(install-primitive-procedure '* *)
(install-primitive-procedure '/ /)
(install-primitive-procedure '< <)
(install-primitive-procedure '> >)
(install-primitive-procedure '= =)
(install-primitive-procedure 'display display)
(install-primitive-procedure 'newline newline)

;(print-special-forms)

(display "... loaded the metacircular evaluator. (s450) runs it.")
(newline)