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
;;;                                                               ;;;
;;;	 The Kernel of the Metacircular Evaluator                 ;;;
;;;                                                               ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; evaluates the expression within the given environment
(define (xeval exp env)
  (let ((action (lookup-action (type-of exp))))
    (if action
        (action exp env)
        (cond ((self-evaluating? exp) exp)
              ((exit-code? exp) (interrupt exp))
              ((eof-object? exp) (interrupt exp))
              ((special-form? exp) (string-append "Special form: " (symbol->string exp)))
              ((variable? exp) (lookup-variable-value exp env))
              ((application? exp)
               (xapply (xeval (operator exp) env) (operands exp) env))
              (else
               (s450error "Not an expression -- " exp))))))

; applies a procedure to a list of arguments within the given environment
(define (xapply procedure arguments environment)
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure procedure (list-of-values arguments environment)))
        ((user-defined-procedure? procedure)
         (let ((return-val (eval-sequence
                            (procedure-body procedure)
                            (xtend-environment
                             (resolve-params (procedure-parameters procedure))
                             (resolve-args (procedure-parameters procedure) arguments environment)
                             environment))))
           (set! the-dynamic-environment (cdr the-dynamic-environment))
           return-val))
        (else
         (s450error "Not a procedure -- " procedure))))

(define (first-param params) (car params))

(define (rest-params params) (cdr params))

(define (first-arg args) (car args))

(define (rest-args args) (cdr args))

(define (resolve-args params args env)
  (define (resolve params args)
    (if (null? args) '()
        (let ((param (first-param params)) (arg (first-arg args))
              (rem-params (rest-params params)) (rem-args (rest-args args)))
          (cond ((delayed? param) (cons (create-thunk arg env) (resolve rem-params rem-args)))
                ((dynamic? param) (cons (xeval arg the-dynamic-environment) (resolve rem-params rem-args)))
                ((reference? param) (if (symbol? arg)
                                        (cons (create-reference arg env) (resolve rem-params rem-args))
                                        (s450error "Reference parameter must be a symbol -- " arg)))
                (else (cons (xeval arg env) (resolve rem-params rem-args)))))))
  (cond ((< (length params) (length args)) (s450error "Too many arguments. Expected " (length params) " but got " (length args)))
        ((> (length params) (length args)) (s450error "Too few arguments. Expected " (length params) " but got " (length args)))
        (else (resolve params args))))

(define (resolve-params params)
  (if (null? params)
      '()
      (let ((param (first-param params)))
        (cond ((delayed? param) (set! param (symbol param)))
              ((dynamic? param) (set! param (symbol param)))
              ((reference? param) (set! param (symbol param))))
        (cons param (resolve-params (rest-params params))))))

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
  (if (special-form? (cadr exp)) (s450error "Assigning to a special form name -- " (cadr exp)))
  (let ((name (assignment-variable exp)))
    (set-variable-value! name
                         (xeval (assignment-value exp) env)
                         env)
    name))    ;; A & S return 'ok

(define (eval-definition exp env)
  (let ((var (definition-variable exp)))
    (cond ((special-form? var) (s450error "Defining a special form name -- " var)))
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
;;;                                                               ;;;
;;;               Special Form Lookup Table                       ;;;
;;;                                                               ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; creates a new table and returns the dispatch to access said table
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
            (else (s450error "Undefined operation -- TABLE " m)))) 
    dispatch))

; defines a special form table to hold special forms
(define special-forms (make-table))

; passes through a type to lookup
(define lookup-special-form (special-forms 'get-proc))

; passes through a type and an action to insert
(define insert-special-form (special-forms 'put-proc))

; passes through a request to print the special form table
(define print-special-forms (special-forms 'print-proc))

; evaluates to the type of the expression or false if it is not an expression
(define (type-of exp)
  (if (expression? exp) (car exp) #f))

; checks if the value is an expression 
(define (expression? exp) (pair? exp))

; lookup a type in the special-form table and return its action or false if it does not exist
(define (lookup-action type)
  (let ((action (lookup-special-form type)))
    (if action (cdr action) action)))

; install a special-form in the lookup table
(define (install-special-form name function)
  (cond ((special-form? name) (s450error "Reinstalling a special form -- " name))
        ((defined? name) (s450error "Installing a special form with a defined name -- " name))
        (else (insert-special-form name function))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                               ;;;
;;;	                 Expressions                              ;;;
;;;                                                               ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; determines if the expression evaluates to itself (except characters)
(define (self-evaluating? exp)
  (or (number? exp)
      (string? exp)
      (boolean? exp)))

; determines if the expression is a variable (represented as symbols)
(define (variable? exp) (symbol? exp))

; determines if the expression is a quoted expression
(define (quoted? exp)
  (tagged-list? exp 'quote))

; accesses the text of a quoted expression
(define (text-of-quotation exp) (cadr exp))

; determines if the expression is a list with first element equal to tag
(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      #f))

;------------------------------ Assignment ------------------------------;

; determines if the expression is an assignment expression
(define (assignment? exp) 
  (tagged-list? exp 'set!))

; accesses the variable of an assignment expression
(define (assignment-variable exp) (cadr exp))

; accesses the value of an assignment expression
(define (assignment-value exp) (caddr exp))

;------------------------------ Definitions ------------------------------;
;;; represented as:
;;;    (define <var> <value>)
;;;  or:
;;;    (define (<var> <parameter_1> <parameter_2> ... <parameter_n>) <body>)
;;; The second form is immediately turned into the equivalent lambda
;;; expression.

; determines if the expression is a definition expression
(define (definition? exp)
  (tagged-list? exp 'define))

; accesses the variable of a definition expression
(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))

; accesses the value of a definition expression
(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp)
                   (cddr exp))))

;------------------------------ Lambdas ------------------------------;
;;; represented as: (lambda ...)
;;;
;;; That is, any list starting with lambda.  The list must have at
;;; least one other element, or an error will be generated.

; determines if the expression is a lambda expression
(define (lambda? exp) (tagged-list? exp 'lambda))

; accesses the parameters of a lambda expression
(define (lambda-parameters exp) (cadr exp))

; accesses the body of a lambda expression
(define (lambda-body exp) (cddr exp))

; creates a lambda with the given parameters and body
(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

;------------------------------ Conditionals ------------------------------;
;;; represented as: (if <predicate> <consequent> <alternative>?)

; determines if the expression is an if statement
(define (if? exp) (tagged-list? exp 'if))

; accesses the predicate of an if statement
(define (if-predicate exp) (cadr exp))

; accesses the consequent of an if statement
(define (if-consequent exp) (caddr exp))

; accesses the alternative of an if statement
(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      #f))

; creates an if statement given a predicate consequent and alternative
(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))

;------------------------------ Sequences ------------------------------;
;;; represented as: (begin <list of expressions>)

; determines if the expression is a begin statement
(define (begin? exp) (tagged-list? exp 'begin))

; accesses the actions of a begin statement
(define (begin-actions exp) (cdr exp))

; determines if this is the last expression in a sequence
(define (last-exp? seq) (null? (cdr seq)))

; accesses the first expression in a sequence
(define (first-exp seq) (car seq))

; accesses the rest of the expressions in a sequence
(define (rest-exps seq) (cdr seq))

; converts a sequence to an expression
(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))

; creates a begin statement given a sequence of expressions
(define (make-begin seq) (cons 'begin seq))

;------------------------------ Procedure Applications ------------------------------;
;;; any compound expression that is not one of the above expression types.

; determines if the expression is an application
(define (application? exp) (pair? exp))

; accesses the operator of an expression
(define (operator exp) (car exp))

; accesses the operands of an expression
(define (operands exp) (cdr exp))

; checks if the operands list has no operands remaining
(define (no-operands? ops) (null? ops))

; accesses the first operand in a list of operands
(define (first-operand ops) (car ops))

; accesses the rest of the operands in a list of operands
(define (rest-operands ops) (cdr ops))

;------------------------------ Derived Expressions ------------------------------;
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
                (s450error "ELSE clause isn't last -- COND->IF "
                       clauses))
            (make-if (cond-predicate first)
                     (sequence->exp (cond-actions first))
                     (expand-clauses rest))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                               ;;;
;;;             Truth Values and Procedure Objects                ;;;
;;;                                                               ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;------------------------------ Truth Values ------------------------------;

; checks if an argument is true
(define (true? x)
  (not (eq? x #f)))

; checks if an argument is false
(define (false? x)
  (eq? x #f))


;------------------------------ Procedures ------------------------------;

; creats a procedure given a body and an environment
(define (make-procedure parameters body env)
  (list 'procedure parameters body env))

; checks if the argument is a user defined procedure
(define (user-defined-procedure? p)
  (tagged-list? p 'procedure))

(define (procedure-parameters p) (cadr p))
(define (procedure-body p) (caddr p))
(define (procedure-environment p) (cadddr p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                               ;;;
;;;                   Delayed Evaluation                          ;;;
;;;                                                               ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accesses the value of a thunk
(define (thunk-val thunk) (cadr thunk))

; accesses the environment of a thunk
(define (thunk-env thunk) (caddr thunk))

; creates a thunk object given a value and an environment
(define (create-thunk val env)
  (list 'thunk val env))

; forces the evaluation of a thunk
(define (force-thunk thunk)
  (xeval (thunk-val thunk) (thunk-env thunk)))

; checks if the expression is a thunk
(define (thunk? exp)
  (tagged-list? exp 'thunk))

; checks if an expression is delayed
(define (delayed? exp)
  (tagged-list? exp 'delayed))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                               ;;;
;;;                   Dynamic Evaluation                          ;;;
;;;                                                               ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; check if an expression is dynamic
(define (dynamic? exp)
  (tagged-list? exp 'dynamic))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                               ;;;
;;;                 Referential Evaluation                        ;;;
;;;                                                               ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; check if an expression is a reference
(define (reference? exp)
  (tagged-list? exp 'reference))

; accesses the symbol of a reference expression
(define (reference-symbol ref) (cadr ref))

; accesses the environment of a reference expression
(define (reference-env ref) (caddr ref))

; creates a reference expression
(define (create-reference symbol env)
  (list 'reference symbol env))

; evaluates a reference expression
(define (eval-reference ref)
  (xeval (reference-symbol ref) (reference-env ref)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                               ;;;
;;;	            Environment Representations                   ;;;
;;;                                                               ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Environments are represented as lists of frames.

(define (enclosing-environment env) (cdr env))

(define (first-frame env) (car env))

(define the-empty-environment '())

(define the-dynamic-environment the-empty-environment)

;;; Frames are represented as a pair of lists.
;;;   1.  a list of the variables bound in that frame, and
;;;   2.  a list of the associated values.

(define (make-frame variables values)
  (cons variables values))

(define (frame-variables frame) (car frame))
(define (frame-values frame) (cdr frame))

(define (add-binding-to-frame! var val frame)
  (set-car! frame (cons var (car frame)))
  (set-cdr! frame (cons val (cdr frame))))

; sets the binding of a given variable to a given value in a given frame
(define (set-binding-in-frame! var val frame)
  (define (scan vars vals)
    (cond ((null? vars) (s450error "Cannot change binding - binding does not exist -- " var))
          ((eq? var (car vars)) (set-car! vals val) var)
          (else (scan (cdr vars) (cdr vals)))))
  (scan (frame-variables frame)
        (frame-values frame)))

; removes the binding of a given variable from a given frame
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

; determines if the given variable has a binding in the given frame
(define (has-binding-in-frame? var frame)
  (define (scan var vars)
    (cond ((null? vars) #f)
          ((eq? var (car vars)) #t)
          (else (scan var (cdr vars)))))
  (scan var (frame-variables frame)))

;;; Extending an environment

(define (xtend-environment vars vals base-env)
  (if (= (length vars) (length vals))
      (let ((new-frame (make-frame vars vals)))
        (set! the-dynamic-environment (cons new-frame the-dynamic-environment))
        (cons new-frame base-env))
      (if (< (length vars) (length vals))
          (s450error "Too many arguments supplied " vars vals)
          (s450error "Too few arguments supplied " vars vals))))

;;; Looking up a variable in an environment

(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (cond ((reference? (car vals)) (eval-reference (car vals)))
                   ((thunk? (car vals)) (force-thunk (car vals)))
                   (else (car vals))))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (s450error "Unbound variable " var)
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
             (if (reference? (car vals))
                 (set-variable-value! (reference-symbol (car vals)) val (reference-env (car vals)))
                 (set-car! vals val)))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (s450error "Unbound variable -- SET! " var)
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

; -------------------------- Streams --------------------------------;
(define (stream-val exp) (cadr exp))

(define (stream-thunk exp) (caddr exp))

(define (eval-cons-stream exp env)
  (cons-stream (xeval (stream-val exp) env) (create-thunk (stream-thunk exp) env)))

; creates a new stream (<value> <thunk>)
(define (cons-stream val stream)
  (cons val stream))

; retrieves the value of a stream
(define (stream-car stream) (car stream))

; forces the next element in a stream
(define (stream-cdr stream) (force-thunk (cdr stream)))

; accesses the first element in a stream
(define (stream-null? stream) (null? stream))

; defines the empty stream
(define the-empty-stream '())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                               ;;;
;;;	              The Initial Environment                     ;;;
;;;                                                               ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; creates a new environment with one empty frame rooted in the-empty-environment
(define (setup-environment)
  (let ((initial-env
         (xtend-environment '()
                            '()
                            the-empty-environment)))
    initial-env))

; defines the global environment
(define the-global-environment (setup-environment))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                               ;;;
;;;	               Primitive Procedures                       ;;;
;;;                                                               ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; checks if a procedure is a primitive procedure
(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))

; extracts the procedure from a tagged primitive procedure
(define (primitive-implementation proc) (cadr proc))

; apply a primitive procedure to a list of arguments
(define (apply-primitive-procedure proc args)
  (apply (primitive-implementation proc) args))

; installs a primitive procedure in the global environment
(define (install-primitive-procedure name action)
  (let ((frame (first-frame the-global-environment))
        (action (list 'primitive action)))
    (cond ((special-form? name) (s450error "Installing a primitive procedure with the name of a special form -- " name))
          ((has-binding-in-frame? name frame) (set-binding-in-frame! name action frame))
          (else (add-binding-to-frame! name action frame))))
  name)

; checks if a value is a primitive name (not used)
(define (primitive? name)
  (if (has-binding-in-frame? name (first-frame the-global-environment))
      (primitive-procedure? (lookup-variable-value name the-global-environment))
      #f))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                               ;;;
;;;	                   System Loop                            ;;;
;;;                                                               ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; the main loop for the s450 user prompt
(define (s450)
  (let ((code (call/cc
               (lambda (here)
                 (set! interrupt here)))))
    (cond ((exit-code? code) (exit))
          ((eof-object? code) (eof-exit))
          ((error-code? code) (handle-error code))
          (else (set! the-dynamic-environment the-global-environment)
                (prompt-for-input input-prompt)
                (let ((input (read)))
                  (let ((output (xeval input the-global-environment)))
                    (user-print output)))
                (s450)))))

; user prompt
(define input-prompt "s450==> ")

; prompts the user for input
(define (prompt-for-input string)
  (newline) (newline) (display string))

; prints the output of xeval to the console
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
;;;                                                               ;;;
;;;                   Control Flow Procedures                     ;;;
;;;                                                               ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; tag used for call/cc jumps
(define interrupt '())

; redefining call/cc for ease of use/readability
(define call/cc call-with-current-continuation)

; determines if the code is an exit code
(define (exit-code? code)
  (tagged-list? code 'exit))

; determines if the code is an error code
(define (error-code? code)
  (tagged-list? code 's450error))

; throws an error
(define (s450error . args)
  (interrupt (cons 's450error (cons ': args))))

; handles an error and resumes normal function
(define (handle-error code)
  (if (null? code)
      (s450)
      (begin (display (car code))
             (handle-error (cdr code)))))

; exits the s450 prompt cleanly
(define (exit) (display "Exiting s450 user prompt.") (newline))

; exits the s450 prompt cleanly after indicating eof was found
(define (eof-exit)
  (display "Found EOF. ")
  (exit))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                               ;;;
;;;	       Install Primitives and Special Forms               ;;;
;;;                                                               ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; install special forms
(install-special-form 'if eval-if)
(install-special-form 'set! eval-assignment)
(install-special-form 'cond eval-cond)
(install-special-form 'load eval-load)
(install-special-form 'begin eval-begin)
(install-special-form 'quote eval-quote)
(install-special-form 'lambda eval-lambda)
(install-special-form 'define eval-definition)
(install-special-form 'defined? eval-defined)
(install-special-form 'cons-stream eval-cons-stream)
(install-special-form 'make-unbound! eval-make-unbound)
(install-special-form 'locally-defined? eval-locally-defined)
(install-special-form 'locally-make-unbound! eval-locally-make-unbound)

; install primitives
(install-primitive-procedure '+ +)
(install-primitive-procedure '- -)
(install-primitive-procedure '* *)
(install-primitive-procedure '/ /)
(install-primitive-procedure '< <)
(install-primitive-procedure '> >)
(install-primitive-procedure '= =)
(install-primitive-procedure 'car car)
(install-primitive-procedure 'cdr cdr)
(install-primitive-procedure 'cons cons)
(install-primitive-procedure 'null? null?)
(install-primitive-procedure 'equal? equal?)
(install-primitive-procedure 'display display)
(install-primitive-procedure 'newline newline)
(install-primitive-procedure 'stream-car stream-car)
(install-primitive-procedure 'stream-cdr stream-cdr)
(install-primitive-procedure 'stream-null? stream-null?)

; invite the user to run
(display "... loaded the metacircular evaluator. (s450) runs it.")
(newline)