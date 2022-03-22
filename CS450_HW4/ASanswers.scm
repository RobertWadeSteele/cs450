;; HW4 - part 1 and optimal BST

;;; Answer part 1 here.

; ---------------------Question 1--------------------------
;;; Original:
(define (make-account balance)
  (define (withdraw amount)
    (if (>= balance amount)
        (begin (set! balance (- balance amount))
               balance)
        "Insufficient funds"))
  (define (deposit amount)
    (set! balance (+ balance amount))
    balance)
  (define (dispatch m)
    (cond ((eq? m 'withdraw) withdraw)
          ((eq? m 'deposit) deposit)
          (else (error "Unknown request -- MAKE-ACCOUNT"
                       m))))
  dispatch)

;;; First version:
(define make-account-lambda
  (lambda (balance)
    (define withdraw
      (lambda (amount)
        (if (>= balance amount)
            (begin (set! balance (- balance amount))
                   balance)
            "Insufficient funds")))
    (define deposit
      (lambda (amount)
        (set! balance (+ balance amount))
        balance))
    (lambda (m)
      (cond ((eq? m 'withdraw) withdraw)
            ((eq? m 'deposit) deposit)
            (else (error "Unknown request -- MAKE-ACCOUNT"
                         m))))))

;;; Second version:
(define make-account-inline
  (lambda (balance)
    (lambda (m)
      (cond ((eq? m 'withdraw) (lambda (amount)
                                 (if (>= balance amount)
                                     (begin (set! balance (- balance amount))
                                            balance)
                                     "Insufficient funds")))
            ((eq? m 'deposit) (lambda (amount)
                                (set! balance (+ balance amount))
                                balance))
            (else (error "Unknown request -- MAKE-ACCOUNT"
                         m))))))

;;; Third version:
(define make-account-inline-factored
  (lambda (balance)
    (lambda (m)
      (lambda (amount)
        (cond ((eq? m 'withdraw)
               (if (>= balance amount)
                   (begin (set! balance (- balance amount))
                          balance)
                   "Insufficient funds"))
              ((eq? m 'deposit) 
               (set! balance (+ balance amount))
               balance)
              (else (error "Unknown request -- MAKE-ACCOUNT"
                           m)))))))

;-----------------------------Question 3------------------------------------
(define make-monitored
  ((lambda (counter)
     (lambda (f)
       (lambda (val)
         (cond ((eq? val 'how-many-calls?) counter)
               ((eq? val 'reset-count) (set! counter 0))
               (else (set! counter (+ counter 1))
                     (f val))))))
   0))

;-----------------------------Question 4------------------------------------
(define make-pw-account
  (lambda (balance password)
    ((lambda (account)
       (lambda (pwd instruction)
         (if (eq? pwd password)
             (account instruction)
             (lambda (process . arg) "Invalid Password"))))
     (make-account balance))))

(define pw (make-pw-account 100 'pass))
((pw 'pass 'withdraw) 20)
((pw 'passs 'withdraw) 30)
;----------------------------------------------------------------------------;
;------------------------------Part 2----------------------------------------;
;----------------------------------------------------------------------------;
;; read-file produces a list whose elements are the expressions in the file.
(define (read-file)
  (let ((expr (read)))
    (if (eof-object? expr)
        '()
        (cons expr (read-file)))))

;`(define data (with-input-from-file "keys.dat" read-file))

(define (entry tree) (car tree))
(define (key entry) (car entry))
(define (freq entry) (cadr entry))
(define (left-branch tree) (cadr tree)) 
(define (right-branch tree) (caddr tree)) 


(define (make-tree entry left right) 
  (list entry left right))
  
(define (adjoin-set x set) 
  (cond ((null? set) (make-tree x '() '()))
        (else
         (let ((rkey (car (entry set))))
           (cond ((= (car x) rkey) set) 
                 ((< (car x) rkey)
                  (make-tree (entry set) 
                             (adjoin-set x (left-branch set)) 
                             (right-branch set))) 
                 ((> (car x) rkey) 
                  (make-tree (entry set) 
                             (left-branch set) 
                             (adjoin-set x (right-branch set)))))))))

;; A skeleton for BST. You may add things here 
(define (make-table) 
  (let ((local-table '())) 
      
    (define (lookup key records) 
      (if (null? records) #f
          (let ((rkey (car (entry records))))
            (cond ((= key rkey) (entry records)) 
                  ((< key rkey) (lookup key (left-branch records))) 
                  ((> key rkey) (lookup key (right-branch records))))))) 
      
    (define (insert! dat)
      (let ((rkey (car dat)))
        (let ((record (lookup rkey local-table))) 
          (if record 
              (set-cdr! record (freq dat)) 
              (set! local-table (adjoin-set dat local-table)))))) 
      
    (define (get key) 
      (lookup key local-table))
     
    ;build table from data. Data is a list of (key freq)
    (define (build-tree-from-data the-keys)
      (if (null? the-keys) 'ok
          (begin (insert! (car the-keys))
                 (build-tree-from-data (cdr the-keys)))))
     
    (define (dispatch m) 
      (cond ((eq? m 'get-proc) get) 
            ((eq? m 'insert-proc) insert!)
            ((eq? m 'build-proc) build-tree-from-data)
            ((eq? m 'print) local-table) 
            (else (error "Undefined operation -- TABLE" m))))
    dispatch))
  
(define table (make-table)) 
(define get (table 'get-proc)) 
(define put (table 'insert-proc))
(define build (table 'build-proc))
(define print (table 'print))

;;; Put your naive and DP procedures here.
;----------------------------------MIN COST NAIVE--------------------------------------------------------------------
;;; min-cost-naive function (entry point for min-cost-naive-recurse)
(define (min-cost-naive data)
  (if (null? data)
      0
      (min-cost-naive-recurse 1 '() (car data) (cdr data))))

;;; recursive helper function of min-cost-naive
(define (min-cost-naive-recurse level left root right)
  (let ((root-cost (+ (* level (cadr root))
                      (if (null? left)
                          0
                          (min-cost-naive-recurse (+ level 1) '() (car left) (cdr left)))
                      (if (null? right)
                          0
                          (min-cost-naive-recurse (+ level 1) '() (car right) (cdr right)))))
        (best-alternative (if (null? right)
                              1000000000000
                              (min-cost-naive-recurse level (append left (cons root '())) (car right) (cdr right)))))
    (if (< root-cost best-alternative)
        root-cost
        best-alternative)))
;-------------------------------------------------LOOKUP TABLE--------------------------------------------------------------------
;;; defines a lookup table for DP min-cost
(define (make-lookup-table)
  (let ((local-table (list 'lookup )))

    (define (assoc key table)
      (cond ((null? table) #f)
            ((equal? key (caar table)) (car table))
            (else (assoc key (cdr table)))))
    
    (define (lookup level key table)
      (let ((subtable (assoc level (cdr table))))
        (if subtable
            (let ((record (assoc key (cdr subtable))))
              (if record
                  (cdr record)
                  #f))
            #f)))
    
    (define (insert! level key value table)
      (let ((subtable (assoc level (cdr table))))
        (if subtable
            (let ((record (assoc key (cdr subtable))))
              (if record
                  (set-cdr! record value)
                  (set-cdr! subtable
                            (cons (cons key value)
                                  (cdr subtable)))))
            (set-cdr! table
                      (cons (list level
                                  (cons key value))
                            (cdr table))))))

    (define (get level key)
      (lookup level key local-table))

    (define (put level key value)
      (insert! level key value local-table))

    (define get-table local-table)
    
    (define (dispatch m)
      (cond ((eq? m 'get-proc) get)
            ((eq? m 'put-proc) put)
            ((eq? m 'get-table-proc) get-table)
            (else (error "Undefined operation..." m))))

    dispatch))

;;; creates a table and defines functions to access said table
(define lookup-table (make-lookup-table))
(define get-from-lookup (lookup-table 'get-proc))
(define put-in-lookup (lookup-table 'put-proc))
(define get-table (lookup-table 'get-table-proc))

;--------------------------------------------MIN COST----------------------------------------------------------------------
;;; entry point for min-cost
(define (min-cost data)
  (if (null? data)
      0
      (cdr (min-cost-recurse 1 '() (car data) (cdr data)))))

;;; recursive min-cost function
(define (min-cost-recurse level left root right)
  (let ((left-lookup  (if (null? left)
                          (cons '() 0)
                          (get-from-lookup (+ level 1) left)))
        (right-lookup (if (null? right)
                          (cons '() 0)
                          (get-from-lookup (+ level 1) right))))
    (let ((left-cost  (if left-lookup
                          (cdr left-lookup)
                          (cdr (min-cost-recurse (+ level 1) '() (car left) (cdr left)))))
          (right-cost (if right-lookup
                          (cdr right-lookup)
                          (cdr (min-cost-recurse (+ level 1) '() (car right) (cdr right))))))
      (let ((this-tree (append left (list root) right))
            (this-node (cons root (+ (* level (cadr root)) left-cost right-cost)))
            (best-alt-node (if (null? right)
                                  (cons '() 1000000000000000000)
                                  (min-cost-recurse level (append left (list root)) (car right) (cdr right)))))
        (if (< (cdr this-node) (cdr best-alt-node))
            (begin
              (put-in-lookup level this-tree this-node)
              this-node)
            (begin
              (put-in-lookup level this-tree best-alt-node)
              best-alt-node))))))

(define data (with-input-from-file "keys-medium.dat" read-file))
;(min-cost-naive 1 data)
;(min-cost 1 data)
;--------------------------------------------BUILD MIN TREE----------------------------------------------------------------------

  

;;;; the following procedure is handy for timing things
(#%require (only racket/base current-milliseconds))
(define (runtime) (current-milliseconds))

(define (timed f . args)
  (let ((init (runtime)))
    (let ((v (apply f args)))
      (display (list 'time: (- (runtime) init)))
      (newline)
      v)))

;(timed min-cost-naive 1 data)
;(timed min-cost 1 data)