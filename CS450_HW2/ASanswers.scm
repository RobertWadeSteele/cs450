;Problem 1

(define (is-list? x)
  (cond ((null? x) #t)
        ((not(pair? x)) #f)
        (else (is-list? (cdr x)))))

;Problem 2

(define (my-reverse x)
  (if (null? x)
      '()
      (append (my-reverse (cdr x)) (list (car x)))))

;Problem 3

(define (same-parity f . l) (cons f (same-parity-recurse f l)))

(define (same-parity-recurse f l)
  (if (null? l)
      '()
      (if (equal? (even? f) (even? (car l)))
          (cons (car l) (same-parity-recurse f (cdr l)))
          (same-parity-recurse f (cdr l)))))

;Problem 4

;(define (square-list items)
;  (if (null? items)
;      '()
;      (cons (expt (car items) 2) (square-list-1 (cdr items)))))

(define (square-list-3 items)
  (map (lambda (x) (expt x 2)) items))

;Problem 5

(define (my-for-each p l)
  (if (not(null? l))
      (p (car l)))
  (if (not(null? l))
      (my-for-each p (cdr l))))

;Problem 7

(define (my-equal? elem1 elem2)
            (if (and (is-list? elem1) (is-list? elem2))
                (if (or (null? elem1) (null? elem2))
                    (if (and (null? elem1) (null? elem2)) #t #f)
                    (if (my-equal? (car elem1) (car elem2)) (my-equal? (cdr elem1) (cdr elem2)) #f))
                (if (eqv? elem1 elem2) #t #f)))

;Question 8 Part A

(define (every? pred seq)
  (if (null? seq)
      #t
      (if (pred (car seq))
          (every? pred (cdr seq))
          #f)))

#|
Question 8 Part B
If the empty list is evaluated by every? it must return true. If two lists A and B both return #t
when given to every? then concatenating lists A and B to create list C will also return #t. By this
same reasoning we can say that any subset of a list that returns #t should also return #t. Because
the empty list is a subset of every list we can say that the empty list should evaluate to #t.
|#

;Problem 9

(define (element-of-set? x set)
  (cond ((null? set) #f)
        ((equal? x (car set)) #t)
        (else (element-of-set? x (cdr set)))))

(define (unordered-union-set set1 set2)
  (cond ((and (null? set1) (null? set2)) '())
        ((null? set1) (if (element-of-set? (car set2) (cdr set2))
                          (unordered-union-set set1 (cdr set2))
                          (cons (car set2) (unordered-union-set set1 (cdr set2)))))
        (else (if (or (element-of-set? (car set1) (cdr set1)) (element-of-set? (car set1) set2))
                  (unordered-union-set (cdr set1) set2)
                  (cons (car set1) (unordered-union-set (cdr set1) set2))))))

;Problem 10

(define (element-of-ordered-set? x set)
  (cond ((null? set) #f)
        ((equal? x (car set)) #t)
        (else (if (> (car set) x)
                  #f
                  (element-of-set? x (cdr set))))))

(define (ordered-union-set set1 set2)
        ; base case return null set
  (cond ((and (null? set1) (null? set2)) '())
        ; set1 is null so just check if (car set2) appears later in set2
        ((null? set1) (if (element-of-ordered-set? (car set2) (cdr set2))
                          ; if it does, ignore it for now
                          (ordered-union-set set1 (cdr set2))
                          ; if not, add it to the set
                          (cons (car set2) (ordered-union-set set1 (cdr set2)))))
        ; set2 is null so just check if (car set1) appears later in set1
        ((null? set2) (if (element-of-ordered-set? (car set1) (cdr set1))
                          ; if it does, ignore it for now
                          (ordered-union-set (cdr set1) set2)
                          ; if not, add it to the set
                          (cons (car set1) (ordered-union-set (cdr set1) set2))))
        ; both pairs are not null so compare current pair values to determine which pair to evaluate
        (else (if (< (car set1) (car set2))
                  ; (car set1) is smallest so evaluate first, check if (car set1) appears again in set1
                  (if (element-of-ordered-set? (car set1) (cdr set1))
                      ; if it does, ignore it for now
                      (ordered-union-set (cdr set1) set2)
                      ; if not, add it to the set
                      (cons (car set1) (ordered-union-set (cdr set1) set2)))
                  ; (car set2 is smallest or equal to (car set1), check if (car set2) appears in set1 or later in set2
                  (if (or (element-of-ordered-set? (car set2) (cdr set2)) (element-of-ordered-set? (car set2) set1))
                      ; if it does, ignore it for now
                      (ordered-union-set set1 (cdr set2))
                      ; if not, add it to the set
                      (cons (car set2) (ordered-union-set set1 (cdr set2))))))))

; Problem 11

(define (remove-val x s)
  (cond ((null? s) '())
        ((= x (car s)) (remove-val x (cdr s)))
        (else (cons (car s) (remove-val x (cdr s))))))