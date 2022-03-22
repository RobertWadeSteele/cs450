;;;------------------------------HW5 Part1---------------------------;;;
(define-syntax cons-stream
  (syntax-rules ()
    ((cons-stream head tail)
     (cons head (delay tail)))))

(define stream-car car)
(define (stream-cdr stream) (force (cdr stream)))
(define stream-null? null?)
(define the-empty-stream '())

(define (stream-foreach f x)
  (if (stream-null? x)
      'done
      (begin (f (stream-car x))
             (stream-foreach f (stream-cdr x)))))

(define (stream-filter pred stream)
  (cond ((stream-null? stream) the-empty-stream)
        ((pred (stream-car stream))
         (cons-stream (stream-car stream)
                      (stream-filter pred (stream-cdr stream))))
        (else (stream-filter pred (stream-cdr stream)))))

(define (add-streams stream1 stream2)
  (cons-stream (+ (stream-car stream1) (stream-car stream2))
               (add-streams (stream-cdr stream1) (stream-cdr stream2))))
;;;-----------------Question 1--------------------------;;;
(define (display-n stream n)
  (cond ((stream-null? stream) the-empty-stream)
        ((<= n 0) the-empty-stream)
        (else (display (stream-car stream))
              (newline)
              (display-n (stream-cdr stream) (- n 1)))))

;;;-----------------Question 2--------------------------;;;
(define (stream-map proc . argstreams)
  (if (stream-null? (car argstreams))
      the-empty-stream
      (begin
        (display (apply proc (map stream-car argstreams)))
        (apply stream-map
               (cons proc (map stream-cdr argstreams))))))

;;;-------------------Question 3-------------------------;;;
(define ones (cons-stream 1 ones))

(define integers (cons-stream 1 (add-streams ones integers)))

(define (stream-notdiv stream nums)
  (if (stream-null? stream) the-empty-stream
      (if (notdiv (stream-car stream) nums)
          (cons-stream (stream-car stream) (stream-notdiv (stream-cdr stream) nums))
          (stream-notdiv (stream-cdr stream) nums))))

(define (notdiv num nums)
  (if (null? nums)
      #t
      (if (= 0 (remainder num (car nums)))
          #f
          (notdiv num (cdr nums)))))

(define notdiv-235 (cons-stream 1 (stream-notdiv (stream-cdr integers) (list 2 3 5))))

;;;--------------------------------------HW5 Part2---------------------------------------;;;
