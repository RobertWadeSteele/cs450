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

(define (mult-stream mult stream)
  ('()))

;;;Converts a number to a list representation of that number
(define (number->list-of-digits num)
  (let ((list (string->list (number->string num))))

    (define (list->list-of-digits list)
      (if (null? list)
          '()
          (cons (- (char->integer (car list)) 48) (list->list-of-digits (cdr list)))))
      
    (list->list-of-digits list)))

;;;Returns a power of 10 with the same number of digits as elements in a-list
(define (pow a-list)
  (define (pow-r a-list num)
    (if (null? a-list)
        num
        (pow-r (cdr a-list) (* 10 num))))
  
  (pow-r (cdr a-list) 1))

;convert a list to a stream
(define (list->stream list)
  (if (null? list)
      the-empty-stream
      (cons-stream (car list) (list->stream (cdr list)))))

;return a multiplication stream that multiplies a stream 'stream' by multiplier 'm'
(define (mult-stream m stream)
  (if (list? stream)
      (action m (list->stream stream) '() 0)
      (action m stream '() 0)))

;decide what to do next (produce if a-list is not null and left most digit is fixed, consume otherwise)
(define (action m stream a-list a)
  (if (stream-null? stream)
      (list->stream a-list)
      (if (and (not (null? a-list))
               (< (+ m (modulo a (pow a-list))) (pow a-list)))
          (produce m stream a-list a)
          (consume m stream a-list a))))

;remove the next element from a-list and place it in the return stream
(define (produce m stream a-list a)
  (cons-stream (car a-list) (action m stream (cdr a-list) (modulo a (pow a-list)))))

;remove the next element from stream and update a and a-list
;(prepend zeros to new-a-list to make it longer than original a-list if necessary)
(define (consume m stream a-list a)
  (let ((new-a (+ (* 10 a) (* m (stream-car stream)))))
    (let ((new-a-list (number->list-of-digits new-a)))
      ;(if (< (length a-list) (length new-a-list))
          (action m (stream-cdr stream) new-a-list new-a))))
          ;(action m (stream-cdr stream) (append (list-of-zeros (+ (- (length a-list) (length new-a-list)) 1)) new-a-list) new-a)))))

;return a list containing num zeros
(define (list-of-zeros num)
  (if (= num 0)
      '()
      (cons 0 (list-of-zeros (- num 1)))))