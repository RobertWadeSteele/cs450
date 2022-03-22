;;;; RSA.SCM

;;;; fast modular exponentiation. From the textbook, section 1.2.4

(define (expmod b e m)
  (cond ((zero? e) 1)
        ((even? e)
         (remainder (square (expmod b (/ e 2) m))
                    m))
        (else
         (remainder (* b (expmod b (- e 1) m))
                    m))))

(define (square x) (* x x))

;;; Prints to console (w/ newline)

;(define (print s)
;  (display s)
;  (newline))
          
;;; An RSA key consists of a modulus and an exponent.

(define make-key cons)
(define key-modulus car)
(define key-exponent cdr)

(define (RSA-transform number key)
  (expmod number (key-exponent key) (key-modulus key)))

;;; The following routine compresses a list of numbers to a single
;;; number for use in creating digital signatures.

(define (compress intlist)
  (define (add-loop l)
    (if (null? l)
        0
        (+ (car l) (add-loop (cdr l)))))
  (modulo (add-loop intlist) (expt 2 28)))

;;;; generating RSA keys

;;; To choose a prime, we start searching at a random odd number in a
;;; specifed range

(#%require (only racket/base random))
(define (choose-prime smallest range)
  (let ((start (+ smallest (choose-random range))))
    (search-for-prime (if (even? start) (+ start 1) start))))

(define (search-for-prime guess)
  (if (fast-prime? guess 2)
      guess
      (search-for-prime (+ guess 2))))

;;; The following procedure picks a random number in a given range,
;;; but makes sure that the specified range is not too big for
;;; Scheme's RANDOM primitive.

(define choose-random
  ;; restriction of Scheme RANDOM primitive
  (let ((max-random-number (expt 10 18))) 
    (lambda (n)
      (random (inexact->exact(floor (min n max-random-number)))))))


;;; The Fermat test for primality, from the texbook section 1.2.6

(define (fermat-test n)
    (let ((a (choose-random n)))
      (= (expmod a n n) a)))

(define (fast-prime? n times)
    (cond ((zero? times) #t)
          ((fermat-test n) (fast-prime? n (- times 1)))
          (else #f)))
;;; RSA key pairs are pairs of keys

(define make-key-pair cons)
(define key-pair-public car)
(define key-pair-private cdr)

;;; generate an RSA key pair (k1, k2).  This has the property that
;;; transforming by k1 and transforming by k2 are inverse operations.
;;; Thus, we can use one key as the public key andone as the private key.
(define (generate-RSA-key-pair)
  (let ((size (expt 2 14)))
    ;; we choose p and q in the range from 2^14 to 2^15.  This insures
    ;; that the pq will be in the range 2^28 to 2^30, which is large
    ;; enough to encode four characters per number.
    (let ((p (choose-prime size size))
          (q (choose-prime size size)))
    (if (= p q)       ;check that we haven't chosen the same prime twice
        (generate-RSA-key-pair)     ;(VERY unlikely)
        (let ((n (* p q))
              (m (* (- p 1) (- q 1))))
          (let ((e (select-exponent m)))
            (let ((d (invert-modulo e m)))
              (make-key-pair (make-key n e) (make-key n d)))))))))


;;; The RSA exponent can be any random number relatively prime to m

(define (select-exponent m)
  (let ((try (choose-random m)))
    (if (= (gcd try m) 1)
        try
        (select-exponent m))))


;;; Invert e modulo m

(define (invert-modulo e m)
  (if (= (gcd e m) 1)
      (let ((y (cdr (solve-ax+by=1 m e))))
        (modulo y m))                   ;just in case y was negative
      (error "gcd not 1" e m)))


;;; solve ax+by=1
;;; The idea is to let a=bq+r and solve bx+ry=1 recursively

(define (solve-ax+by=1 a b) (recurse-ax+by=1 a b (cons 1 0) (cons 0 1)))

(define (recurse-ax+by=1 a b x y)
  (let ((rem (remainder a b))
        (quo (quotient a b)))
    (if (= rem 0)
        (cons (cdr x) (cdr y))
        (let ((x_temp (- (car x) (* quo (cdr x))))
              (y_temp (- (car y) (* quo (cdr y)))))
          (recurse-ax+by=1 b rem (cons (cdr x) x_temp) (cons (cdr y) y_temp))))))

;;; Actual RSA encryption and decryption

(define (RSA-encrypt string key1)
  (RSA-convert-list (string->intlist string) key1))

(define (RSA-convert-list intlist key)
  (let ((n (key-modulus key)))
    (define (convert l sum)
      (if (null? l)
          '()
          (let ((x (RSA-transform (modulo (- (car l) sum) n) key)))
            (cons x (convert (cdr l) x)))))
    (convert intlist 0)))


(define (RSA-decrypt intlist key2)
  (intlist->string (RSA-unconvert-list intlist key2)))

(define (RSA-unconvert-list intlist key)
  (let ((n (key-modulus key)))
    (define (convert l sum)
      (if (null? l)
          '()
          (cons (modulo (+ (RSA-transform (car l) key) sum) n) (convert (cdr l) (car l)))))
    (convert intlist 0)))

  
;;;; searching for divisors.

;;; The following procedure is very much like the find-divisor
;;; procedure of section 1.2.6 of the test, except that it increments
;;; the test divisor by 2 each time (compare exercise 1.18 of the
;;; text).  You should be careful to call it only with odd numbers n.

(define (smallest-divisor n)
  (find-divisor n 3))

(define (find-divisor n test-divisor)
  (cond ((> (square test-divisor) n) n)
        ((divides? test-divisor n) test-divisor)
        (else (find-divisor n (+ test-divisor 2)))))

(define (divides? a b)
  (= (remainder b a) 0))

(define (crack-RSA public-key)
  (let ((n (key-modulus public-key))
        (e (key-exponent public-key)))
    (let ((p (smallest-divisor n)))
      (let ((q (/ n p)))
        (let ((m (* (- p 1) (- q 1))))
          (let ((d (invert-modulo e m)))
            (make-key n d)))))))

;;;; converting between strings and numbers

;;; The following procedures are used to convert between strings, and
;;; lists of integers in the range 0 through 2^28.  You are not
;;; responsible for studying this code -- just use it.

;;; Convert a string into a list of integers, where each integer
;;; encodes a block of characters.  Pad the string with spaces if the
;;; length of the string is not a multiple of the blocksize.

(define (string->intlist string)
  (let ((blocksize 4))
    (let ((padded-string (pad-string string blocksize)))
      (let ((length (string-length padded-string)))
        (block-convert padded-string 0 length blocksize)))))

(define (block-convert string start-index end-index blocksize)
  (if (= start-index end-index)
      '()
      (let ((block-end (+ start-index blocksize)))
        (cons (charlist->integer
	       (string->list (substring string start-index block-end)))
              (block-convert string block-end end-index blocksize)))))

(define (pad-string string blocksize)
  (let ((rem (remainder (string-length string) blocksize)))
    (if (= rem 0)
        string
        (string-append string (make-string (- blocksize rem) #\Space)))))

;;; Encode a list of characters as a single number
;;; Each character gets converted to an ascii code between 0 and 127.
;;; Then the resulting number is c[0]+c[1]*128+c[2]*128^2,...
(define (charlist->integer charlist)
  (let ((n (char->integer (car charlist))))
    (if (null? (cdr charlist))
        n
        (+ n (* 128 (charlist->integer (cdr charlist)))))))

;;; Convert a list of integers to a string. (Inverse of
;;; string->intlist, except for the padding.)
(define (intlist->string intlist)
  (list->string
   (apply
    append
    (map integer->charlist intlist))))

;;; Decode an integer into a list of characters.  (This is essentially
;;; writing the integer in base 128, and converting each "digit" to a
;;; character.)
(define (integer->charlist integer)
  (if (< integer 128)
      (list (integer->char integer))
      (cons (integer->char (remainder integer 128))
            (integer->charlist (quotient integer 128)))))

;;;; the following procedure is handy for timing things
(#%require (only racket/base current-milliseconds))
(define (runtime) (current-milliseconds))

(define (timed f . args)
  (let ((init (runtime)))
    (let ((v (apply f args)))
      (display (list 'time: (- (runtime) init)))
      (newline)
      v)))

;;;; Some initial test data
(define test-key-pair1
  (make-key-pair
   (make-key 816898139 180798509)
   (make-key 816898139 301956869)))

(define test-key-pair2
  (make-key-pair
   (make-key 513756253 416427023)
   (make-key 513756253 462557987)))

;; Implemnent digital signature here
(define (signed-message message signature) (cons message signature))

(define (encrypt-and-sign message private-key public-key)
  (let ((m (RSA-encrypt message public-key)))
    (signed-message m (RSA-transform (compress m) private-key))))

(define (authenticate-and-decrypt signed-message public-key private-key)
  (let ((message (car signed-message))
        (signature (cdr signed-message)))
    (if (= (compress message) (RSA-transform signature public-key))
        (RSA-decrypt message private-key)
        #f)))

;;;public keys for political figures

(define donald-trump-public-key (make-key 833653283 583595407))
(define mike-pence-public-key (make-key 655587853 463279441))
(define nancy-pelosi-public-key (make-key 507803083 445001911))
(define aoc-public-key (make-key 865784123 362279729))
(define michael-cohen-public-key (make-key 725123713 150990017))
(define ivanka-trump-public-key (make-key 376496027 270523157))
(define bernie-sanders-public-key (make-key 780450379 512015071))
(define kamala-harris-public-key (make-key 412581307 251545759))
(define joe-biden-public-key (make-key 718616329 290820109))
(define joe-biden-private-key (make-key 718616329 129033029))

;;;message received by Joe Biden -- Who sent it?
(define received-mystery-message
  '(521793772 221028613 52459926 511097780 523838672 443241014 511806122 640398158 370564768 315158823 38083336 483957005 194461903 678652729))

(define received-mystery-signature 205550182)

;;; test keys
(define test-public-key1 (key-pair-public test-key-pair1))
(define test-private-key1 (key-pair-private test-key-pair1))
(define test-public-key2 (key-pair-public test-key-pair2))
(define test-private-key2 (key-pair-private test-key-pair2))

;;; encrypted secret message
(define result1 (RSA-encrypt "This is a test message." test-public-key1))

(RSA-unconvert-list result1 test-private-key1)

;;; decrypt secret message
(RSA-decrypt result1 test-private-key1)

;;; encrypted secret message with signature
(define result2
  (encrypt-and-sign "Test message from user 1 to user 2"
                    test-private-key1
                    test-public-key2))

result2

;;; attempt to authenticate and decrypt with correct public key
(authenticate-and-decrypt result2 test-public-key1 test-private-key2)
;;; attempt to authenticate and decrypt with incorrect public key
(authenticate-and-decrypt result2 test-public-key2 test-private-key2)

;;; crack public key1
;(print "Cracking test-public-key1")
(define test-cracked-key1 (crack-RSA test-public-key1))
;(print "Succesful?")
test-cracked-key1
test-private-key1

;;; crack public key2
;(print "Cracking test-public-key2")
(define test-cracked-key2 (crack-RSA test-public-key2))
;(print "Succesful?")
test-cracked-key2
test-private-key2

;;; crack donald trump and mike pence public keys for future use
(define donald-trump-private-key (crack-RSA donald-trump-public-key))
(define mike-pence-private-key (crack-RSA mike-pence-public-key))

;;; define fake message to rig 2020 election
(define fake-message "Announce that we're increasing taxes by 100%! Biggest increase ever! TREMENDOUS increase!")

;;; wrapper to send a message from trump to pence
(define trump2pence (encrypt-and-sign fake-message donald-trump-private-key mike-pence-public-key))

;;; decrypt fake message using trump's public key and mik pence's private key
(define decrypted-message (authenticate-and-decrypt trump2pence donald-trump-public-key mike-pence-private-key))

;;; check if we succesfully rigged an election
;(print "Successfully sent and recieved incriminating message?")
decrypted-message
fake-message

;;; WRITTEN SECTION

;;; (1)
(solve-ax+by=1 233987973 41111687)

;;; (2)
;;; ((623764469 . 575076109) 623764469 . 120825157)
(generate-RSA-key-pair)
;;; ((776512123 . 233162125) 776512123 . 637040805)
(generate-RSA-key-pair)

;;; (3)
;;; list of politicians public keys
(define politicians (list donald-trump-public-key
                          mike-pence-public-key
                          nancy-pelosi-public-key
                          aoc-public-key
                          michael-cohen-public-key
                          ivanka-trump-public-key
                          bernie-sanders-public-key
                          kamala-harris-public-key
                          joe-biden-public-key))

;;; if false then message could not be authenticated from list
(define (who-sent? message list private-key)
  (if (null? list)
      #f
      (let ((m (authenticate-and-decrypt message (car list) private-key)))
        (if (equal? m #f)
            (who-sent? message (cdr list) private-key)
            (car list)))))

(define mess (signed-message received-mystery-message received-mystery-signature))
(define politician (who-sent? mess politicians joe-biden-private-key))
(authenticate-and-decrypt mess politician joe-biden-private-key)
politician

;;; (4)
(define forged-message1 "I am a TREMENDOUS fan.")
(define forged-message2 "You have small hands.")
(define forged-message3 "This is a message from future you... watch out for ice cubes.")

(define nancy-pelosi-private-key (crack-RSA nancy-pelosi-public-key))
(define bernie-sanders-private-key (crack-RSA bernie-sanders-public-key))

(define message-to-bernie (encrypt-and-sign forged-message1 donald-trump-private-key bernie-sanders-public-key))
(define message-to-trump (encrypt-and-sign forged-message2 nancy-pelosi-private-key donald-trump-public-key))
(define message-to-biden (encrypt-and-sign forged-message3 joe-biden-private-key joe-biden-public-key))

(authenticate-and-decrypt message-to-bernie donald-trump-public-key bernie-sanders-private-key)
(authenticate-and-decrypt message-to-trump nancy-pelosi-public-key donald-trump-private-key)
(authenticate-and-decrypt message-to-biden joe-biden-public-key joe-biden-private-key)

;;; (5)
(define sample1 (generate-RSA-key-pair))
(define sample2 (generate-RSA-key-pair))
(define sample3 (generate-RSA-key-pair))

;(timed crack-RSA (car sample1))
;(timed crack-RSA (car sample2))
;(timed crack-RSA (car sample3))