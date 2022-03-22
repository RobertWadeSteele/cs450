;;;; LOADS THE EXPLICIT-CONTROL EVALUATOR FROM SECTION 5.4 OF
;;;; STRUCTURE AND INTERPRETATION OF COMPUTER PROGRAMS, WITH
;;;; ALL THE SUPPORTING CODE IT NEEDS IN ORDER TO RUN.

(load "regsim.scm")			;reg machine simulator

;; **NB** next file loads "syntax.scm":
(load "eceval-support.scm")		;simulation of machine operations

(load "eceval.scm")			;eceval itself

; (load "eceval_5.28.scm")

;;;; I added the following 2 lines (C. Offner):

(define the-global-environment (setup-environment))
(start eceval)
