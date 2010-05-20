#!r6rs

(library
 (maximizing-nondeterministic-promises)
 (export delayed-a-member-of force-nondeterministic-promise maximal)
 (import (rnrs) (QobiScheme) (nondeterministic-scheme))

 (define-record-type nondeterministic-promise
  (fields domain (mutable value?) (mutable value)))

 (define *promises* '())
 
 (define *maximum-number-of-falses* 0)

 (define *best-number-of-falses* 0)

 (define (delayed-a-member-of d) (make-nondeterministic-promise d #f #f))

 (define (force-nondeterministic-promise promise)
  (cond
   ((not (nondeterministic-promise? promise)) promise)
   ((nondeterministic-promise-value? promise)
    (nondeterministic-promise-value promise))
   (else
    (upon-fail (nondeterministic-promise-value?-set! promise #f))
    (nondeterministic-promise-value?-set! promise #t)
    (let ((value (a-member-of (nondeterministic-promise-domain promise))))
     (when (and (memq promise *promises*) value)
      (let ((maximum-number-of-falses *maximum-number-of-falses*))
       (upon-fail (set! *maximum-number-of-falses* maximum-number-of-falses))
       (set! *maximum-number-of-falses* (- *maximum-number-of-falses* 1)))
      (when (<= *maximum-number-of-falses* *best-number-of-falses*) (fail)))
     (nondeterministic-promise-value-set! promise value)
     value))))

 (define (maximal procedure promises)
  (let ((promises *promises*)) (upon-fail (set! *promises* promises)))
  (set! *promises* promises)
  (let ((maximum-number-of-falses *maximum-number-of-falses*))
   (upon-fail (set! *maximum-number-of-falses* maximum-number-of-falses)))
  (set! *maximum-number-of-falses* (length promises))
  (let ((best-number-of-falses *best-number-of-falses*))
   (upon-fail (set! *best-number-of-falses* best-number-of-falses)))
  (set! *best-number-of-falses* 0)
  (let ((result (procedure promises)))
   (unless (every nondeterministic-promise-value? promises) (fuck-up))
   (let ((number-of-falses
	  (count-if-not nondeterministic-promise-value promises)))
    (unless (= *maximum-number-of-falses* number-of-falses) (fuck-up))
    (when (> number-of-falses *best-number-of-falses*)
     (set! *best-number-of-falses* number-of-falses))
    result))))
