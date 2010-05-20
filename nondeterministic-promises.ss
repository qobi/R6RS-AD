#!r6rs

(library
 (nondeterministic-promises)
 (export delayed-a-member-of force-nondeterministic-promise)
 (import (rnrs) (nondeterministic-scheme))

 (define-record-type nondeterministic-promise
  (fields domain (mutable value?) (mutable value)))

 (define (delayed-a-member-of d) (make-nondeterministic-promise d #f #f))

 (define (force-nondeterministic-promise promise)
  (cond
   ((not (nondeterministic-promise? promise)) promise)
   ((nondeterministic-promise-value? promise)
    (nondeterministic-promise-value promise))
   (else (upon-fail (nondeterministic-promise-value?-set! promise #f))
	 (nondeterministic-promise-value?-set! promise #t)
	 (let ((value (a-member-of (nondeterministic-promise-domain promise))))
	  (nondeterministic-promise-value-set! promise value)
	  value)))))
