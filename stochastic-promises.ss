#!r6rs

(library
 (stochastic-promises)
 (export delayed-draw force-stochastic-promise)
 (import (rnrs) (stochastic-scheme))

 (define-record-type stochastic-promise
  (fields distribution (mutable value?) (mutable value)))

 (define (delayed-draw d) (make-stochastic-promise d #f #f))

 (define (force-stochastic-promise promise)
  (cond ((not (stochastic-promise? promise)) promise)
	((stochastic-promise-value? promise)
	 (stochastic-promise-value promise))
	(else (upon-bottom (stochastic-promise-value?-set! promise #f))
	      (stochastic-promise-value?-set! promise #t)
	      (let ((value (draw (stochastic-promise-distribution promise))))
	       (stochastic-promise-value-set! promise value)
	       value)))))
