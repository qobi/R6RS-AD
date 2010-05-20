#!r6rs

(library
 (deterministic-memoization)
 (export memoize)
 (import (rnrs))

 (define (memoize f)
  (let ((cache '()))
   (lambda arguments
    (let ((entry (assoc arguments cache)))
     (if entry
	 (cdr entry)
	 (let ((result (apply f arguments)))
	  (set! cache (cons (cons arguments result) cache))
	  result)))))))
