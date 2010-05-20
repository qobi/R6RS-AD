#!r6rs

(library
 (stochastic-memoization)
 (export memoize-stochastic memoize-stochastic-coalescing-duplicates)
 (import (rnrs) (stochastic-scheme) (deterministic-memoization))

 (define (memoize-stochastic f)
  (let ((f (memoize (lambda arguments (distribution (apply f arguments))))))
   (lambda arguments (draw (apply f arguments)))))

 (define (memoize-stochastic-coalescing-duplicates f)
  (let ((f (memoize
	    (lambda arguments
	     (coalesce-duplicates (distribution (apply f arguments)))))))
   (lambda arguments (draw (apply f arguments))))))
