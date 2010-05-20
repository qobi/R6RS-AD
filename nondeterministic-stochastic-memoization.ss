#!r6rs

(library
 (nondeterministic-stochastic-memoization)
 (export memoize-nondeterministic-stochastic
	 memoize-nondeterministic-removing-duplicates-stochastic
	 memoize-nondeterministic-stochastic-coalescing-duplicates
	 memoize-nondeterministic-removing-duplicates-stochastic-coalescing-duplicates
	 memoize-stochastic-nondeterministic
	 memoize-stochastic-coalescing-duplicates-nondeterministic
	 memoize-stochastic-nondeterministic-removing-duplicates
	 memoize-stochastic-coalescing-duplicates-nondeterministic-removing-duplicates)
 (import (rnrs)
	 (nondeterministic-scheme)
	 (stochastic-scheme)
	 (deterministic-memoization))

 (define (memoize-nondeterministic-stochastic f)
  (let ((f (memoize
	    (lambda arguments (distribution (domain (apply f arguments)))))))
   (lambda arguments (a-member-of (draw (apply f arguments))))))

 (define (memoize-nondeterministic-removing-duplicates-stochastic f)
  (let ((f (memoize
	    (lambda arguments
	     (distribution (remove-duplicates (domain (apply f arguments))))))))
   (lambda arguments (a-member-of (draw (apply f arguments))))))

 (define (memoize-nondeterministic-stochastic-coalescing-duplicates f)
  (let ((f (memoize
	    (lambda arguments
	     (coalesce-duplicates
	      (distribution (domain (apply f arguments))))))))
   (lambda arguments (a-member-of (draw (apply f arguments))))))

 (define (memoize-nondeterministic-removing-duplicates-stochastic-coalescing-duplicates f)
  (let ((f (memoize
	    (lambda arguments
	     (coalesce-duplicates
	      (distribution
	       (remove-duplicates (domain (apply f arguments)))))))))
   (lambda arguments (a-member-of (draw (apply f arguments))))))

 (define (memoize-stochastic-nondeterministic f)
  (let ((f (memoize
	    (lambda arguments (domain (distribution (apply f arguments)))))))
   (lambda arguments (draw (a-member-of (apply f arguments))))))

 (define (memoize-stochastic-coalescing-duplicates-nondeterministic f)
  (let ((f (memoize
	    (lambda arguments
	     (domain
	      (coalesce-duplicates (distribution (apply f arguments))))))))
   (lambda arguments (draw (a-member-of (apply f arguments))))))

 (define (memoize-stochastic-nondeterministic-removing-duplicates f)
  (let ((f (memoize
	    (lambda arguments
	     (remove-duplicates (domain (distribution (apply f arguments))))))))
   (lambda arguments (draw (a-member-of (apply f arguments))))))

 (define (memoize-stochastic-coalescing-duplicates-nondeterministic-removing-duplicates f)
  (let ((f (memoize
	    (lambda arguments
	     (remove-duplicates
	      (domain
	       (coalesce-duplicates (distribution (apply f arguments)))))))))
   (lambda arguments (draw (a-member-of (apply f arguments)))))))
