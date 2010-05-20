#!r6rs

(library
 (nondeterministic-memoization)
 (export memoize-nondeterministic memoize-nondeterministic-removing-duplicates)
 (import (rnrs) (nondeterministic-scheme) (deterministic-memoization))

 (define (memoize-nondeterministic f)
  (let ((f (memoize (lambda arguments (domain (apply f arguments))))))
   (lambda arguments (a-member-of (apply f arguments)))))

 (define (memoize-nondeterministic-removing-duplicates f)
  (let ((f (memoize (lambda arguments
		     (remove-duplicates (domain (apply f arguments)))))))
   (lambda arguments (a-member-of (apply f arguments))))))
