#!r6rs

(import (rnrs)
	(QobiScheme)
	(nondeterministic-scheme)
	(nondeterministic-constraints)
	(constraint-categorical-grammar))

(define (test n)
 (set-nondeterministic-strategy! 'ac)
 (all-sentences n))
