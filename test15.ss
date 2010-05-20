#!r6rs

(import (rnrs)
	(QobiScheme)
	(nondeterministic-scheme)
	(generative-montague-grammar))

(define *state1* (things '(empty empty empty empty x empty empty empty empty)))

(define *state2* (things '(empty empty empty x empty empty empty empty empty)))

(define *state3*
 (things '(empty empty empty empty empty empty empty empty empty)))

(define *state4* (things '(empty empty empty empty x x empty empty empty)))

(define (test1)
 (domain (a-bottom-up-parse (parse-type 'boolean) '(the x is-on the center))))

(define (test2)
 (domain (a-top-down-parse (parse-type 'boolean) '(the x is-on the center))))

(define (test3) (possibly-true? '(the x is-on the center) *state1*))

(define (test4) (possibly-true? '(the x is-on the center) *state2*))

(define (test5) (possibly-true? '(the x is-on the center) *state3*))

(define (test6) (possibly-true? '(the x is-on the center) *state4*))

(define (test7) (domain (a-phrase-of-type 'boolean)))

(define (test8) (domain (a-phrase-of-value #t 'boolean *state1*)))

(define (test9) (domain (a-phrase-of-value #t 'boolean *state2*)))

(define (test10) (domain (a-phrase-of-value #t 'boolean *state3*)))

(define (test11) (domain (a-phrase-of-value #t 'boolean *state4*)))

(define (test12) (domain (a-phrase-of-value #f 'boolean *state1*)))

(define (test13) (domain (a-phrase-of-value #f 'boolean *state2*)))

(define (test14) (domain (a-phrase-of-value #f 'boolean *state3*)))

(define (test15) (domain (a-phrase-of-value #f 'boolean *state4*)))
