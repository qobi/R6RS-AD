#!r6rs

(import (rnrs)
	(QobiScheme)
	(nondeterministic-scheme)
	(games7a))

(define (test1)
 (for-each (lambda (words)
	    (write words)
	    (newline)
	    (write (length (domain (a-top-down-parse (parse-type *s*) words))))
	    (newline)
	    (newline))
	   (append *tic-tac-toe* *hexapawn*)))

(define *tic-tac-toe-initital-state*
 (make-state
  '#(#(#f #f #f) #(#f #f #f) #(#f #f #f)) '#(x x x x x) '#(o o o o o) 'x))

(define *hexapawn-initital-state*
 (make-state
  '#(#(x x x) #(#f #f #f) #(o o o)) '#(#f #f #f #f #f) '#(#f #f #f #f #f) 'x))

(define *state*
 (make-state '#(#(x x x) #(x x x) #(x x o)) '#(x x x x x) '#(o o o o o) 'x))

(define (test2)
 (possibly-true? (first *tic-tac-toe*) (things) *tic-tac-toe-initital-state*))

;;; erroneously yields #t
(define (test3)
 (possibly-true? (first *tic-tac-toe*) (things) *hexapawn-initital-state*))

(define (test4)
 (possibly-true? (first *hexapawn*) (things) *tic-tac-toe-initital-state*))

;;; erroneously yields #f
(define (test5)
 (possibly-true? (first *hexapawn*) (things) *hexapawn-initital-state*))

(define (test6)
 (possibly-true? '(some cache square has some piece)
		 (things)
		 *tic-tac-toe-initital-state*))

(define (test7)
 (let ((some
	(evaluate
	 (parse-expression
	  '(rlambda (noun1) (lambda (noun2) (some noun1 noun2)))
	  (parse-type *d*))
	 '()
	 (things)
	 *tic-tac-toe-initital-state*))
       (cache
	(evaluate
	 (parse-expression
	  '(rlambda (noun)
		    (lambda (thing1)
		     (and (noun thing1 (-> thing boolean))
			  (some
			   (lambda (thing2) (player? thing2))
			   (lambda (thing2)
			    (some
			     (lambda (thing3) (cache? thing3 thing2))
			     (lambda (thing3) (square? thing1 thing3))))))))
	  (parse-type *a*))
	 '()
	 (things)
	 *tic-tac-toe-initital-state*))
       (square
	(evaluate
	 (parse-expression
	  '(lambda (thing1)
	    (some (lambda (thing2)
		   (or (row? thing2)
		       (column? thing2)
		       (diagonal? thing2)
		       (some (lambda (thing3) (player? thing3))
			     (lambda (thing3) (cache? thing2 thing3)))))
		  (lambda (thing2) (square? thing1 thing2))))
	  (parse-type *n*))
	 '()
	 (things)
	 *tic-tac-toe-initital-state*))
       (has
	(evaluate
	 (parse-expression
	  '(rlambda (np2)
		    (llambda (np1)
			     (np2 (lambda (thing2)
				   (np1 (lambda (thing1) (has? thing1 thing2))
					(-> (-> thing boolean) boolean)))
				  (-> (-> thing boolean) boolean))))
	  (parse-type *v-np*))
	 '()
	 (things)
	 *tic-tac-toe-initital-state*))
       (piece
	(evaluate
	 (parse-expression
	  '(lambda (thing1)
	    (some (lambda (thing2) (player? thing2))
		  (lambda (thing2) (piece? thing1 thing2))))
	  (parse-type *n*))
	 '()
	 (things)
	 *tic-tac-toe-initital-state*)))
  (call (call has
	      (call some piece (things) *tic-tac-toe-initital-state*)
	      (things)
	      *tic-tac-toe-initital-state*)
	(call some
	      (call cache square (things) *tic-tac-toe-initital-state*)
	      (things)
	      *tic-tac-toe-initital-state*)
	(things)
	*tic-tac-toe-initital-state*)))

(define (test8)
 (possibly-true? '(every square has some piece) (things) *state*))

(define (test9)
 (domain
  (begin (write (a-phrase-of-value #t (parse-type *s*) (things) *state* 1))
	 (newline)
	 (fail))))

(define (test10)
 (domain (begin (let ((words (a-phrase-of-type (parse-type *s*) 5)))
		 (unless (possibly-true? words (things) *state*) (fail))
		 (write words)
		 (newline))
		(fail))))
