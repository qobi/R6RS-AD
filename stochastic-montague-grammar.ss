#!r6rs

(library
 (stochastic-montague-grammar)
 (export generate understand)
 (import (rnrs)
	 (QobiScheme)
	 (nondeterministic-scheme)
	 (stochastic-scheme)
	 (deterministic-memoization)
	 (nondeterministic-memoization)
	 (reduced-gradient))

 (define-record-type typed-meaning (fields type meaning))

 (define-record-type position (fields position))

 (define-record-type position-state (fields position state))

 (define-record-type leftward-arrow-type (fields result argument))

 (define-record-type rightward-arrow-type (fields argument result))

 (define (equal-type? type1 type2)
  (or (eq? type1 type2)
      (and (leftward-arrow-type? type1)
	   (leftward-arrow-type? type2)
	   (equal-type? (leftward-arrow-type-argument type1)
			(leftward-arrow-type-argument type2))
	   (equal-type? (leftward-arrow-type-result type1)
			(leftward-arrow-type-result type2)))
      (and (rightward-arrow-type? type1)
	   (rightward-arrow-type? type2)
	   (equal-type? (rightward-arrow-type-argument type1)
			(rightward-arrow-type-argument type2))
	   (equal-type? (rightward-arrow-type-result type1)
			(rightward-arrow-type-result type2)))))

 (define (lexicon game-state)
  (let ((things (append (map-n make-position 9)
			(map-n (lambda (position)
				(make-position-state
				 position (list-ref game-state position)))
			       9))))
   (list
    (cons
     'the
     (make-typed-meaning
      (make-rightward-arrow-type
       (make-rightward-arrow-type 'thing 'bool)
       (make-rightward-arrow-type
	(make-rightward-arrow-type 'thing 'bool) 'bool))
      (lambda (noun1)
       (lambda (noun2)
	;; Montague semantics of "the" is wrong
	(and (one noun1 things) (noun2 (find-if noun1 things)))))))
    (cons
     'x
     (make-typed-meaning
      (make-rightward-arrow-type 'thing 'bool)
      (lambda (thing)
       (and (position-state? thing) (eq? (position-state-state thing) 'x)))))
    (cons
     'is-on
     (make-typed-meaning
      (make-rightward-arrow-type
       (make-rightward-arrow-type
	(make-rightward-arrow-type 'thing 'bool) 'bool)
       (make-leftward-arrow-type
	'bool
	(make-rightward-arrow-type
	 (make-rightward-arrow-type 'thing 'bool) 'bool)))
      (lambda (np2)
       (lambda (np1)
	(np2 (lambda (thing2)
	      (np1 (lambda (thing1)
		    (and (position-state? thing1)
			 (position? thing2)
			 (= (position-state-position thing1)
			    (position-position thing2)))))))))))
    (cons
     'center
     (make-typed-meaning
      (make-rightward-arrow-type 'thing 'bool)
      (lambda (thing)
       (and (position? thing) (= (position-position thing) 4))))))))

 (define (a-typed-apply left right)
  (amb (if (and (rightward-arrow-type? (typed-meaning-type left))
		(equal-type?
		 (typed-meaning-type right)
		 (rightward-arrow-type-argument (typed-meaning-type left))))
	   (make-typed-meaning
	    (rightward-arrow-type-result (typed-meaning-type left))
	    ((typed-meaning-meaning left) (typed-meaning-meaning right)))
	   (fail))
       (if (and (leftward-arrow-type? (typed-meaning-type right))
		(equal-type?
		 (typed-meaning-type left)
		 (leftward-arrow-type-argument (typed-meaning-type right))))
	   (make-typed-meaning
	    (leftward-arrow-type-result (typed-meaning-type right))
	    ((typed-meaning-meaning right) (typed-meaning-meaning left)))
	   (fail))))

 (define (possibly-true? game-state)
  (let ((lexicon (lexicon game-state)))
   (lambda (words)
    (letrec ((an-interpretation
	      (memoize-nondeterministic
	       (lambda (words)
		(if (= (length words) 1)
		    (cdr (assq (first words) lexicon))
		    (let ((i (+ (a-member-of (enumerate (- (length words) 1)))
				1)))
		     (a-typed-apply (an-interpretation
				     (sublist words 0 i))
				    (an-interpretation
				     (sublist words i (length words))))))))))
     (possibly? (domain (let ((typed-meaning (an-interpretation words)))
			 (and (eq? (typed-meaning-type typed-meaning) 'bool)
			      (typed-meaning-meaning typed-meaning)))))))))

 (define (position-state-draw mixture)
  (draw (map cons '(empty x o) (vector->list mixture))))

 (define (word-draw mixture)
  (draw (map cons '(the x is-on center) (vector->list mixture))))

 (define (generate)
  (argmax
   (lambda (mixtures)
    (probability
     (distribution
      ((possibly-true? '(empty empty empty empty x empty empty empty empty))
       (map word-draw (vector->list mixtures))))))
   (map-n-vector (lambda (i) (uniform 4)) 5)))

 (define (understand)
  (argmax
   (lambda (mixtures)
    (probability
     (distribution
      ((possibly-true? (map position-state-draw (vector->list mixtures)))
       '(the x is-on the center)))))
   (map-n-vector (lambda (i) (uniform 3)) 9))))
