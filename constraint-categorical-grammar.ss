#!r6rs

(library
 (constraint-categorical-grammar)
 (export all-sentences)
 (import (rnrs)
	 (QobiScheme)
	 (nondeterministic-scheme)
	 (nondeterministic-constraints))

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

 (define *lexicon*
  (list (cons 'the
	      (make-rightward-arrow-type
	       (make-rightward-arrow-type 'thing 'boolean)
	       (make-rightward-arrow-type
		(make-rightward-arrow-type 'thing 'boolean) 'boolean)))
	(cons 'x (make-rightward-arrow-type 'thing 'boolean))
	(cons 'is-on
	      (make-rightward-arrow-type
	       (make-rightward-arrow-type
		(make-rightward-arrow-type 'thing 'boolean) 'boolean)
	       (make-leftward-arrow-type
		'boolean
		(make-rightward-arrow-type
		 (make-rightward-arrow-type 'thing 'boolean) 'boolean))))
	(cons 'center (make-rightward-arrow-type 'thing 'boolean))))

 (define (create-word-variable)
  (create-domain-variable (remove-duplicates (map car *lexicon*))))

 (define (create-type-variable)
  (create-domain-variable
   (cons #f
	 (remove-duplicatesp
	  equal-type?
	  (map-reduce append
		      '()
		      (lambda (entry)
		       (let loop ((type (cdr entry)))
			(cons type
			      (cond ((leftward-arrow-type? type)
				     (loop (leftward-arrow-type-result type)))
				    ((rightward-arrow-type? type)
				     (loop (rightward-arrow-type-result type)))
				    (else '())))))
		      *lexicon*)))))

 (define (make-upper-triangular-matrix n initializer)
  (list->vector
   (map-n
    (lambda (i) (list->vector (map-n (lambda (j) (initializer)) (- n i 1))))
    n)))

 (define (upper-triangular-matrix-ref m i j)
  (vector-ref (vector-ref m i) (- j i 1)))

 (define (constraints words)
  (let* ((n (+ (length words) 1))
	 (type (make-upper-triangular-matrix n create-type-variable)))
   (do ((i 0 (+ i 1))) ((= i (- n 1)))
    (assert-nondeterministic-constraint!
     (lambda (type word)
      (some (lambda (entry)
	     (and (eq? (car entry) word) (equal-type? (cdr entry) type)))
	    *lexicon*))
     (upper-triangular-matrix-ref type i (+ i 1))
     (list-ref words i)))
   (do ((i 0 (+ i 1))) ((= i (- n 2)))
    (do ((k (+ i 2) (+ k 1))) ((= k n))
     (apply assert-nondeterministic-constraint!
	    (lambda (type . types)
	     (or (not type)
		 (some (lambda (left right) (and left right))
		       (sublist types 0 (/ (length types) 2))
		       (sublist types (/ (length types) 2) (length types)))))
	    (upper-triangular-matrix-ref type i k)
	    (append
	     (map-n (lambda (j) (upper-triangular-matrix-ref type i (+ i j 1)))
		    (- k i 1))
	     (map-n (lambda (j) (upper-triangular-matrix-ref type (+ i j 1) k))
		    (- k i 1))))))
   (do ((i 0 (+ i 1))) ((= i (- n 2)))
    (do ((j (+ i 1) (+ j 1))) ((= j (- n 1)))
     (do ((k (+ j 1) (+ k 1))) ((= k n))
      (assert-nondeterministic-constraint!
       (lambda (parent left right)
	(or (not parent)
	    (not left)
	    (not right)
	    (and (leftward-arrow-type? right)
		 (equal-type? left (leftward-arrow-type-argument right))
		 (equal-type? parent (leftward-arrow-type-result right)))
	    (and (rightward-arrow-type? left)
		 (equal-type? right (rightward-arrow-type-argument left))
		 (equal-type? parent (rightward-arrow-type-result left)))))
       (upper-triangular-matrix-ref type i k)
       (upper-triangular-matrix-ref type i j)
       (upper-triangular-matrix-ref type j k)))))
   (assert-nondeterministic-constraint!
    (lambda (type) (eq? type 'boolean))
    (upper-triangular-matrix-ref type 0 (- n 1)))
   type))

 (define (all-domain-variables type)
  (map-reduce append '() vector->list (vector->list type)))

 (define (all-sentences n)
  (domain (let* ((words (map-n (lambda (i) (create-word-variable)) n))
		 (type (constraints words)))
	   (nondeterministic-solution
	    (append (all-domain-variables type) words))
	   (map binding words)))))
