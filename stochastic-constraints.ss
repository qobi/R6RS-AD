#!r6rs

(library
 (stochastic-constraints)
 (export set-stochastic-strategy! create-distribution-variable
	 distribution-variable-distribution stochastic-solution
	 assert-stochastic-constraint!)
 (import (rnrs) (QobiScheme) (stochastic-scheme))

 (define *strategy* #f)

 (define-record-type distribution-variable
  (fields (mutable distribution) (mutable demons)))

 (define (set-stochastic-strategy! strategy) (set! *strategy* strategy))

 (define (distribution-variable-distribution-local-set!
	  distribution-variable distribution)
  (let ((distribution
	 (distribution-variable-distribution distribution-variable)))
   (upon-bottom (distribution-variable-distribution-set!
		 distribution-variable distribution)))
  (distribution-variable-distribution-set! distribution-variable distribution))

 (define (distribution-variable-demons-local-set! distribution-variable demons)
  (let ((demons (distribution-variable-demons distribution-variable)))
   (upon-bottom
    (distribution-variable-demons-set! distribution-variable demons)))
  (distribution-variable-demons-set! distribution-variable demons))

 (define (create-distribution-variable distribution)
  (let ((distribution (coalesce-duplicates distribution)))
   (when (null? distribution) (bottom))
   (make-distribution-variable distribution '())))

 (define (restrict-distribution! d distribution)
  (when (null? distribution) (bottom))
  (when (< (length distribution)
	   (length (distribution-variable-distribution d)))
   (distribution-variable-distribution-local-set! d distribution)
   (for-each (lambda (demon) (demon)) (distribution-variable-demons d))))

 (define (bound? d) (null? (rest (distribution-variable-distribution d))))

 (define (binding d) (car (first (distribution-variable-distribution d))))

 (define (stochastic-solution ds)
  (let loop ((ds ds) (xs '()))
   (if (null? ds)
       (reverse xs)
       (let ((pair
	      (draw-pair (distribution-variable-distribution (first ds)))))
	(restrict-distribution! (first ds) (list pair))
	(loop (rest ds) (cons (first pair) xs))))))

 (define (some-element predicate d)
  (some (lambda (pair) (predicate (car pair)))
	(distribution-variable-distribution d)))

 (define (one-element predicate d)
  (one (lambda (pair) (predicate (car pair)))
       (distribution-variable-distribution d)))

 (define (the-element predicate d)
  (list (find-if (lambda (pair) (predicate (car pair)))
		 (distribution-variable-distribution d))))

 (define (the-elements predicate d)
  (remove-if-not (lambda (pair) (predicate (car pair)))
		 (distribution-variable-distribution d)))

 (define (attach-demon! demon d)
  (distribution-variable-demons-local-set!
   d (cons demon (distribution-variable-demons d)))
  (demon))

 (define (assert-constraint-efd! constraint ds)
  (for-each
   (lambda (d)
    (attach-demon! (lambda ()
		    (when (every bound? ds)
		     (unless (apply constraint (map binding ds)) (bottom))))
		   d))
   ds))

 (define (assert-constraint-fc! constraint ds)
  (for-each
   (lambda (d)
    (attach-demon!
     (lambda ()
      (when (one (lambda (d) (not (bound? d))) ds)
       (let* ((i (position-if (lambda (d) (not (bound? d))) ds))
	      (d (list-ref ds i)))
	(unless (some-element
		 (lambda (x)
		  (apply
		   constraint
		   (map-indexed (lambda (d j) (if (= j i) x (binding d))) ds)))
		 d)
	 (bottom)))))
     d))
   ds))

 (define (assert-constraint-vp! constraint ds)
  (for-each
   (lambda (d)
    (attach-demon!
     (lambda ()
      (when (one (lambda (d) (not (bound? d))) ds)
       (let* ((i (position-if (lambda (d) (not (bound? d))) ds))
	      (d (list-ref ds i)))
	(when (one-element
	       (lambda (x)
		(apply
		 constraint
		 (map-indexed (lambda (d j) (if (= j i) x (binding d))) ds)))
	       d)
	 (restrict-distribution!
	  d
	  (the-element
	   (lambda (x)
	    (apply constraint
		   (map-indexed (lambda (d j) (if (= j i) x (binding d))) ds)))
	   d))))))
     d))
   ds))

 (define (assert-constraint-gfc! constraint ds)
  (for-each
   (lambda (d)
    (attach-demon!
     (lambda ()
      (when (one (lambda (d) (not (bound? d))) ds)
       (let* ((i (position-if (lambda (d) (not (bound? d))) ds))
	      (d (list-ref ds i)))
	(restrict-distribution!
	 d
	 (the-elements
	  (lambda (x)
	   (apply constraint
		  (map-indexed (lambda (d j) (if (= j i) x (binding d))) ds)))
	  d)))))
     d))
   ds))

 (define (assert-constraint-ac! constraint ds)
  (for-each
   (lambda (d)
    (attach-demon!
     (lambda ()
      (for-each-indexed
       (lambda (d i)
	(restrict-distribution!
	 d
	 (the-elements
	  (lambda (x)
	   (let loop ((ds ds) (xs '()) (j 0))
	    (if (null? ds)
		(apply constraint (reverse xs))
		(if (= j i)
		    (loop (rest ds) (cons x xs) (+ j 1))
		    (some-element
		     (lambda (pair) (loop (rest ds) (cons (car pair) xs) (+ j 1)))
		     (first ds))))))
	  d)))
       ds))
     d))
   ds))

 (define (assert-stochastic-constraint! constraint . ds)
  (case *strategy*
   ((efd) (assert-constraint-efd! constraint ds))
   ((fc) (assert-constraint-efd! constraint ds)
    (assert-constraint-fc! constraint ds))
   ((vp) (assert-constraint-efd! constraint ds)
    (assert-constraint-fc! constraint ds)
    (assert-constraint-vp! constraint ds))
   ((gfc) (assert-constraint-efd! constraint ds)
    (assert-constraint-gfc! constraint ds))
   ((ac) (assert-constraint-ac! constraint ds))
   (else (error #f "Unrecognized strategy")))))
