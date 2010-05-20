#!r6rs

(library
 (nondeterministic-constraints)
 (export set-nondeterministic-strategy! create-domain-variable
	 binding nondeterministic-solution assert-nondeterministic-constraint!)
 (import (rnrs) (QobiScheme) (nondeterministic-scheme))

 (define *strategy* #f)

 (define-record-type domain-variable
  (fields (mutable domain) (mutable demons)))

 (define (set-nondeterministic-strategy! strategy) (set! *strategy* strategy))

 (define (domain-variable-domain-local-set! domain-variable domain)
  (let ((domain (domain-variable-domain domain-variable)))
   (upon-fail (domain-variable-domain-set! domain-variable domain)))
  (domain-variable-domain-set! domain-variable domain))

 (define (domain-variable-demons-local-set! domain-variable demons)
  (let ((demons (domain-variable-demons domain-variable)))
   (upon-fail (domain-variable-demons-set! domain-variable demons)))
  (domain-variable-demons-set! domain-variable demons))

 (define (create-domain-variable domain)
  (let ((domain (remove-duplicates domain)))
   (when (null? domain) (fail))
   (make-domain-variable domain '())))

 (define (restrict-domain! d domain)
  (when (null? domain) (fail))
  (when (< (length domain) (length (domain-variable-domain d)))
   (domain-variable-domain-local-set! d domain)
   (for-each (lambda (demon) (demon)) (domain-variable-demons d))))

 (define (bound? d) (null? (rest (domain-variable-domain d))))

 (define (binding d) (first (domain-variable-domain d)))

 (define (nondeterministic-solution ds)
  (let loop ((ds ds) (xs '()))
   (if (null? ds)
       (reverse xs)
       (let ((x (a-member-of (domain-variable-domain (first ds)))))
	(restrict-domain! (first ds) (list x))
	(loop (rest ds) (cons x xs))))))

 (define (some-element predicate d)
  (some (lambda (x) (predicate x)) (domain-variable-domain d)))

 (define (one-element predicate d)
  (one (lambda (x) (predicate x)) (domain-variable-domain d)))

 (define (the-element predicate d)
  (list (find-if (lambda (x) (predicate x)) (domain-variable-domain d))))

 (define (the-elements predicate d)
  (remove-if-not (lambda (x) (predicate x)) (domain-variable-domain d)))

 (define (attach-demon! demon d)
  (domain-variable-demons-local-set! d (cons demon (domain-variable-demons d)))
  (demon))

 (define (assert-constraint-efd! constraint ds)
  (for-each
   (lambda (d)
    (attach-demon! (lambda ()
		    (when (every bound? ds)
		     (unless (apply constraint (map binding ds)) (fail))))
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
	 (fail)))))
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
	 (restrict-domain!
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
	(restrict-domain!
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
	(restrict-domain!
	 d
	 (the-elements
	  (lambda (x)
	   (let loop ((ds ds) (xs '()) (j 0))
	    (if (null? ds)
		(apply constraint (reverse xs))
		(if (= j i)
		    (loop (rest ds) (cons x xs) (+ j 1))
		    (some-element
		     (lambda (x) (loop (rest ds) (cons x xs) (+ j 1)))
		     (first ds))))))
	  d)))
       ds))
     d))
   ds))

 (define (assert-nondeterministic-constraint! constraint . ds)
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
