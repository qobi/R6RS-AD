#!r6rs

(library
 (nondeterministic-lifting)
 (export initialize-domain-variables! domain-variables new-domain-variable
	 true-domain-variable false-domain-variable
	 create-boolean-variable and-constraint or-constraint not-constraint
	 every-constraint some-constraint
	 at-least-constraint at-most-constraint exactly-constraint
	 eq?-constraint memq-constraint assert!)
 (import (rnrs)
	 (QobiScheme)
	 (nondeterministic-scheme)
	 (nondeterministic-constraints)
	 (deterministic-memoization))

 ;; needs work: to all all lifted operations to take either domain variables
 ;;             or values and eliminate true/false-domain-variable

 (define *domain-variables* '())

 (define (initialize-domain-variables!)
  (set! *domain-variables* '())
  (set! *true-domain-variable* (new-domain-variable '(#t)))
  (set! *false-domain-variable* (new-domain-variable '(#f))))

 (define (domain-variables) *domain-variables*)

 (define (new-domain-variable domain)
  (let ((domain-variable (create-domain-variable domain))
	(domain-variables *domain-variables*))
   (upon-fail (set! *domain-variables* domain-variables))
   (set! *domain-variables* (cons domain-variable *domain-variables*))
   domain-variable))

 (define *true-domain-variable* (new-domain-variable '(#t)))

 (define *false-domain-variable* (new-domain-variable '(#f)))

 (define (true-domain-variable) *true-domain-variable*)

 (define (false-domain-variable) *false-domain-variable*)

 (define (create-boolean-variable) (new-domain-variable '(#t #f)))

 (define (and-constraint . boolean-variables)
  (let ((boolean-variable (create-boolean-variable)))
   (apply assert-nondeterministic-constraint!
	  (lambda (boolean . booleans)
	   (eq? boolean (fold (lambda (p q) (and p q)) #t booleans)))
	  boolean-variable
	  boolean-variables)
   boolean-variable))

 (define (or-constraint . boolean-variables)
  (let ((boolean-variable (create-boolean-variable)))
   (apply assert-nondeterministic-constraint!
	  (lambda (boolean . booleans)
	   (eq? boolean (fold (lambda (p q) (or p q)) #f booleans)))
	  boolean-variable
	  boolean-variables)
   boolean-variable))

 (define (not-constraint boolean-variable)
  (let ((boolean-variable1 (create-boolean-variable)))
   (assert-nondeterministic-constraint!
    (lambda (boolean1 boolean) (eq? boolean1 (not boolean)))
    boolean-variable1
    boolean-variable)
   boolean-variable1))

 (define (every-constraint p l)
  (map-reduce and-constraint (true-domain-variable) p l))

 (define (some-constraint p l)
  (map-reduce or-constraint (false-domain-variable) p l))

 (define (at-least-constraint k p l)
  (define at-least-constraint
   (memoize
    (lambda (k l)
     (cond ((negative? k) (fuck-up))
	   ((zero? k) (true-domain-variable))
	   ((null? l) (false-domain-variable))
	   (else (or-constraint
		  (and-constraint (p (first l))
				  (at-least-constraint (- k 1) (rest l)))
		  (and-constraint (not-constraint (p (first l)))
				  (at-least-constraint k (rest l)))))))))
  (at-least-constraint k l))

 (define (at-most-constraint k p l)
  (define at-most-constraint
   (memoize
    (lambda (k l)
     (cond ((negative? k) (fuck-up))
	   ((zero? k) (not-constraint (some-constraint p l)))
	   ((null? l) (true-domain-variable))
	   (else (or-constraint
		  (and-constraint (p (first l))
				  (at-most-constraint (- k 1) (rest l)))
		  (and-constraint (not-constraint (p (first l)))
				  (at-most-constraint k (rest l)))))))))
  (at-most-constraint k l))

 (define (exactly-constraint k p l)
  (define exactly-constraint
   (memoize
    (lambda (k l)
     (cond ((negative? k) (fuck-up))
	   ((zero? k) (not-constraint (some-constraint p l)))
	   ((null? l) (false-domain-variable))
	   (else (or-constraint
		  (and-constraint (p (first l))
				  (exactly-constraint (- k 1) (rest l)))
		  (and-constraint (not-constraint (p (first l)))
				  (exactly-constraint k (rest l)))))))))
  (exactly-constraint k l))

 (define (eq?-constraint domain-variable1 domain-variable2)
  (let ((boolean-variable (create-boolean-variable)))
   (assert-nondeterministic-constraint!
    (lambda (boolean value1 value2) (eq? boolean (eq? value1 value2)))
    boolean-variable
    domain-variable1
    domain-variable2)
   boolean-variable))

 (define (memq-constraint domain-variable domain)
  (let ((boolean-variable (create-boolean-variable)))
   (assert-nondeterministic-constraint!
    (lambda (boolean value) (eq? boolean (not (not (memq value domain)))))
    boolean-variable
    domain-variable)
   boolean-variable))

 (define (assert! boolean-variable)
  (assert-nondeterministic-constraint!
   (lambda (boolean) boolean) boolean-variable)))
