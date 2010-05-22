#!r6rs

(library
 (nondeterministic-scheme)
 (export a-boolean fail domain remove-duplicates a-member-of possibly? amb
	 upon-fail)
 (import (rnrs) (QobiScheme))

 (define (*a-boolean*) (error #f "Top-level a-boolean"))

 (define (a-boolean) (*a-boolean*))

 (define (*fail*) (error #f "Top-level fail"))

 (define (fail) (*fail*))

 (define (domain-thunk thunk)
  (call-with-current-continuation
   (lambda (c)
    (let ((domain '()) (saved-a-boolean *a-boolean*) (saved-fail *fail*))
     (set! *a-boolean*
	   (lambda ()
	    (call-with-current-continuation
	     (lambda (c)
	      (let ((saved-fail *fail*))
	       (set! *fail*
		     (lambda ()
		      (set! *fail* saved-fail)
		      (c #f))))
	      #t))))
     (set! *fail*
	   (lambda ()
	    (set! *a-boolean* saved-a-boolean)
	    (set! *fail* saved-fail)
	    (c (reverse domain))))

     (let ((result (thunk)))
      (set! domain (cons result domain)))
     (fail)))))

 (define-syntax domain
  (syntax-rules () ((domain e) (domain-thunk (lambda () e)))))

 (define (remove-duplicates domain)
  (let loop ((domain domain) (new-domain '()))
   (cond ((null? domain) (reverse new-domain))
	 ((member (first domain) new-domain) (loop (rest domain) new-domain))
	 (else (loop (rest domain) (cons (first domain) new-domain))))))

 (define (a-member-of domain)
  (let loop ((domain domain))
   (cond ((null? domain) (fail))
	 ((a-boolean) (first domain))
	 (else (loop (rest domain))))))

 (define (possibly? domain) (some (lambda (x) x) domain))

 (define-syntax amb (syntax-rules () ((amb e1 e2) (if (a-boolean) e1 e2))))

 (define (upon-fail-thunk thunk)
  (let ((saved-fail *fail*)) (set! *fail* (lambda () (thunk) (saved-fail)))))

 (define-syntax upon-fail
  (syntax-rules () ((upon-fail e) (upon-fail-thunk (lambda () e))))))
