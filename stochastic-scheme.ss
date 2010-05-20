#!r6rs

(library
 (stochastic-scheme)
 (export flip bottom distribution coalesce-duplicates draw-pair draw
	 probability support expected-value entropy upon-bottom)
 (import (except (rnrs) + - * / sqrt exp log expt sin cos atan = < > <= >=
		 zero? positive? negative? real? magnitude)
	 (AD)
	 (QobiScheme))

 (define (*flip* alpha) (error #f "Top-level flip"))

 (define (flip alpha) (*flip* alpha))

 (define (*bottom*) (error #f "Top-level bottom"))

 (define (bottom) (*bottom*))

 (define (distribution-thunk thunk)
  (call-with-current-continuation
   (lambda (c)
    (let ((distribution '()) (saved-flip *flip*) (saved-bottom *bottom*) (p 1))
     (set! *flip*
	   (lambda (alpha)
	    (unless (<= 0 alpha 1) (error #f "Alpha not probability"))
	    (call-with-current-continuation
	     (lambda (c)
	      (let ((saved-bottom *bottom*) (saved-p p))
	       (set! p (* alpha p))
	       (set! *bottom*
		     (lambda ()
		      (set! p (* (- 1 alpha) saved-p))
		      (set! *bottom* saved-bottom)
		      (c #f)))
	       #t)))))
     (set! *bottom*
	   (lambda ()
	    (set! *flip* saved-flip)
	    (set! *bottom* saved-bottom)
	    (c (reverse distribution))))
     (set! distribution (cons (cons (thunk) p) distribution))
     (bottom)))))

 (define-syntax distribution
  (syntax-rules () ((distribution e) (distribution-thunk (lambda () e)))))

 (define (coalesce-duplicates distribution)
  (let loop ((distribution distribution) (new-distribution '()))
   (cond ((null? distribution) (reverse new-distribution))
	 ((zero? (cdr (first distribution)))
	  (loop (rest distribution) new-distribution))
	 ((position-if
	   (lambda (pair) (equal? (car pair) (car (first distribution))))
	   new-distribution)
	  => (lambda (i)
	      (loop (rest distribution)
		    (map-indexed
		     (lambda (pair j)
		      (if (= i j)
			  (cons (car pair)
				(+ (cdr (first distribution)) (cdr pair)))
			  pair))
		     new-distribution))))
	 (else (loop (rest distribution)
		     (cons (first distribution) new-distribution))))))

 (define (draw-pair distribution)
  (define (min x1 x2) (if (< x1 x2) x1 x2))
  (define (max x1 x2) (if (> x1 x2) x1 x2))
  (let loop ((distribution distribution) (p 1))
   (cond
    ((or (zero? p) (null? distribution)) (bottom))
    ((flip (min (/ (cdr (first distribution)) p) 1)) (first distribution))
    (else
     (loop (rest distribution) (max (- p (cdr (first distribution))) 0))))))

 (define (draw distribution) (car (draw-pair distribution)))

 (define (probability distribution)
  (fold + 0 (map cdr (remove-if-not car distribution))))

 (define (support distribution) (map car distribution))

 (define (expected-value distribution)
  (fold + 0 (map (lambda (pair) (* (car pair) (cdr pair))) distribution)))

 (define (entropy distribution)
  (fold
   + 0 (map (lambda (pair) (* (cdr pair) (log (cdr pair)))) distribution)))

 (define (upon-bottom-thunk thunk)
  (let ((saved-bottom *bottom*))
   (set! *bottom* (lambda () (thunk) (saved-bottom)))))

 (define-syntax upon-bottom
  (syntax-rules () ((upon-bottom e) (upon-bottom-thunk (lambda () e))))))
