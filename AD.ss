#!r6rs

(library
 (AD)
 (export (rename (d+ +))
	 (rename (d- -))
	 (rename (d* *))
	 (rename (d/ /))
	 (rename (dsqrt sqrt))
	 (rename (dexp exp))
	 (rename (dlog log))
	 (rename (dexpt expt))
	 (rename (dsin sin))
	 (rename (dcos cos))
	 (rename (datan atan))
	 (rename (d= =))
	 (rename (d< <))
	 (rename (d> >))
	 (rename (d<= <=))
	 (rename (d>= >=))
	 (rename (dzero? zero?))
	 (rename (dpositive? positive?))
	 (rename (dnegative? negative?))
	 (rename (dreal? real?))
	 write-real
	 forward-mode
	 derivative-F
	 directional-derivative-list-F
	 directional-derivative-vector-F
	 gradient-list-F
	 gradient-vector-F
	 reverse-mode
	 derivative-R
	 gradient-list-R
	 gradient-vector-R
	 f-gradient-vector-vector-R)
 (import (rnrs))

 (define *e* 0)

 (define <_e <)

 (define-record-type dual-number (fields epsilon primal perturbation))

 (define-record-type
  tape
  (fields
   epsilon primal factors tapes (mutable fanout) (mutable sensitivity)))

 (define (new-tape epsilon primal factors tapes)
  (make-tape epsilon primal factors tapes 0 0))

 (define (tapify x) (new-tape *e* x '() '()))

 (define (lift-real->real f df/dx)
  (letrec ((self (lambda (x)
		  (cond ((dual-number? x)
			 (make-dual-number (dual-number-epsilon x)
					   (self (dual-number-primal x))
					   (d* (df/dx (dual-number-primal x))
					       (dual-number-perturbation x))))
			((tape? x)
			 (new-tape (tape-epsilon x)
				   (self (tape-primal x))
				   (list (df/dx (tape-primal x)))
				   (list x)))
			(else (f x))))))
   self))

 (define (lift-real*real->real f df/dx1 df/dx2)
  (letrec ((self
	    (lambda (x1 x2)
	     (cond
	      ((dual-number? x1)
	       (cond
		((dual-number? x2)
		 (cond
		  ((<_e (dual-number-epsilon x1)
			(dual-number-epsilon x2))
		   (make-dual-number (dual-number-epsilon x2)
				     (self x1 (dual-number-primal x2))
				     (d* (df/dx2 x1 (dual-number-primal x2))
					 (dual-number-perturbation x2))))
		  ((<_e (dual-number-epsilon x2)
			(dual-number-epsilon x1))
		   (make-dual-number (dual-number-epsilon x1)
				     (self (dual-number-primal x1) x2)
				     (d* (df/dx1 (dual-number-primal x1) x2)
					 (dual-number-perturbation x1))))
		  (else
		   (make-dual-number
		    (dual-number-epsilon x1)
		    (self (dual-number-primal x1) (dual-number-primal x2))
		    (d+ (d* (df/dx1 (dual-number-primal x1)
				    (dual-number-primal x2))
			    (dual-number-perturbation x1))
			(d* (df/dx2 (dual-number-primal x1)
				    (dual-number-primal x2))
			    (dual-number-perturbation x2)))))))
		((tape? x2)
		 (if (<_e (dual-number-epsilon x1) (tape-epsilon x2))
		     (new-tape (tape-epsilon x2)
			       (self x1 (tape-primal x2))
			       (list (df/dx2 x1 (tape-primal x2)))
			       (list x2))
		     (make-dual-number (dual-number-epsilon x1)
				       (self (dual-number-primal x1) x2)
				       (d* (df/dx1 (dual-number-primal x1) x2)
					   (dual-number-perturbation x1)))))
		(else (make-dual-number (dual-number-epsilon x1)
					(self (dual-number-primal x1) x2)
					(d* (df/dx1 (dual-number-primal x1) x2)
					    (dual-number-perturbation x1))))))
	      ((tape? x1)
	       (cond
		((dual-number? x2)
		 (if (<_e (tape-epsilon x1) (dual-number-epsilon x2))
		     (make-dual-number (dual-number-epsilon x2)
				       (self x1 (dual-number-primal x2))
				       (d* (df/dx2 x1 (dual-number-primal x2))
					   (dual-number-perturbation x2)))
		     (new-tape (tape-epsilon x1)
			       (self (tape-primal x1) x2)
			       (list (df/dx1 (tape-primal x1) x2))
			       (list x1))))
		((tape? x2)
		 (cond
		  ((<_e (tape-epsilon x1) (tape-epsilon x2))
		   (new-tape (tape-epsilon x2)
			     (self x1 (tape-primal x2))
			     (list (df/dx2 x1 (tape-primal x2)))
			     (list x2)))
		  ((<_e (tape-epsilon x2) (tape-epsilon x1))
		   (new-tape (tape-epsilon x1)
			     (self (tape-primal x1) x2)
			     (list (df/dx1 (tape-primal x1) x2))
			     (list x1)))
		  (else
		   (new-tape (tape-epsilon x1)
			     (self (tape-primal x1) (tape-primal x2))
			     (list (df/dx1 (tape-primal x1) (tape-primal x2))
				   (df/dx2 (tape-primal x1) (tape-primal x2)))
			     (list x1 x2)))))
		(else (new-tape (tape-epsilon x1)
				(self (tape-primal x1) x2)
				(list (df/dx1 (tape-primal x1) x2))
				(list x1)))))
	      (else
	       (cond ((dual-number? x2)
		      (make-dual-number (dual-number-epsilon x2)
					(self x1 (dual-number-primal x2))
					(d* (df/dx2 x1 (dual-number-primal x2))
					    (dual-number-perturbation x2))))
		     ((tape? x2)
		      (new-tape (tape-epsilon x2)
				(self x1 (tape-primal x2))
				(list (df/dx2 x1 (tape-primal x2)))
				(list x2)))
		     (else (f x1 x2))))))))
   self))

 (define (fold f l)
  (let loop ((l (cdr l)) (c (car l)))
   (if (null? l) c (loop (cdr l) (f c (car l))))))

 (define (lift-real^n->real f df/dx1 df/dx2)
  (lambda xs
   (if (null? xs) (f) (fold (lift-real*real->real f df/dx1 df/dx2) xs))))

 (define (lift-real^n+1->real f df/dx df/dx1 df/dx2)
  (lambda xs
   (cond ((null? xs) (f))
	 ((null? (cdr xs)) ((lift-real->real f df/dx) (car xs)))
	 (else (fold (lift-real*real->real f df/dx1 df/dx2) xs)))))

 (define (primal* x)
  (cond ((dual-number? x) (primal* (dual-number-primal x)))
	((tape? x) (primal* (tape-primal x)))
	(else x)))

 (define (lift-real^n->boolean f) (lambda xs (apply f (map primal* xs))))

 (define d+ (lift-real^n->real + (lambda (x1 x2) 1) (lambda (x1 x2) 1)))

 (define d- (lift-real^n+1->real
	     - (lambda (x) -1) (lambda (x1 x2) 1) (lambda (x1 x2) -1)))

 (define d* (lift-real^n->real * (lambda (x1 x2) x2) (lambda (x1 x2) x1)))

 (define d/ (lift-real^n+1->real
	     /
	     (lambda (x) (d- (d/ (d* x x))))
	     (lambda (x1 x2) (d/ x2))
	     (lambda (x1 x2) (d- (d/ x1 (d* x2 x2))))))

 (define dsqrt (lift-real->real sqrt (lambda (x) (d/ (d* 2 (dsqrt x))))))

 (define dexp (lift-real->real exp (lambda (x) (dexp x))))

 (define dlog (lift-real->real log (lambda (x) (d/ x))))

 (define dexpt
  (lift-real*real->real expt
			(lambda (x1 x2) (d* x2 (dexpt x1 (d- x2 1))))
			(lambda (x1 x2) (d* (dlog x1) (dexpt x1 x2)))))

 (define dsin (lift-real->real sin (lambda (x) (dcos x))))

 (define dcos (lift-real->real cos (lambda (x) (d- (dsin x)))))

 (define (datan . xs)
  (cond ((null? xs) (apply atan xs))
	((null? (cdr xs)) (datan (car xs) 1))
	((null? (cdr (cdr xs)))
	 ((lift-real*real->real
	   atan
	   (lambda (x1 x2) (d/ x2 (d+ (d* x1 x1) (d* x2 x2))))
	   (lambda (x1 x2) (d/ (d- x1) (d+ (d* x1 x1) (d* x2 x2)))))
	  (car xs)
	  (cadr xs)))
	(else (apply atan xs))))

 (define d= (lift-real^n->boolean =))

 (define d< (lift-real^n->boolean <))

 (define d> (lift-real^n->boolean >))

 (define d<= (lift-real^n->boolean <=))

 (define d>= (lift-real^n->boolean >=))

 (define dzero? (lift-real^n->boolean zero?))

 (define dpositive? (lift-real^n->boolean positive?))

 (define dnegative? (lift-real^n->boolean negative?))

 (define dreal? (lift-real^n->boolean real?))

 (define (write-real x)
  (cond ((dual-number? x) (write-real (dual-number-primal x)) x)
	((tape? x) (write-real (tape-primal x)) x)
	(else (write x) (newline) x)))

 (define (forward-mode map-independent map-dependent f x x-perturbation)
  ;; needs work: We don't support what the AD community calls tangent vector
  ;;             mode.
  (set! *e* (+ *e* 1))
  (let ((y-forward
	 (f (map-independent (lambda (x x-perturbation)
			      (make-dual-number *e* x x-perturbation))
			     x
			     x-perturbation))))
   (set! *e* (- *e* 1))
   (list (map-dependent (lambda (y-forward)
			 (if (or (not (dual-number? y-forward))
				 (<_e (dual-number-epsilon y-forward) *e*))
			     y-forward
			     (dual-number-primal y-forward)))
			y-forward)
	 (map-dependent (lambda (y-forward)
			 (if (or (not (dual-number? y-forward))
				 (<_e (dual-number-epsilon y-forward) *e*))
			     0
			     (dual-number-perturbation y-forward)))
			y-forward))))

 (define (derivative-F f)
  (lambda (x)
   (cadr (forward-mode (lambda (f x x-perturbation) (f x x-perturbation))
		       (lambda (f y-forward) (f y-forward))
		       f
		       x
		       1))))

 (define (directional-derivative-list-F f)
  (lambda (x x-perturbation)
   (cadr (forward-mode (lambda (f x x-perturbation) (map f x x-perturbation))
		       (lambda (f y-forward) (map f y-forward))
		       f
		       x
		       x-perturbation))))

 (define (for-each-n f n)
  (let loop ((i 0)) (when (< i n) (f i) (loop (+ i 1)))))

 (define (map-vector f v . vs)
  (let ((u (make-vector (vector-length v))))
   (for-each-n
    (lambda (i)
     (vector-set!
      u i (apply f (vector-ref v i) (map (lambda (v) (vector-ref v i)) vs))))
    (vector-length v))
   u))

 (define (directional-derivative-vector-F f)
  (lambda (x x-perturbation)
   (cadr
    (forward-mode (lambda (f x x-perturbation) (map-vector f x x-perturbation))
		  (lambda (f y-forward) (map-vector f y-forward))
		  f
		  x
		  x-perturbation))))

 (define (replace-ith x i xi)
  (if (zero? i)
      (cons xi (cdr x))
      (cons (car x) (replace-ith (cdr x) (- i 1) xi))))

 (define (map-n f n)
  (let loop ((result '()) (i 0))
   (if (= i n) (reverse result) (loop (cons (f i) result) (+ i 1)))))

 (define (gradient-list-F f)
  (lambda (x)
   (map-n
    (lambda (i)
     ((derivative-F (lambda (xi) (f (replace-ith x i xi)))) (list-ref x i)))
    (length x))))

 (define (map-n-vector f n)
  (let ((v (make-vector n)))
   (let loop ((i 0))
    (when (< i n)
     (vector-set! v i (f i))
     (loop (+ i 1))))
   v))

 (define (replace-ith-vector x i xi)
  (map-n-vector
   (lambda (j) (if (= j i) xi (vector-ref x j))) (vector-length x)))

 (define (gradient-vector-F f)
  (lambda (x)
   (map-n-vector (lambda (i)
		  ((derivative-F (lambda (xi) (f (replace-ith-vector x i xi))))
		   (vector-ref x i)))
		 (vector-length x))))

 (define (determine-fanout! tape)
  (tape-fanout-set! tape (+ (tape-fanout tape) 1))
  (when (= (tape-fanout tape) 1)
   (for-each determine-fanout! (tape-tapes tape))))

 (define (initialize-sensitivity! tape)
  (tape-sensitivity-set! tape 0)
  (tape-fanout-set! tape (- (tape-fanout tape) 1))
  (when (zero? (tape-fanout tape))
   (for-each initialize-sensitivity! (tape-tapes tape))))

 (define (reverse-phase! sensitivity tape)
  (tape-sensitivity-set! tape (d+ (tape-sensitivity tape) sensitivity))
  (tape-fanout-set! tape (- (tape-fanout tape) 1))
  (when (zero? (tape-fanout tape))
   (let ((sensitivity (tape-sensitivity tape)))
    (for-each
     (lambda (factor tape) (reverse-phase! (d* sensitivity factor) tape))
     (tape-factors tape)
     (tape-tapes tape)))))

 (define (reverse-mode map-independent
		       map-dependent
		       for-each-dependent1!
		       for-each-dependent2!
		       f
		       x
		       y-sensitivities)
  ;; needs work: We don't support providing the y-sensitivies (potentially
  ;;             incrementally) after computing the primal in the forward
  ;;             phase.
  (set! *e* (+ *e* 1))
  (let* ((x-reverse (map-independent tapify x))
	 (y-reverse (f x-reverse))
	 (x-sensitivities
	  (map (lambda (y-sensitivity)
		(for-each-dependent1!
		 (lambda (y-reverse)
		  (when (and (tape? y-reverse)
			     (not (<_e (tape-epsilon y-reverse) *e*)))
		   (determine-fanout! y-reverse)
		   (initialize-sensitivity! y-reverse)))
		 y-reverse)
		(for-each-dependent2!
		 (lambda (y-reverse y-sensitivity)
		  (when (and (tape? y-reverse)
			     (not (<_e (tape-epsilon y-reverse) *e*)))
		   (determine-fanout! y-reverse)
		   (reverse-phase! y-sensitivity y-reverse)))
		 y-reverse
		 y-sensitivity)
		(map-independent tape-sensitivity x-reverse))
	       y-sensitivities)))
   (set! *e* (- *e* 1))
   (list (map-dependent
	  (lambda (y-reverse)
	   (if (or (not (tape? y-reverse)) (<_e (tape-epsilon y-reverse) *e*))
	       y-reverse
	       (tape-primal y-reverse)))
	  y-reverse)
	 x-sensitivities)))

 (define (derivative-R f)
  (lambda (x)
   (car (cadr (reverse-mode
	       (lambda (f x) (f x))
	       (lambda (f y-reverse) (f y-reverse))
	       (lambda (f y-reverse) (f y-reverse))
	       (lambda (f y-reverse y-sensitivity) (f y-reverse y-sensitivity))
	       f
	       x
	       '(1))))))

 (define (gradient-list-R f)
  (lambda (x)
   (car (cadr (reverse-mode
	       (lambda (f x) (map f x))
	       (lambda (f y-reverse) (f y-reverse))
	       (lambda (f y-reverse) (f y-reverse))
	       (lambda (f y-reverse y-sensitivity) (f y-reverse y-sensitivity))
	       f
	       x
	       '(1))))))

 (define (gradient-vector-R f)
  (lambda (x)
   (car (cadr (reverse-mode
	       (lambda (f x) (map-vector f x))
	       (lambda (f y-reverse) (f y-reverse))
	       (lambda (f y-reverse) (f y-reverse))
	       (lambda (f y-reverse y-sensitivity) (f y-reverse y-sensitivity))
	       f
	       x
	       '(1))))))

 (define (f-gradient-vector-vector-R f)
  (lambda (x)
   (let ((result
	  (reverse-mode
	   (lambda (f x) (map-vector (lambda (x) (map-vector f x)) x))
	   (lambda (f y-reverse) (f y-reverse))
	   (lambda (f y-reverse) (f y-reverse))
	   (lambda (f y-reverse y-sensitivity) (f y-reverse y-sensitivity))
	   f
	   x
	   '(1))))
    (list (car result) (car (cadr result)))))))
