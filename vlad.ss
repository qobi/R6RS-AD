#!r6rs

(library
 (vlad)
 (export vlad)
 (import (rnrs) (rnrs r5rs (6)))

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

;;;\needswork: There may be a bug here and in the original AD.ss as to where
;;; (set! *e* (- *e* 1)) belongs in forward-mode and reverse-mode.

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

;;;\needswork: We don't provide (co)tangent vector mode.
;;;\needswork: We don't provide the ability to choose y-sensitivity after
;;;             computing y.
;;;\needswork: We don't provide the ability to perform the (co)tangent
;;;            computation multiple times after a single primal computation.

 (define-record-type il:constant-expression (fields value))

 (define-record-type il:variable-access-expression (fields variable))

 (define-record-type il:lambda-expression (fields variable expression))

 (define-record-type il:unary-expression (fields procedure expression))

 (define-record-type il:binary-expression
  (fields procedure expression1 expression2))

 (define-record-type il:ternary-expression
  (fields procedure expression1 expression2 expression3))

 (define-record-type il:binding (fields variable value))

 (define-record-type il:closure (fields expression environment))

 (define-record-type il:continuation (fields procedure values))

 (define-record-type il:checkpoint
  (fields continuation expression environment count))

;;; Short-circuit if is implemented with syntax that wraps with lambda and a
;;; ternary expression that implements applicative-order if.
;;; Application is implemented as a binary expression with il:apply as the
;;; procedure.
;;; j* and *j are implemented as ternary expressions with il:j* and il:*j as the
;;; procedure.

 (define (il:lookup variable environment)
  (cond ((null? environment) (error #f "Unbound variable: ~s" variable))
	((eq? variable (il:binding-variable (first environment)))
	 (il:binding-value (first environment)))
	(else (il:lookup variable (rest environment)))))

 (define (il:walk1 f x)
  (cond ((eq? x #t) #t)
	((eq? x #f) #f)
	((null? x) '())
	((real? x) (f x))
	((pair? x) (cons (il:walk1 f (car x)) (il:walk1 f (cdr x))))
	((il:binding? x)
	 (make-il:binding (il:binding-variable x)
			  (il:walk1 f (il:binding-value x))))
	((il:closure? x)
	 (make-il:closure (il:closure-expression x)
			  (il:walk1 f (il:closure-environment x))))
	((il:continuation? x)
	 (make-il:continuation (il:continuation-procedure x)
			       (il:walk1 f (il:continuation-values x))))
	((il:checkpoint? x)
	 (make-il:checkpoint (il:walk1 f (il:checkpoint-continuation x))
			     (il:checkpoint-expression x)
			     (il:walk1 f (il:checkpoint-environment x))
			     (il:checkpoint-count x)))
	(else (error #f "Can't walk1: ~s" x))))

 (define (il:walk2 f x x-prime)
  (cond
   ((and (eq? x #t) (eq? x-prime #t)) #t)
   ((and (eq? x #f) (eq? x-prime #f)) #f)
   ((and (null? x) (null? x-prime)) '())
   ((and (real? x) (real? x-prime)) (f x x-prime))
   ((and (pair? x) (pair? x-prime))
    (cons (il:walk2 f (car x) (car x-prime))
	  (il:walk2 f (cdr x) (cdr x-prime))))
   ((and (il:binding? x)
	 (il:binding? x-prime)
	 (eq? (il:binding-variable x) (il:binding-variable x-prime)))
    (make-il:binding
     (il:binding-variable x)
     (il:walk2 f (il:binding-value x) (il:binding-value x-prime))))
   ((and (il:closure? x) (il:closure? x-prime)
	 (eq? (il:closure-expression x) (il:closure-expression x-prime)))
    (make-il:closure (il:closure-expression x)
		     (il:walk2 f
			       (il:closure-environment x)
			       (il:closure-environment x-prime))))
   ((and (il:continuation? x)
	 (il:continuation? x-prime)
	 (eq? (il:continuation-procedure x)
	      (il:continuation-procedure x-prime)))
    (make-il:continuation
     (il:continuation-procedure x)
     (il:walk2 f (il:continuation-values x) (il:continuation-values x-prime))))
   ((and (il:checkpoint? x)
	 (il:checkpoint? x-prime)
	 (eq? (il:checkpoint-expression x) (il:checkpoint-expression x-prime))
	 (= (il:checkpoint-count x) (il:checkpoint-count x-prime)))
    (make-il:checkpoint (il:walk2 f
				  (il:checkpoint-continuation x)
				  (il:checkpoint-continuation x-prime))
			(il:checkpoint-expression x)
			(il:walk2 f
				  (il:checkpoint-environment x)
				  (il:checkpoint-environment x-prime))
			(il:checkpoint-count x)))
   (else (error #f "Can't walk2: ~s ~s" x x-prime))))

 (define (il:walk1! f x)
  (cond ((eq? x #t) #f)
	((eq? x #f) #f)
	((null? x) #f)
	((real? x) (f x))
	((pair? x) (il:walk1! f (car x)) (il:walk1! f (cdr x)))
	((il:binding? x) (il:walk1! f (il:binding-value x)))
	((il:closure? x) (il:walk1! f (il:closure-environment x)))
	((il:continuation? x) (il:walk1! f (il:continuation-values x)))
	((il:checkpoint? x)
	 (il:walk1! f (il:checkpoint-continuation x))
	 (il:walk1! f (il:checkpoint-environment x)))
	(else (error #f "Can't walk1!: ~s" x))))

 (define (il:walk2! f x x-prime)
  (cond
   ((and (eq? x #t) (eq? x-prime #t)) #f)
   ((and (eq? x #f) (eq? x-prime #f)) #f)
   ((and (null? x) (null? x-prime)) #f)
   ((and (real? x) (real? x-prime)) (f x x-prime))
   ((and (pair? x) (pair? x-prime))
    (il:walk2! f (car x) (car x-prime))
    (il:walk2! f (cdr x) (cdr x-prime)))
   ((and (il:binding? x)
	 (il:binding? x-prime)
	 (eq? (il:binding-variable x) (il:binding-variable x-prime)))
    (il:walk2! f (il:binding-value x) (il:binding-value x-prime)))
   ((and (il:closure? x)
	 (il:closure? x-prime)
	 (eq? (il:closure-expression x) (il:closure-expression x-prime)))
    (il:walk2! f (il:closure-environment x) (il:closure-environment x-prime)))
   ((and (il:continuation? x)
	 (il:continuation? x-prime)
	 (eq? (il:continuation-procedure x)
	      (il:continuation-procedure x-prime)))
    (il:walk2! f (il:continuation-values x) (il:continuation-values x-prime)))
   ((and (il:checkpoint? x)
	 (il:checkpoint? x-prime)
	 (eq? (il:checkpoint-expression x) (il:checkpoint-expression x-prime))
	 (= (il:checkpoint-count x) (il:checkpoint-count x-prime)))
    (il:walk2!
     f (il:checkpoint-continuation x) (il:checkpoint-continuation x-prime))
    (il:walk2!
     f (il:checkpoint-environment x) (il:checkpoint-environment x-prime)))
   (else (error #f "Can't walk2!: ~s ~s" x x-prime))))

 (define (il:make-continuation procedure . values)
  (make-il:continuation procedure values))

 (define (il:call-continuation continuation value count)
  (apply (il:continuation-procedure continuation)
	 value
	 count
	 (il:continuation-values continuation)))

 (define (il:apply continuation value1 value2 count limit)
  (if (il:closure? value1)
      (il:eval
       continuation
       (il:lambda-expression-expression (il:closure-expression value1))
       (cons (make-il:binding
	      (il:lambda-expression-variable (il:closure-expression value1))
	      value2)
	     (il:closure-environment value1))
       count
       limit)
      (error #f "Not a closure: ~s" value1)))

 (define (forward-mode
	  continuation map-independent map-dependent f x x-perturbation)
  (set! *e* (+ *e* 1))
  ;; This does not need to close over continuation or map-dependent since they
  ;; are opaque.
  (f (il:make-continuation
      (lambda (y-forward count)
       (set! *e* (- *e* 1))
       (il:call-continuation
	continuation
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
			     y-forward))
	count)))
     (map-independent (lambda (x x-perturbation)
		       (make-dual-number *e* x x-perturbation))
		      x
		      x-perturbation)))

 (define (reverse-mode continuation
		       map-independent
		       map-dependent
		       for-each-dependent1!
		       for-each-dependent2!
		       f
		       x
		       y-sensitivities)
  (set! *e* (+ *e* 1))
  (let ((x-reverse (map-independent tapify x)))
   ;; This does not need to close over continuation, map-independent,
   ;; map-dependent,  for-each-dependent1!, or for-each-dependent2! since they
   ;; are opaque.
   (f (il:make-continuation
       (lambda (y-reverse count x-reverse y-sensitivities)
	(let ((x-sensitivities
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
	 (il:call-continuation
	  continuation
	  (list
	   (map-dependent
	    (lambda (y-reverse)
	     (if (or (not (tape? y-reverse)) (<_e (tape-epsilon y-reverse) *e*))
		 y-reverse
		 (tape-primal y-reverse)))
	    y-reverse)
	   x-sensitivities)
	  count)))
       x-reverse
       y-sensitivities)
      x-reverse)))

 (define (il:j* continuation value1 value2 value3 count limit)
  (forward-mode
   continuation
   il:walk2
   il:walk1
   (lambda (continuation x) (il:apply continuation value1 x count limit))
   value2
   value3))

 (define (il:*j continuation value1 value2 value3 count limit)
  (reverse-mode
   (il:make-continuation
    (lambda (y count continuation)
     (il:call-continuation continuation (list (car y) (car (cadr y))) count))
    continuation)
   il:walk1
   il:walk1
   il:walk1!
   il:walk2!
   (lambda (continuation x) (il:apply continuation value1 x count limit))
   value2
   (list value3)))

 (define (il:eval continuation expression environment count limit)
  ;; Every entry into il:eval increments count exactly once. So if you call
  ;; il:eval with count=0 and it doesn't checkpoint, continuation is called with
  ;; count=n being the total number of calls to (entries into) il:eval during
  ;; the evaluation. If you evaluate the same expression in the same environment
  ;; with count=0 and limit>=n then it will not checkpoint. But if called with
  ;; count=0 and limit=(0<=i<n) then it will checkpoint upon entry to the ith
  ;; call. The entries are numbered 0,...,i.
  (if (= count limit)
      (make-il:checkpoint continuation expression environment count)
      (cond
       ((il:constant-expression? expression)
	(il:call-continuation
	 continuation (il:constant-expression-value expression) (+ count 1)))
       ((il:variable-access-expression? expression)
	(il:call-continuation
	 continuation
	 (il:lookup (il:variable-access-expression-variable expression)
		    environment)
	 (+ count 1)))
       ((il:lambda-expression? expression)
	(il:call-continuation continuation
			      (make-il:closure expression environment)
			      (+ count 1)))
       ((il:unary-expression? expression)
	(il:eval
	 (il:make-continuation
	  (lambda (value count continuation)
	   ((il:unary-expression-procedure expression)
	    continuation value count limit))
	  continuation)
	 (il:unary-expression-expression expression)
	 environment
	 (+ count 1)
	 limit))
       ((il:binary-expression? expression)
	(il:eval
	 (il:make-continuation
	  (lambda (value1 count continuation)
	   (il:eval
	    (il:make-continuation
	     (lambda (value2 count continuation value1)
	      ((il:binary-expression-procedure expression)
	       continuation value1 value2 count limit))
	     continuation
	     value1)
	    (il:binary-expression-expression2 expression)
	    environment
	    count
	    limit))
	  continuation)
	 (il:binary-expression-expression1 expression)
	 environment
	 (+ count 1)
	 limit))
       ((il:ternary-expression? expression)
	(il:eval
	 (il:make-continuation
	  (lambda (value1 count continuation)
	   (il:eval
	    (il:make-continuation
	     (lambda (value2 count continuation value1)
	      (il:eval (il:make-continuation
			(lambda (value3 count continuation value1 value2)
			 ((il:ternary-expression-procedure expression)
			  continuation value1 value2 value3 count limit))
			continuation
			value1
			value2)
		       (il:ternary-expression-expression3 expression)
		       environment
		       count
		       limit))
	     continuation
	     value1)
	    (il:ternary-expression-expression2 expression)
	    environment
	    count
	    limit))
	  continuation)
	 (il:ternary-expression-expression1 expression)
	 environment
	 (+ count 1)
	 limit))
       (else (error #f "Invalid expression: ~s" expression)))))

;;; Now we have the substrate to implement checkpointing reverse. It should
;;; have the same interface as il:*j.

 (define (il:checkpoint-*j continuation value1 value2 value3 count limit)
  ;;\needswork: What happens when there is nesting? When there is no nesting,
  ;;            the input limit is infinity. So primops doesn't checkpoint. And
  ;;            resume doesn't checkpoint. But in a nested call, limit can be
  ;;            finite and short enough to cause primops and resume to
  ;;            checkpoint.
  ;; The first half of the computation is executed three times:
  ;; 1. (y,2n)=primops(f,x)
  ;; 2. c=checkpoint(f,x,n)
  ;; 4. (c,x`)=*j(\x.checkpoint(f,x,n),x,c`)
  ;; The second half of the computation is executed two times:
  ;; 1. (y,2n)=primops(f,x)
  ;; 3. (y,c`)=*j(\c.resume(c),c,y`)
  ;; But each half is counted only once.
  ;;
  ;; 1. (y,2n)=primops(f,x)
  ;; f is value1
  ;; x is value2
  ;; y is value4
  ;; n is (quotient (- count4 count) 2)
  (il:apply
   (il:make-continuation
    (lambda (value4 count4 continuation value1 value2 value3)
     ;; count4 must be greater than count because it is incremented before any
     ;; path to calling this continuation to il:apply.
     ;; (= (+ count 1) count4)<->(zero? (quotient (- count4 count) 2))
     (if (= (+ count 1) count4)
	 ;; This means that the count for computing primops is ignored.
	 (il:*j continuation value1 value2 value3 count limit)
	 ;; 2. c=checkpoint(f,x,n)
	 ;; f is value1
	 ;; x is value2
	 ;; n is (quotient (- count4 count) 2)
	 ;; c is checkpoint5
	 (let ((checkpoint5
		(il:apply
		 ;; This continuation won't be called with the checkpoint
		 ;; computation but will be called upon resume.
		 (il:make-continuation
		  ;; This closes over value4 only for consistency checking.
		  (lambda (value6 count6 continuation value1 value2 value4)
		   ;; 4. (c,x`)=*j(\x.checkpoint(f,x,n),x,c`)
		   ;; f is value1
		   ;; x is value2
		   ;; c` is (second value6)
		   ;; c is (first value7)
		   ;; x` is (second value7)
		   (unless (equal? value4 (first value6))
		    (error #f "(not (equal? value4 (first value6)))"))
		   (il:checkpoint-*j
		    (il:make-continuation
		     (lambda (value7 count7 continuation value6)
		      (unless (= count7 (+ count (quotient (- count4 count) 2)))
		       (error #f "(not (= count7 (+ count (quotient (- count4 count) 2))))"))
		      ;; We can't check that (equal? checkpoint5 (first value7))
		      ;; because we can't close over checkpoint5.
		      (il:call-continuation
		       ;; This fakes the count as if both halves of the
		       ;; computation were executed exactly once.
		       continuation
		       (list (first value6) (second value7))
		       count4))
		     continuation
		     value6)
		    ;; This is a closure that behaves like \x.checkpoint(f,x,n).
		    (make-il:closure
		     (make-il:lambda-expression
		      'x
		      (make-il:binary-expression
		       (lambda (continuation8 value8 value9 count8 limit8)
			(unless (= count8 count)
			 (error #f "(not (= count8 count))"))
			(unless (= limit8
				   (+ count (quotient (- count4 count) 2)))
			 (error #f "(not (= limit8 (+ count (quotient (- count4 count) 2))))"))
			(il:apply continuation8 value8 value9 count8 limit8))
		       (make-il:variable-access-expression 'f)
		       (make-il:variable-access-expression 'x)))
		     (list (make-il:binding 'f value1)))
		    value2
		    (second value6)
		    ;; This is for the first half of the computation.
		    count
		    ;; If (zero? (quotient (- count4 count) 2)) then the
		    ;; evaluation could checkpoint right at the start without
		    ;; making any progress. But that can't happen.
		    (+ count (quotient (- count4 count) 2))))
		  continuation
		  value1
		  value2
		  value4)
		 value1
		 value2
		 ;; This is for the first half of the computation.
		 ;; This means that the count for computing primops is ignored.
		 count
		 ;; If (zero? (quotient (- count4 count) 2)) then the evaluation
		 ;; could checkpoint right at the start without making any
		 ;; progress. But that can't happen.
		 (+ count (quotient (- count4 count) 2)))))
	  ;; 3. (y,c`)=*j(\c.resume(c),c,y`)
	  ;; c is checkpoint5
	  ;; y` is value3
	  ;; y is (first value6)
	  ;; c` is (second value6)
	  (il:checkpoint-*j
	   ;; This continuation will become continuation10 and never be called.
	   'continuation10
	   ;; This is a closure that behaves like \c.resume(c).
	   (make-il:closure
	    (make-il:lambda-expression
	     'c
	     (make-il:unary-expression
	      (lambda (continuation10 value10 count10 limit10)
	       ;; continuation10 is ignored. What this means is that the CPS
	       ;; resume never calls its continuation, which in turn means that
	       ;; the direction-style resume never returns. This is correct, and
	       ;; is analogous to fail never returning.
	       ;;\needswork: Could eliminate (il:checkpoint-count value10).
	       (unless (= count10 (il:checkpoint-count value10))
		(error #f "(not (= count10 (il:checkpoint-count value10)))"))
	       (unless (= count10 (+ count (quotient (- count4 count) 2)))
		(error
		 #f
		 "(not (= count10 (+ count (quotient (- count4 count) 2))))"))
	       (unless (= limit10 limit) (error #f "(not (= limit10 limit))"))
	       (il:eval (il:checkpoint-continuation value10)
			(il:checkpoint-expression value10)
			(il:checkpoint-environment value10)
			count10
			limit10))
	      (make-il:variable-access-expression 'c)))
	    '())
	   checkpoint5
	   value3
	   ;; This is for the second half of the computation.
	   ;;\needswork: To guarantee that
	   ;;            (> limit (+ count (quotient (- count4 count) 2))).
	   (+ count (quotient (- count4 count) 2))
	   limit))))
    continuation
    value1
    value2
    value3)
   value1
   value2
   count
   limit))

;;; removed compile-time-error

 (define first car)

 (define second cadr)

 (define third caddr)

 (define fourth cadddr)

 (define rest cdr)

 (define (every p l . &rest)
  (let loop ((l l) (&rest &rest))
   (or (null? l)
       (and (apply p (first l) (map first &rest))
	    (loop (rest l) (map rest &rest))))))

 (define (last x) (if (null? (rest x)) (first x) (last (rest x))))

 (define (but-last x) (reverse (rest (reverse x))))

 (define *index* -1)

 (define (gensym)
  (set! *index* (+ *index* 1))
  (string->symbol (string-append "x" (number->string *index*))))

 (define (duplicatesq? xs)
  (and (not (null? xs))
       (or (memq (first xs) (rest xs)) (duplicatesq? (rest xs)))))

 (define (find-if p l)
  (let loop ((l l))
   (cond ((null? l) #f)
	 ((p (first l)) (first l))
	 (else (loop (rest l))))))

 (define (read-source pathname)
  ;; removed default extension
  ;; removed include
  (call-with-input-file pathname
   (lambda (input-port)
    (let loop ((es '()))
     (let ((e (read input-port)))
      (if (eof-object? e) (reverse es) (loop (cons e es))))))))

 (define (concrete-variable? x)
  (and (symbol? x)
       (not (memq x '(quote
		      lambda
		      letrec
		      let
		      let*
		      if
		      cons
		      cons*
		      list
		      cond
		      else
		      and
		      or)))))

 (define (definens? e)
  (or (concrete-variable? e)
      (and (list? e) (not (null? e)) (definens? (first e)))))

 (define (definition? d)
  (and (list? d)
       (>= (length d) 3)
       (eq? (first d) 'define)
       (definens? (second d))
       (or (not (concrete-variable? (second d))) (= (length d) 3))))

 (define (definens-name e)
  (if (concrete-variable? e) e (definens-name (first e))))

 (define (definens-expression e es)
  (if (concrete-variable? e)
      (first es)
      (definens-expression (first e) (list `(lambda ,(rest e) ,@es)))))

 (define (expand-definitions ds e)
  (for-each (lambda (d)
	     (unless (definition? d) (error #f "Invalid definition: ~s" d)))
	    ds)
  (if (null? ds)
      e
      `(letrec ,(map (lambda (d)
		      `(,(definens-name (second d))
			,(definens-expression (second d) (rest (rest d)))))
		     ds)
	,e)))

 (define (value? v)
  (or (null? v)
      (boolean? v)
      (real? v)
      (and (pair? v) (value? (car v)) (value? (cdr v)))))

 (define (syntax-check-parameter! p)
  (cond ((boolean? p) (syntax-check-parameter! `',p))
	((real? p) (syntax-check-parameter! `',p))
	((concrete-variable? p)
	 (unless (concrete-variable? p) (error #f "Invalid parameter: ~s" p))
	 #f)
	((and (list? p) (not (null? p)))
	 (case (first p)
	  ((quote) (unless (and (= (length p) 2) (value? (second p)))
		    (error #f "Invalid parameter: ~s" p))
	   #f)
	  ((cons)
	   (unless (= (length p) 3) (error #f "Invalid parameter: ~s" p))
	   (syntax-check-parameter! (second p))
	   (syntax-check-parameter! (third p)))
	  ((cons*) (syntax-check-parameter! (macro-expand p)))
	  ((list) (syntax-check-parameter! (macro-expand p)))
	  (else (error #f "Invalid parameter: ~s" p))))
	(else (error #f "Invalid parameter: ~s" p))))

 (define (valid-body? es)
  (and (not (null? es)) (every definition? (but-last es))))

 (define (macro-expand-body es) (expand-definitions (but-last es) (last es)))

 (define (macro-expand e)
  (if (and (list? e) (not (null? e)))
      (case (first e)
       ((lambda)
	(unless (and (>= (length e) 3)
		     (list? (second e))
		     (valid-body? (rest (rest e))))
	 (error #f "Invalid expression: ~s" e))
	(case (length (second e))
	 ((0) `(lambda ((cons* ,@(second e)))
		,(macro-expand-body (rest (rest e)))))
	 ;;\needswork: macro-expand parameters
	 ((1) `(lambda ,(second e) ,(macro-expand-body (rest (rest e)))))
	 (else `(lambda ((cons* ,@(second e)))
		 ,(macro-expand-body (rest (rest e)))))))
       ((let) (cond ((and (>= (length e) 3)
			  (list? (second e))
			  (every (lambda (b) (and (list? b) (= (length b) 2)))
				 (second e)))
		     `((lambda ,(map first (second e)) ,@(rest (rest e)))
		       ,@(map second (second e))))
		    ((and (>= (length e) 4)
			  (concrete-variable? (second e))
			  (list? (third e))
			  (every (lambda (b) (and (list? b) (= (length b) 2)))
				 (third e)))
		     `(letrec ((,(second e)
				(lambda ,(map first (third e))
				 ,@(rest (rest (rest e))))))
		       (,(second e) ,@(map second (third e)))))
		    (else (error #f "Invalid expression: ~s" e))))
       ((let*)
	(unless (and (>= (length e) 3)
		     (list? (second e))
		     (every (lambda (b) (and (list? b) (= (length b) 2)))
			    (second e))
		     (valid-body? (rest (rest e))))
	 (error #f "Invalid expression: ~s" e))
	(case (length (second e))
	 ((0) (macro-expand-body (rest (rest e))))
	 ((1) `(let ,(second e) ,@(rest (rest e))))
	 (else `(let (,(first (second e)))
		 (let* ,(rest (second e)) ,@(rest (rest e)))))))
       ;;\needswork: if
       ((if)
	(unless (= (length e) 4)
	 (error #f "Invalid expression: ~s" e))
	;; needs work: To ensure that you don't shadow if-procedure.
	`(if-procedure
	  ,(second e) (lambda () ,(third e)) (lambda () ,(fourth e))))
       ((cons*) (case (length (rest e))
		 ((0) ''())
		 ((1) (second e))
		 (else `(cons ,(second e) (cons* ,@(rest (rest e)))))))
       ((list)
	(if (null? (rest e)) ''() `(cons ,(second e) (list ,@(rest (rest e))))))
       ;; We don't allow (cond ... (e) ...) or (cond ... (e1 => e2) ...).
       ((cond)
	(unless (and (>= (length e) 2)
		     (every (lambda (b) (and (list? b) (= (length b) 2)))
			    (rest e))
		     (eq? (first (last e)) 'else))
	 (error #f "Invalid expression: ~s" e))
	(if (null? (rest (rest e)))
	    (second (second e))
	    `(if ,(first (second e))
		 ,(second (second e))
		 (cond ,@(rest (rest e))))))
       ((and) (case (length (rest e))
	       ((0) #t)
	       ((1) (second e))
	       (else `(if ,(second e) (and ,@(rest (rest e))) #f))))
       ((or) (case (length (rest e))
	      ((0) #f)
	      ((1) (second e))
	      (else
	       (let ((x (gensym)))
		`(let ((,x ,(second e))) (if ,x ,x (or ,@(rest (rest e)))))))))
       (else (case (length (rest e))
	      ((0) `(,(first e) (cons* ,@(rest e))))
	      ((1) e)
	      (else `(,(first e) (cons* ,@(rest e)))))))
      e))

 (define (parameter-variables p) (error #f "here I am A"))

 (define (create-letrec-expression xs es e) (error #f "here I am B"))

 (define (free-variables e) (error #f "here I am C"))

 (define (syntax-check-expression! e)
  (let loop ((e e) (xs (map il:binding-variable *top-level-environment*)))
   (cond
    ((boolean? e) (loop `',e xs))
    ((real? e) (loop `',e xs))
    ((concrete-variable? e)
     (unless (memq e xs) (error #f "Unbound variable: ~s" e))
     #f)
    ((and (list? e) (not (null? e)))
     (case (first e)
      ((quote)
       (unless (and (= (length e) 2) (value? (second e)))
	(error #f "Invalid expression: ~s" e))
       #f)
      ((lambda)
       (unless (and (>= (length e) 3)
		    (list? (second e))
		    (valid-body? (rest (rest e))))
	(error #f "Invalid expression: ~s" e))
       (case (length (second e))
	((0) (loop (macro-expand e) xs))
	((1)
	 (syntax-check-parameter! (first (second e)))
	 (let ((xs0 (parameter-variables
		     (internalize-expression (first (second e))))))
	  (when (duplicatesq? xs0)
	   (error #f "Duplicate variables: ~s" e))
	  (loop (macro-expand-body (rest (rest e))) (append xs0 xs))))
	(else (loop (macro-expand e) xs))))
      ;;\needswork: letrec
      ((letrec)
       (unless (and (>= (length e) 3)
		    (list? (second e))
		    (every
		     (lambda (b)
		      (and (list? b)
			   (= (length b) 2) (concrete-variable? (first b))))
		     (second e)))
	(error #f "Invalid expression: ~s" e))
       (let ((xs0 (map first (second e))))
	(when (duplicatesq? xs0)
	 (error #f "Duplicate variables: ~s" e))
	(for-each
	 (lambda (b)
	  (let ((e1 (macro-expand (second b))))
	   (unless (and (list? e1) (= (length e1) 3) (eq? (first e1) 'lambda))
	    (error #f "Invalid expression: ~s" e))
	   (loop e1 (append xs0 xs))))
	 (second e))
	(loop (macro-expand-body (rest (rest e))) (append xs0 xs))))
      ((let) (loop (macro-expand e) xs))
      ((let*) (loop (macro-expand e) xs))
      ;;\needswork: if
      ((if) (loop (macro-expand e) xs))
      ((cons)
       (unless (= (length e) 3) (error #f "Invalid expression: ~s" e))
       (loop (second e) xs)
       (loop (third e) xs))
      ((cons*) (loop (macro-expand e) xs))
      ((list) (loop (macro-expand e) xs))
      ((cond) (loop (macro-expand e) xs))
      ((and) (loop (macro-expand e) xs))
      ((or) (loop (macro-expand e) xs))
      (else (case (length (rest e))
	     ((0) (loop (macro-expand e) xs))
	     ((1) (loop (first e) xs)
	      (loop (second e) xs))
	     (else (loop (macro-expand e) xs))))))
    (else (error #f "Invalid expression: ~s" e)))))

 (define (internalize-expression e)
  (cond
   ((boolean? e) (internalize-expression `',e))
   ((real? e) (internalize-expression `',e))
   ((concrete-variable? e) (make-il:variable-access-expression e))
   ((and (list? e) (not (null? e)))
    (case (first e)
     ((quote) (make-il:constant-expression (second e)))
     ((lambda)
      (case (length (second e))
       ((0) (internalize-expression (macro-expand e)))
       ((1) (make-il:lambda-expression
	     (internalize-expression (first (second e)))
	     (internalize-expression (macro-expand-body (rest (rest e))))))
       (else (internalize-expression (macro-expand e)))))
     ((letrec)
      ;;\needswork: letrec
      (create-letrec-expression
       (map first (second e))
       (map (lambda (b) (internalize-expression (macro-expand (second b))))
	    (second e))
       (internalize-expression (macro-expand-body (rest (rest e))))))
     ((let) (internalize-expression (macro-expand e)))
     ((let*) (internalize-expression (macro-expand e)))
     ;;\needswork: if
     ((if) (internalize-expression (macro-expand e)))
     ((cons) (make-il:binary-expression
	      (lambda (continuation value1 value2 count limit)
	       (il:call-continuation (cons value1 value2) count))
	      (internalize-expression (second e))
	      (internalize-expression (third e))))
     ((cons*) (internalize-expression (macro-expand e)))
     ((list) (internalize-expression (macro-expand e)))
     ((cond) (internalize-expression (macro-expand e)))
     ((and) (internalize-expression (macro-expand e)))
     ((or) (internalize-expression (macro-expand e)))
     (else (case (length (rest e))
	    ((0) (internalize-expression (macro-expand e)))
	    ((1) (make-il:binary-expression
		  il:apply
		  (internalize-expression (first e))
		  (internalize-expression (second e))))
	    (else (internalize-expression (macro-expand e)))))))
   (else (error #f "Can't internalize: ~s" e))))

 (define (concrete->abstract e)
  (let ((e (internalize-expression e)))
   (list e
	 (map (lambda (x)
	       (find-if (lambda (b) (eq? x (il:binding-variable b)))
			*top-level-environment*))
	      (free-variables e)))))

 (define (make-unary-primitive variable f)
  (make-il:binding
   variable
   (make-il:closure
    (make-il:lambda-expression
     'x
     (make-il:unary-expression
      (lambda (continuation value count limit)
       (il:call-continuation (f value) count))
      (make-il:variable-access-expression 'x)))
    '())))

 (define (make-binary-primitive variable f)
  (make-il:binding
   variable
   (make-il:closure
    (make-il:lambda-expression
     'x
     (make-il:unary-expression
      (lambda (continuation value count limit)
       (il:call-continuation (f (car value) (cdr value)) count))
      (make-il:variable-access-expression 'x)))
    '())))

 (define (make-ternary-primitive variable f)
  (make-il:binding
   variable
   (make-il:closure
    (make-il:lambda-expression
     'x
     (make-il:unary-expression
      (lambda (continuation value count limit)
       (il:call-continuation
	(f (car value) (car (cdr value)) (cdr (cdr value))) count))
      (make-il:variable-access-expression 'x)))
    '())))

 (define *top-level-environment*
  (list (make-binary-primitive '+ d+)
	(make-binary-primitive '- d-)
	(make-binary-primitive '* d*)
	(make-binary-primitive '/ d/)
	(make-unary-primitive 'sqrt dsqrt)
	(make-unary-primitive 'exp dexp)
	(make-unary-primitive 'log dlog)
	(make-unary-primitive 'sin dsin)
	(make-unary-primitive 'cos dcos)
	(make-binary-primitive 'atan datan)
	(make-binary-primitive '= d=)
	(make-binary-primitive '< d<)
	(make-binary-primitive '> d>)
	(make-binary-primitive '<= d<=)
	(make-binary-primitive '>= d>=)
	(make-unary-primitive 'zero? dzero?)
	(make-unary-primitive 'positive? dpositive?)
	(make-unary-primitive 'negative? dnegative?)
	(make-unary-primitive 'null? null?)
	(make-unary-primitive 'boolean? boolean?)
	(make-unary-primitive 'real? dreal?)
	(make-unary-primitive 'pair? pair?)
	(make-unary-primitive 'procedure? il:closure?)
	(make-ternary-primitive 'j* il:j*)
	(make-ternary-primitive '*j il:*j)
	(make-ternary-primitive 'checkpoint-*j il:checkpoint-*j)))

 (define (vlad pathname)
  (let loop ((es (read-source pathname)) (ds '()))
   (unless (null? es)
    (if (definition? (first es))
	(loop (rest es) (cons (first es) ds))
	(let ((e (expand-definitions (reverse ds) (first es))))
	 (syntax-check-expression! e)
	 (let* ((result (concrete->abstract e))
		(e (first result))
		(bs (second result)))
	  (error #f "here I am D"))
	 (loop (rest es) ds)))))))
