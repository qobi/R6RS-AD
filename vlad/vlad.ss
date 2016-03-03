#!r6rs

(library
 (vlad)
 (export vlad vlad-I)
 (import (rnrs) (rnrs r5rs (6)) (ikarus))

 ;; All threading of path is for debugging.

 (define *debugging?* #t)

 ;;\needswork: The base case would nominally be triggered when count4-count=1
 ;;            but this difference is to compensate for the fudge factors in
 ;;            the counts.
 (define *base-case-duration* 7)

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
  ;; The mutation here is OK with checkpoints because a chackpoint cannot
  ;; occur in the critical section.
  (tape-fanout-set! tape (+ (tape-fanout tape) 1))
  (when (= (tape-fanout tape) 1)
   (for-each determine-fanout! (tape-tapes tape))))

 (define (initialize-sensitivity! tape)
  ;; The mutation here is OK with checkpoints because a chackpoint cannot
  ;; occur in the critical section.
  (tape-sensitivity-set! tape 0)
  (tape-fanout-set! tape (- (tape-fanout tape) 1))
  (when (zero? (tape-fanout tape))
   (for-each initialize-sensitivity! (tape-tapes tape))))

 (define (reverse-phase! sensitivity tape)
  ;; The mutation here is OK with checkpoints because a chackpoint cannot
  ;; occur in the critical section.
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

;;; This evaluator has all of the same vagaries as the Stalingrad evaluator:
;;;   constant expressions instead of constant conversion
;;;   if-procedure
;;;   parameters
;;;   cons is syntax
;;;   +, -, *, /, atan, =, <, >, <=, and >= are binary
;;;   generalized define

 (define-record-type il:constant-expression (fields value))

 (define-record-type il:variable-access-expression (fields variable))

 (define-record-type il:lambda-expression (fields parameter expression))

 (define-record-type il:unary-expression (fields procedure expression))

 (define-record-type il:binary-expression
  (fields procedure expression1 expression2))

 (define-record-type il:ternary-expression
  (fields procedure expression1 expression2 expression3))

 (define-record-type il:letrec-expression
  (fields variables expressions expression))

 (define-record-type il:binding (fields variable value))

 (define-record-type il:nonrecursive-closure (fields expression environment))

 (define-record-type il:recursive-closure
  (fields variables expressions index environment))

 (define-record-type il:continuation (fields id procedure values))

 (define-record-type il:checkpoint
  (fields continuation expression environment count))

;;; Short-circuit if is implemented with syntax that wraps with lambda and a
;;; ternary expression that implements applicative-order if.
;;; Application is implemented as a binary expression with il:apply as the
;;; procedure.
;;; j* and *j are implemented as ternary expressions with il:j* and il:*j as the
;;; procedure.

 (define (il:externalize-expression expression)
  (cond
   ((il:constant-expression? expression)
    (il:constant-expression-value expression))
   ((il:variable-access-expression? expression)
    (il:variable-access-expression-variable expression))
   ((il:lambda-expression? expression)
    `(lambda (,(il:externalize-expression
		(il:lambda-expression-parameter expression)))
      ,(il:externalize-expression
	(il:lambda-expression-expression expression))))
   ((il:unary-expression? expression)
    `(,(il:unary-expression-procedure expression)
      ,(il:externalize-expression (il:unary-expression-expression expression))))
   ((il:binary-expression? expression)
    (cond ((eq? (il:binary-expression-procedure expression) il:apply)
	   `(,(il:externalize-expression
	       (il:binary-expression-expression1 expression))
	     ,(il:externalize-expression
	       (il:binary-expression-expression2 expression))))
	  ((eq? (il:binary-expression-procedure expression) il:cons)
	   `(cons ,(il:externalize-expression
		    (il:binary-expression-expression1 expression))
		  ,(il:externalize-expression
		    (il:binary-expression-expression2 expression))))
	  (else `(,(il:binary-expression-procedure expression)
		  ,(il:externalize-expression
		    (il:binary-expression-expression1 expression))
		  ,(il:externalize-expression
		    (il:binary-expression-expression2 expression))))))
   ((il:ternary-expression? expression)
    `(,(il:ternary-expression-procedure expression)
      ,(il:externalize-expression
	(il:ternary-expression-expression1 expression))
      ,(il:externalize-expression
	(il:ternary-expression-expression2 expression))
      ,(il:externalize-expression
	(il:ternary-expression-expression3 expression))))
   ((il:letrec-expression? expression)
    `(letrec ,(map (lambda (variable expression)
		    `(,variable ,(il:externalize-expression expression)))
		   (il:letrec-expression-variables expression)
		   (il:letrec-expression-expressions expression))
      ,(il:externalize-expression
	(il:letrec-expression-expression expression))))
   (else (internal-error))))

 (define (il:externalize x)
  (cond ((eq? x #t) #t)
	((eq? x #f) #f)
	((null? x) '())
	((dreal? x) x)
	((pair? x) (cons (il:externalize (car x)) (il:externalize (cdr x))))
	((il:binding? x)
	 `(binding ,(il:binding-variable x)
		   ,(il:externalize (il:binding-value x))))
	((il:nonrecursive-closure? x)
	 `(nonrecursive-closure
	   ,(il:externalize-expression (il:nonrecursive-closure-expression x))
	   ,(il:externalize (il:nonrecursive-closure-environment x))))
	((il:recursive-closure? x)
	 `(recursive-closure
	   ,(il:recursive-closure-variables x)
	   ,(map il:externalize-expression (il:recursive-closure-expressions x))
	   ,(il:recursive-closure-index x)
	   ,(il:externalize (il:recursive-closure-environment x))))
	((il:continuation? x)
	 `(continuation ,(il:continuation-id x)
			,(il:externalize (il:continuation-values x))))
	((il:checkpoint? x)
	 `(checkpoint ,(il:externalize (il:checkpoint-continuation x))
		      ,(il:externalize-expression (il:checkpoint-expression x))
		      ,(il:externalize (il:checkpoint-environment x))
		      ,(il:checkpoint-count x)))
	(else (internal-error))))

 (define (il:lookup variable environment)
  (cond ((null? environment) (internal-error))
	((eq? variable (il:binding-variable (first environment)))
	 (il:binding-value (first environment)))
	(else (il:lookup variable (rest environment)))))

 (define (il:walk1 f x)
  ;;\needswork: Not safe for space.
  (cond ((eq? x #t) #t)
	((eq? x #f) #f)
	((null? x) '())
	((dreal? x) (f x))
	((pair? x) (cons (il:walk1 f (car x)) (il:walk1 f (cdr x))))
	((il:binding? x)
	 (make-il:binding (il:binding-variable x)
			  (il:walk1 f (il:binding-value x))))
	((il:nonrecursive-closure? x)
	 (make-il:nonrecursive-closure
	  (il:nonrecursive-closure-expression x)
	  (il:walk1 f (il:nonrecursive-closure-environment x))))
	((il:recursive-closure? x)
	 (make-il:recursive-closure
	  (il:recursive-closure-variables x)
	  (il:recursive-closure-expressions x)
	  (il:recursive-closure-index x)
	  (il:walk1 f (il:recursive-closure-environment x))))
	((il:continuation? x)
	 (if (= (il:continuation-id x) 9)
	     ;;\needswork: This still breaks eq? for continuation9 because if
	     ;;            you il:walk2 then il:walk1 to extract x-prime you
	     ;;            get back x which is equal? but not eq?
	     x
	     (make-il:continuation (il:continuation-id x)
				   (il:continuation-procedure x)
				   (il:walk1 f (il:continuation-values x)))))
	((il:checkpoint? x)
	 (make-il:checkpoint (il:walk1 f (il:checkpoint-continuation x))
			     (il:checkpoint-expression x)
			     (il:walk1 f (il:checkpoint-environment x))
			     (il:checkpoint-count x)))
	(else (internal-error))))

 (define (il:walk2 f x x-prime)
  ;;\needswork: Not safe for space.
  (cond
   ((and (eq? x #t) (eq? x-prime #t)) #t)
   ((and (eq? x #f) (eq? x-prime #f)) #f)
   ((and (null? x) (null? x-prime)) '())
   ((and (dreal? x) (dreal? x-prime)) (f x x-prime))
   ((and (pair? x) (pair? x-prime))
    (cons (il:walk2 f (car x) (car x-prime))
	  (il:walk2 f (cdr x) (cdr x-prime))))
   ((and (il:binding? x)
	 (il:binding? x-prime)
	 (eq? (il:binding-variable x) (il:binding-variable x-prime)))
    (make-il:binding
     (il:binding-variable x)
     (il:walk2 f (il:binding-value x) (il:binding-value x-prime))))
   ((and (il:nonrecursive-closure? x) (il:nonrecursive-closure? x-prime)
	 (eq? (il:nonrecursive-closure-expression x)
	      (il:nonrecursive-closure-expression x-prime)))
    (make-il:nonrecursive-closure
     (il:nonrecursive-closure-expression x)
     (il:walk2 f
	       (il:nonrecursive-closure-environment x)
	       (il:nonrecursive-closure-environment x-prime))))
   ((and (il:recursive-closure? x) (il:recursive-closure? x-prime)
	 (equal? (il:recursive-closure-variables x)
		 (il:recursive-closure-variables x-prime))
	 (equal? (il:recursive-closure-expressions x)
		 (il:recursive-closure-expressions x-prime))
	 (= (il:recursive-closure-index x)
	    (il:recursive-closure-index x-prime)))
    (make-il:recursive-closure
     (il:recursive-closure-variables x)
     (il:recursive-closure-expressions x)
     (il:recursive-closure-index x)
     (il:walk2 f
	       (il:recursive-closure-environment x)
	       (il:recursive-closure-environment x-prime))))
   ((and (il:continuation? x)
	 (il:continuation? x-prime)
	 ;; Can't check eq? on il:continuation-procedure because c and c` are
	 ;; generated from different calls to il:apply/il:eval.
	 (= (il:continuation-id x) (il:continuation-id x-prime)))
    (if (= (il:continuation-id x) 9)
	;;\needswork: This still breaks eq? for continuation9 because if you
	;;            il:walk2 then il:walk1 to extract x-prime you get back x
	;;            which is equal? but not eq?
	x
	(make-il:continuation
	 (il:continuation-id x)
	 ;; Use the one from x, not x-prime.
	 (il:continuation-procedure x)
	 (il:walk2
	  f (il:continuation-values x) (il:continuation-values x-prime)))))
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
   (else (run-time-error "Values don't conform: ~s ~s" x x-prime))))

 (define (il:walk1! f x)
  (cond ((eq? x #t) #f)
	((eq? x #f) #f)
	((null? x) #f)
	((dreal? x) (f x))
	((pair? x) (il:walk1! f (car x)) (il:walk1! f (cdr x)))
	((il:binding? x) (il:walk1! f (il:binding-value x)))
	((il:nonrecursive-closure? x)
	 (il:walk1! f (il:nonrecursive-closure-environment x)))
	((il:recursive-closure? x)
	 (il:walk1 f (il:recursive-closure-environment x)))
	((il:continuation? x) (il:walk1! f (il:continuation-values x)))
	((il:checkpoint? x)
	 (il:walk1! f (il:checkpoint-continuation x))
	 (il:walk1! f (il:checkpoint-environment x)))
	(else (internal-error))))

 (define (il:walk2! f x x-prime)
  (cond
   ((and (eq? x #t) (eq? x-prime #t)) #f)
   ((and (eq? x #f) (eq? x-prime #f)) #f)
   ((and (null? x) (null? x-prime)) #f)
   ((and (dreal? x) (dreal? x-prime)) (f x x-prime))
   ((and (pair? x) (pair? x-prime))
    (il:walk2! f (car x) (car x-prime))
    (il:walk2! f (cdr x) (cdr x-prime)))
   ((and (il:binding? x)
	 (il:binding? x-prime)
	 (eq? (il:binding-variable x) (il:binding-variable x-prime)))
    (il:walk2! f (il:binding-value x) (il:binding-value x-prime)))
   ((and (il:nonrecursive-closure? x)
	 (il:nonrecursive-closure? x-prime)
	 (eq? (il:nonrecursive-closure-expression x)
	      (il:nonrecursive-closure-expression x-prime)))
    (il:walk2! f
	       (il:nonrecursive-closure-environment x)
	       (il:nonrecursive-closure-environment x-prime)))
   ((and (il:recursive-closure? x) (il:recursive-closure? x-prime)
	 (equal? (il:recursive-closure-variables x)
		 (il:recursive-closure-variables x-prime))
	 (equal? (il:recursive-closure-expressions x)
		 (il:recursive-closure-expressions x-prime))
	 (= (il:recursive-closure-index x)
	    (il:recursive-closure-index x-prime)))
    (il:walk2 f
	      (il:recursive-closure-environment x)
	      (il:recursive-closure-environment x-prime)))
   ((and (il:continuation? x)
	 (il:continuation? x-prime)
	 ;; Can't check eq? on il:continuation-procedure because c and c` are
	 ;; generated from different calls to il:apply/il:eval.
	 ;;\needswork
	 (or (and
	      #t
	      (or (= (il:continuation-id x) 9)
		  (= (il:continuation-id x-prime) 9))
	      (or (= (il:continuation-id x) 12)
		  (= (il:continuation-id x-prime) 12)))
	     (= (il:continuation-id x) (il:continuation-id x-prime))))
    (il:walk2! f (il:continuation-values x) (il:continuation-values x-prime)))
   ((and (il:checkpoint? x)
	 (il:checkpoint? x-prime)
	 (eq? (il:checkpoint-expression x) (il:checkpoint-expression x-prime))
	 (= (il:checkpoint-count x) (il:checkpoint-count x-prime)))
    (il:walk2!
     f (il:checkpoint-continuation x) (il:checkpoint-continuation x-prime))
    (il:walk2!
     f (il:checkpoint-environment x) (il:checkpoint-environment x-prime)))
   (else (run-time-error "Values don't conform: ~s ~s" x x-prime))))

 (define (il:count-dummies c x)
  (cond
   ((eq? x #t) 0)
   ((eq? x #f) 0)
   ((null? x) 0)
   ((dreal? x) 0)
   ((pair? x) (+ (il:count-dummies c (car x)) (il:count-dummies c (cdr x))))
   ((il:binding? x) (il:count-dummies c (il:binding-value x)))
   ((il:nonrecursive-closure? x)
    (il:count-dummies c (il:nonrecursive-closure-environment x)))
   ((il:recursive-closure? x)
    (il:count-dummies c (il:recursive-closure-environment x)))
   ((il:continuation? x)
    (+ (if (eq? x c) 1 0) (il:count-dummies c (il:continuation-values x))))
   ((il:checkpoint? x)
    (+ (il:count-dummies c (il:checkpoint-continuation x))
       (il:count-dummies c (il:checkpoint-environment x))))
   (else (internal-error))))

 (define (il:replace-dummy c1 c2 x)
  ;;\needswork: Not safe for space.
  (cond
   ((eq? x #t) #t)
   ((eq? x #f) #f)
   ((null? x) '())
   ((dreal? x) x)
   ((pair? x)
    (cons (il:replace-dummy c1 c2 (car x)) (il:replace-dummy c1 c2 (cdr x))))
   ((il:binding? x)
    (make-il:binding (il:binding-variable x)
		     (il:replace-dummy c1 c2 (il:binding-value x))))
   ((il:nonrecursive-closure? x)
    (make-il:nonrecursive-closure
     (il:nonrecursive-closure-expression x)
     (il:replace-dummy c1 c2 (il:nonrecursive-closure-environment x))))
   ((il:recursive-closure? x)
    (make-il:recursive-closure
     (il:recursive-closure-variables x)
     (il:recursive-closure-expressions x)
     (il:recursive-closure-index x)
     (il:replace-dummy c1 c2 (il:recursive-closure-environment x))))
   ((il:continuation? x)
    (cond ((eq? x c1) c2)
	  ((= (il:continuation-id x) 9) x)
	  (else (make-il:continuation
		 (il:continuation-id x)
		 (il:continuation-procedure x)
		 (il:replace-dummy c1 c2 (il:continuation-values x))))))
   ((il:checkpoint? x)
    (make-il:checkpoint (il:replace-dummy c1 c2 (il:checkpoint-continuation x))
			(il:checkpoint-expression x)
			(il:replace-dummy c1 c2 (il:checkpoint-environment x))
			(il:checkpoint-count x)))
   (else (internal-error))))

 (define (il:equal? x x-prime)
  (or
   (and (eq? x #t) (eq? x-prime #t))
   (and (eq? x #f) (eq? x-prime #f))
   (and (null? x) (null? x-prime))
   (and (dreal? x) (dreal? x-prime) (d= x x-prime))
   (and (pair? x)
	(pair? x-prime)
	(il:equal? (car x) (car x-prime))
	(il:equal? (cdr x) (cdr x-prime)))
   (and (il:binding? x)
	(il:binding? x-prime)
	(eq? (il:binding-variable x) (il:binding-variable x-prime))
	(il:equal? (il:binding-value x) (il:binding-value x-prime)))
   (and (il:nonrecursive-closure? x)
	(il:nonrecursive-closure? x-prime)
	(eq? (il:nonrecursive-closure-expression x)
	     (il:nonrecursive-closure-expression x-prime))
	(il:equal? (il:nonrecursive-closure-environment x)
		   (il:nonrecursive-closure-environment x-prime)))
   (and (il:recursive-closure? x)
	(il:recursive-closure? x-prime)
	(equal? (il:recursive-closure-variables x)
		(il:recursive-closure-variables x-prime))
	(equal? (il:recursive-closure-expressions x)
		(il:recursive-closure-expressions x-prime))
	(= (il:recursive-closure-index x)
	   (il:recursive-closure-index x-prime))
	(il:equal? (il:recursive-closure-environment x)
		   (il:recursive-closure-environment x-prime)))
   (and (il:continuation? x)
	(il:continuation? x-prime)
	;; Can't check eq? on il:continuation-procedure because c and c` are
	;; generated from different calls to il:apply/il:eval.
	;;\needswork
	(or (and
	     #t
	     (or (= (il:continuation-id x) 9)
		 (= (il:continuation-id x-prime) 9))
	     (or (= (il:continuation-id x) 12)
		 (= (il:continuation-id x-prime) 12)))
	    (= (il:continuation-id x) (il:continuation-id x-prime)))
	(il:equal? (il:continuation-values x) (il:continuation-values x-prime)))
   (and (il:checkpoint? x)
	(il:checkpoint? x-prime)
	(eq? (il:checkpoint-expression x) (il:checkpoint-expression x-prime))
	(= (il:checkpoint-count x) (il:checkpoint-count x-prime))
	(il:equal? (il:checkpoint-continuation x)
		   (il:checkpoint-continuation x-prime))
	(il:equal? (il:checkpoint-environment x)
		   (il:checkpoint-environment x-prime)))))

 (define (il:closure? thing)
  (or (il:nonrecursive-closure? thing) (il:recursive-closure? thing)))

 (define (il:make-continuation id procedure . values)
  (make-il:continuation id procedure values))

 (define (il:call-continuation continuation value count limit path)
  (apply (il:continuation-procedure continuation)
	 value
	 count
	 limit
	 path
	 (il:continuation-values continuation)))

 (define (il:destructure parameter value)
  ;; removed lambda and letrec parameters
  (cond ((il:constant-expression? parameter)
	 ;; This equal? is OK because a constant expression can't contain a
	 ;; checkpoint or continuation.
	 (unless (equal? (il:constant-expression-value parameter) value)
	  (run-time-error "Argument is not an equivalent value for ~s: ~s"
			  (il:constant-expression-value parameter)
			  value))
	 '())
	((il:variable-access-expression? parameter)
	 (list (make-il:binding
		(il:variable-access-expression-variable parameter) value)))
	((il:binary-expression? parameter)
	 (append (il:destructure
		  (il:binary-expression-expression1 parameter) (car value))
		 (il:destructure
		  (il:binary-expression-expression2 parameter) (cdr value))))
	(else (internal-error))))

 (define (il:apply continuation value1 value2 count limit path)
  (cond
   ((il:nonrecursive-closure? value1)
    (il:eval continuation
	     (il:lambda-expression-expression
	      (il:nonrecursive-closure-expression value1))
	     ;;\needswork: Not safe for space.
	     (append (il:destructure
		      (il:lambda-expression-parameter
		       (il:nonrecursive-closure-expression value1))
		      value2)
		     (il:nonrecursive-closure-environment value1))
	     count
	     limit
	     path))
   ((il:recursive-closure? value1)
    (il:eval
     continuation
     (il:lambda-expression-expression
      (list-ref (il:recursive-closure-expressions value1)
		(il:recursive-closure-index value1)))
     ;;\needswork: Not safe for space.
     (append (il:destructure
	      (il:lambda-expression-parameter
	       (list-ref (il:recursive-closure-expressions value1)
			 (il:recursive-closure-index value1)))
	      value2)
	     (map-indexed (lambda (variable index)
			   (make-il:binding
			    variable
			    (make-il:recursive-closure
			     (il:recursive-closure-variables value1)
			     (il:recursive-closure-expressions value1)
			     index
			     (il:recursive-closure-environment value1))))
			  (il:recursive-closure-variables value1))
	     (il:recursive-closure-environment value1))
     count
     limit
     path))
   (else (run-time-error "Not a closure: ~s" value1))))

 (define (il:if-procedure
	  continuation value1 value2 value3 count limit path)
  (il:call-continuation
   continuation (if value1 value2 value3) count limit path))

 (define (il:real value) value)

 (define (il:write-real value) (write (primal* value)) (newline) value)

 (define (forward-mode
	  continuation map-independent map-dependent f x x-perturbation)
  ;;\needswork: What happens if this checkpoints in between the increment and
  ;;            decrement of *e* and is resumed out of order? What happens if
  ;;            the checkpoint is resumed multiple times or is not resumed?
  (set! *e* (+ *e* 1))
  (f (il:make-continuation
      0
      (lambda (y-forward count limit path)
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
	count
	limit
	path)))
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
		       y-sensitivity)
  ;;\needswork: What happens if this checkpoints in between the increment and
  ;;            decrement of *e* and is resumed out of order? What happens if
  ;;            the checkpoint is resumed multiple times or is not resumed?
  (set! *e* (+ *e* 1))
  (let ((x-reverse (map-independent tapify x)))
   (f (il:make-continuation
       1
       (lambda (y-reverse count limit path x-reverse y-sensitivity)
	(for-each-dependent1!
	 (lambda (y-reverse)
	  (when (and (tape? y-reverse) (not (<_e (tape-epsilon y-reverse) *e*)))
	   (determine-fanout! y-reverse)))
	 y-reverse)
	(for-each-dependent1!
	 (lambda (y-reverse)
	  (when (and (tape? y-reverse) (not (<_e (tape-epsilon y-reverse) *e*)))
	   (initialize-sensitivity! y-reverse)))
	 y-reverse)
	(for-each-dependent1!
	 (lambda (y-reverse)
	  (when (and (tape? y-reverse) (not (<_e (tape-epsilon y-reverse) *e*)))
	   (determine-fanout! y-reverse)))
	 y-reverse)
	(for-each-dependent2!
	 (lambda (y-reverse y-sensitivity)
	  (when (and (tape? y-reverse) (not (<_e (tape-epsilon y-reverse) *e*)))
	   (reverse-phase! y-sensitivity y-reverse)))
	 y-reverse
	 y-sensitivity)
	(let ((x-sensitivity (map-independent tape-sensitivity x-reverse)))
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
	   x-sensitivity)
	  count
	  limit
	  path)))
       x-reverse
       y-sensitivity)
      x-reverse)))

 (define (reverse-mode-for-base-case-of-checkpoint-*j continuation
						      map-independent
						      map-dependent
						      for-each-dependent1!
						      for-each-dependent2!
						      f
						      x
						      y-sensitivity)
  ;; This is a special version of reverse-mode that handles the case where f
  ;; checkpoints.
  ;;\needswork: What happens if this checkpoints in between the increment and
  ;;            decrement of *e* and is resumed out of order? What happens if
  ;;            the checkpoint is resumed multiple times or is not resumed?
  (set! *e* (+ *e* 1))
  (let ((x-reverse (map-independent tapify x)))
   (let* ((continuation
	   (il:make-continuation
	    18
	    (lambda (y-reverse count limit path x-reverse y-sensitivity)
	     (for-each-dependent1!
	      (lambda (y-reverse)
	       (when (and (tape? y-reverse)
			  (not (<_e (tape-epsilon y-reverse) *e*)))
		(determine-fanout! y-reverse)))
	      y-reverse)
	     (when *debugging?*
	      (display "after determing-fanout!")
	      (newline)
	      (pretty-print (il:externalize y-reverse)))
	     (for-each-dependent1!
	      (lambda (y-reverse)
	       (when (and (tape? y-reverse)
			  (not (<_e (tape-epsilon y-reverse) *e*)))
		(initialize-sensitivity! y-reverse)))
	      y-reverse)
	     (when *debugging?*
	      (display "after initialize-sensitivity!")
	      (newline)
	      (pretty-print (il:externalize y-reverse)))
	     (for-each-dependent1!
	      (lambda (y-reverse)
	       (when (and (tape? y-reverse)
			  (not (<_e (tape-epsilon y-reverse) *e*)))
		(determine-fanout! y-reverse)))
	      y-reverse)
	     (when *debugging?*
	      (display "after determing-fanout!")
	      (newline)
	      (pretty-print (il:externalize y-reverse)))
	     (for-each-dependent2!
	      (lambda (y-reverse y-sensitivity)
	       (when (and (tape? y-reverse)
			  (not (<_e (tape-epsilon y-reverse) *e*)))
		(reverse-phase! y-sensitivity y-reverse)))
	      y-reverse
	      y-sensitivity)
	     (when *debugging?*
	      (display "after reverse-phase!")
	      (newline)
	      (pretty-print (il:externalize y-reverse)))
	     (let ((x-sensitivity (map-independent tape-sensitivity x-reverse)))
	      (set! *e* (- *e* 1))
	      (il:call-continuation
	       continuation
	       (list
		(map-dependent
		 (lambda (y-reverse)
		  (if (or (not (tape? y-reverse))
			  (<_e (tape-epsilon y-reverse) *e*))
		      y-reverse
		      (tape-primal y-reverse)))
		 y-reverse)
		x-sensitivity)
	       count
	       limit
	       path)))
	    x-reverse
	    y-sensitivity))
	  (checkpoint (f continuation x-reverse)))
    ;; I think count, limit, and path are never used.
    (il:call-continuation continuation checkpoint 'count 'limit 'path)
    (internal-error
     "reverse-mode-for-base-case-of-checkpoint-*j continuation checkpointed"))))

 (define (il:j* continuation value1 value2 value3 count limit path)
  (forward-mode continuation
		il:walk2
		il:walk1
		(lambda (continuation x)
		 (il:apply continuation value1 x count limit path))
		value2
		value3))

 (define (il:*j continuation value1 value2 value3 count limit path)
  (reverse-mode continuation
		il:walk1
		il:walk1
		il:walk1!
		il:walk2!
		(lambda (continuation x)
		 (il:apply continuation value1 x count limit path))
		value2
		value3))

 (define (il:base-case-of-checkpoint-*j
	  continuation value1 value2 value3 count limit path)
  (reverse-mode-for-base-case-of-checkpoint-*j
   continuation
   il:walk1
   il:walk1
   il:walk1!
   il:walk2!
   (lambda (continuation x)
    (il:apply continuation value1 x count limit path))
   value2
   value3))

 (define (il:eval continuation expression environment count limit path)
  ;; Every entry into il:eval increments count exactly once. So if you call
  ;; il:eval with count=0 and it doesn't checkpoint, continuation is called with
  ;; count=n being the total number of calls to (entries into) il:eval during
  ;; the evaluation. If you evaluate the same expression in the same environment
  ;; with count=0 and limit>=n then it will not checkpoint. But if called with
  ;; count=0 and limit=(0<=i<n) then it will checkpoint upon entry to the ith
  ;; call. The entries are numbered 0,...,i.
  (when *debugging?*
   (display "il:eval, count=")
   (write count)
   (display ", limit=")
   (write limit)
   (display ", path=")
   (write path)
   (newline)
   (pretty-print (il:externalize-expression expression)))
  (when (> count limit) (internal-error "(> count limit)" count limit))
  (if (= count limit)
      (make-il:checkpoint continuation expression environment count)
      (cond
       ((il:constant-expression? expression)
	(il:call-continuation continuation
			      (il:constant-expression-value expression)
			      (+ count 1)
			      limit
			      path))
       ((il:variable-access-expression? expression)
	(il:call-continuation
	 continuation
	 (il:lookup (il:variable-access-expression-variable expression)
		    environment)
	 (+ count 1)
	 limit
	 path))
       ((il:lambda-expression? expression)
	(il:call-continuation
	 continuation
	 ;;\needswork: Not safe for space.
	 (make-il:nonrecursive-closure expression environment)
	 (+ count 1)
	 limit
	 path))
       ((il:unary-expression? expression)
	(il:eval
	 (il:make-continuation
	  2
	  (lambda (value count limit path continuation)
	   ((il:unary-expression-procedure expression)
	    continuation value count limit path))
	  continuation)
	 (il:unary-expression-expression expression)
	 environment
	 (+ count 1)
	 limit
	 path))
       ((il:binary-expression? expression)
	(il:eval
	 (il:make-continuation
	  3
	  (lambda (value1 count limit path continuation environment)
	   (il:eval
	    (il:make-continuation
	     4
	     (lambda (value2 count limit path continuation value1)
	      ((il:binary-expression-procedure expression)
	       continuation value1 value2 count limit path))
	     continuation
	     value1)
	    (il:binary-expression-expression2 expression)
	    environment
	    count
	    limit
	    path))
	  continuation
	  environment)
	 (il:binary-expression-expression1 expression)
	 environment
	 (+ count 1)
	 limit
	 path))
       ((il:ternary-expression? expression)
	(il:eval
	 (il:make-continuation
	  5
	  (lambda (value1 count limit path continuation environment)
	   (il:eval
	    (il:make-continuation
	     6
	     (lambda (value2 count limit path continuation environment value1)
	      (il:eval
	       (il:make-continuation
		7
		(lambda (value3 count limit path continuation value1 value2)
		 ((il:ternary-expression-procedure expression)
		  continuation
		  value1
		  value2
		  value3
		  count
		  limit
		  path))
		continuation
		value1
		value2)
	       (il:ternary-expression-expression3 expression)
	       environment
	       count
	       limit
	       path))
	     continuation
	     environment
	     value1)
	    (il:ternary-expression-expression2 expression)
	    environment
	    count
	    limit
	    path))
	  continuation
	  environment)
	 (il:ternary-expression-expression1 expression)
	 environment
	 (+ count 1)
	 limit
	 path))
       ((il:letrec-expression? expression)
	(il:eval continuation
		 (il:letrec-expression-expression expression)
		 ;;\needswork: Not safe for space.
		 (append
		  (map-indexed (lambda (variable index)
				(make-il:binding
				 variable
				 (make-il:recursive-closure
				  (il:letrec-expression-variables expression)
				  (il:letrec-expression-expressions expression)
				  index
				  environment)))
			       (il:letrec-expression-variables expression))
		  environment)
		 (+ count 1)
		 limit
		 path))
       (else (internal-error)))))

 (define (il:checkpoint-*j continuation value1 value2 value3 count limit path)
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
  (when *debugging?*
   (display "entering il:checkpoint-*j, path=")
   (write path)
   (newline)
   (display "f=")
   (pretty-print (il:externalize value1))
   (display "x=")
   (pretty-print (il:externalize value2))
   (display "y`=")
   (pretty-print (il:externalize value3))
   (display "count=")
   (write count)
   (display ", limit=")
   (write limit)
   (newline)
   (display "starting step 1. (y,2n)=primops(f,x), path=")
   (write (append path '(1)))
   (newline))
  (let* ((continuation4
	  (il:make-continuation
	   8
	   (lambda (value4 count4 limit4 path4
			   continuation value1 value2 value3)
	    ;; path4 is ignored
	    (when *debugging?*
	     (display "finished step 1, path=")
	     (write (append path '(1)))
	     (newline)
	     (display "y=")
	     (pretty-print (il:externalize value4))
	     (display "steps=")
	     (write (- count4 count))
	     (display ", half=")
	     (write (quotient (- count4 count) 2))
	     (display ", count for second half=")
	     (write (+ count (quotient (- count4 count) 2)))
	     (display ", limit for second half=")
	     (write limit)
	     (newline))
	    ;; count4 must be greater than count because it is incremented
	    ;; before any path to calling this continuation to il:apply.
	    (unless (> count4 count)
	     (internal-error "(not (> count4 count))" count4 count))
	    (cond
	     ((<= (- count4 count) *base-case-duration*)
	      (when *debugging?*
	       (display "base case, path=")
	       (write (append path '(0)))
	       (newline))
	      ;;\needswork: This continuation can be eta converted when we
	      ;;            remove the debugging printout.
	      (il:base-case-of-checkpoint-*j
	       (il:make-continuation
		15
		(lambda (value count limit path15 continuation)
		 ;; path15 is ignored
		 (when *debugging?*
		  (display "finished base case, path=")
		  (write (append path '(0)))
		  (newline)
		  (display "y=")
		  (pretty-print (il:externalize (first value)))
		  (display "x`=")
		  (pretty-print (il:externalize (second value))))
		 (il:call-continuation continuation value count limit path)
		 (internal-error "base case continuation checkpointed"))
		continuation)
	       value1 value2 value3 count limit (append path '(0)))
	      (internal-error "base case checkpointed"))
	     (else
	      ;; 2. c=checkpoint(f,x,n)
	      ;; f is value1
	      ;; x is value2
	      ;; n is (quotient (- count4 count) 2)
	      ;; c is checkpoint5
	      (when *debugging?*
	       (display "inductive case, path=")
	       (write (append path '(2)))
	       (newline)
	       (display "starting step 2. c=checkpoint(f,x,n), path=")
	       (write (append path '(2)))
	       (newline))
	      (let* ((continuation9
		      ;; This continuation will be spliced out and never called.
		      ;; It won't be called with the checkpoint computation but
		      ;; would have been called upon resume.
		      (il:make-continuation
		       9
		       (lambda (value count limit path)
			(internal-error "Dummy continuation 9"))))
		     (checkpoint5
		      (il:apply
		       continuation9
		       value1
		       value2
		       ;; These are the count and limit for the first half of
		       ;; the computation. If
		       ;; (zero? (quotient (- count4 count) 2))
		       ;; then the evaluation could checkpoint right at the
		       ;; start without making any progress. But that can't
		       ;; happen.
		       count
		       (+ count (quotient (- count4 count) 2))
		       (append path '(2)))))
	       (when *debugging?*
		(display "finished step 2, path=")
		(write (append path '(2)))
		(newline)
		(display "c=")
		(pretty-print (il:externalize checkpoint5))
		(display
		 "starting step 3. (y,c`)=*j(\\c.resume(c),c,y`), path=")
		(write (append path '(3)))
		(newline)
		(display "backing up count by 2")
		(newline))
	       ;; 3. (y,c`)=*j(\c.resume(c),c,y`)
	       ;; c is checkpoint5
	       ;; y` is value3
	       ;; y is (first value6)
	       ;; c` is (second value6)
	       (il:checkpoint-*j
		;; This continuation will become continuation10. It would
		;; normally not be called except that it is spliced in for the
		;; dummy continuation 9.
		(il:make-continuation
		 10
		 ;; This closes over value4 and checkpoint5 only for consistency
		 ;; checking.
		 (lambda (value6 count6 limit6 path6
				 continuation value1 value2 value4 checkpoint5)
		  ;; envirornment6, count6, limit6, and path6m that at the end
		  ;; of step 3, are ignored.
		  (when *debugging?*
		   (display "finished step 3, path=")
		   (write (append path '(3)))
		   (newline)
		   (display "y=")
		   (pretty-print (il:externalize (first value6)))
		   (display "c`=")
		   (pretty-print (il:externalize (second value6)))
		   (display
		    "starting step 4. (c,x`)=*j(\\x.checkpoint(f,x,n),x,c`), path=")
		   (write (append path '(4)))
		   (newline)
		   (display "backing up count by 3")
		   (newline))
		  ;; 4. (c,x`)=*j(\x.checkpoint(f,x,n),x,c`)
		  ;; f is value1
		  ;; x is value2
		  ;; c` is (second value6)
		  ;; c is (first value7)
		  ;; x` is (second value7)
		  (unless (il:equal? value4 (first value6))
		   (internal-error "(not (il:equal? value4 (first value6)))"
				   value4
				   (first value6)))
		  (il:checkpoint-*j
		   (il:make-continuation
		    11
		    ;; This closes over checkpoint5 only for consistency
		    ;; checking.
		    (lambda (value7 count7 limit7 path7
				    continuation checkpoint5 value6)
		     ;; count7, limit7, and path7, that at the end of step 4,
		     ;; are ignored, except for consistency checking.
		     (when *debugging?*
		      (display "finished step 4, path=")
		      (write (append path '(4)))
		      (newline))
		     (unless (= count7 (+ count (quotient (- count4 count) 2)))
		      (internal-error
		       "(not (= count7 (+ count (quotient (- count4 count) 2))))"
		       count7
		       (+ count (quotient (- count4 count) 2))))
		     (unless (il:equal? checkpoint5 (first value7))
		      (internal-error
		       "(not (il:equal? checkpoint5 (first value7)))"
		       checkpoint5
		       (first value7)))
		     (when *debugging?*
		      (display "leaving il:checkpoint-*j, path=")
		      (write path)
		      (newline)
		      (display "c=")
		      (pretty-print (il:externalize (first value7)))
		      (display "x`=")
		      (pretty-print (il:externalize (second value7)))
		      (display "count=")
		      (write count4)
		      (display ", limit=")
		      (write limit4)
		      (newline))
		     (il:call-continuation
		      continuation
		      (list (first value6) (second value7))
		      ;; This fakes the count and limit to be the same as
		      ;; computed for primops, as if the entire computation
		      ;; were done exactly once.
		      count4
		      limit4
		      path)
		     (internal-error "step 4 continuation checkpointed"))
		    continuation
		    checkpoint5
		    value6)
		   ;; This is a closure that behaves like \x.checkpoint(f,x,n).
		   (make-il:nonrecursive-closure
		    (make-il:lambda-expression
		     (make-il:variable-access-expression 'x)
		     (make-il:binary-expression
		      (lambda (continuation8 value8 value9 count8 limit8 path8)
		       ;; path8 is ignored
		       ;; continuation8 should be continuation 11, the value of
		       ;; the above il:make-continuation passed to
		       ;; il:checkpoint-*j for step 4.
		       (when *debugging?*
			(display "starting checkpoint(f,x,n), path=")
			(write path8)
			(newline))
		       (unless (= count8 count)
			(internal-error "(not (= count8 count))" count8 count))
		       ;; Because the call to checkpoint(f,x,n) returns and
		       ;; never calls its continuation, we have to call the
		       ;; continuation of step 4.
		       (let ((checkpoint27
			      ;; Since this is a call to checkpoint(f,x,n), it
			      ;; will always checkpoint. That means that it
			      ;; returns a checkpoint and never calls its
			      ;; continuation. The returned checkpoint should
			      ;; never be resumed. So the dummy continuation 12
			      ;; should never be called.
			      (il:apply
			       (il:make-continuation
				12
				(lambda (value count limit path)
				 (internal-error "Dummy continuation 12")))
			       value8 value9 count8 limit8 path8)))
			(when *debugging?*
			 (when (= (il:continuation-id continuation8) 9)
			  (display
			   "k=k9, returning instead of calling continuation")
			  (newline)))
			(when *debugging?*
			 (when (= (il:continuation-id continuation8) 12)
			  (display
			   "k=k12, returning instead of calling continuation")
			  (newline)))
			(if (or (= (il:continuation-id continuation8) 9)
				(= (il:continuation-id continuation8) 12))
			    checkpoint27
			    ;;\needswork: We don't give an error if this
			    ;;            checkpoints.
			    (il:call-continuation
			     continuation8
			     checkpoint27
			     ;; These are the count and limit at the end of
			     ;; checkpoint(f,x,n). Since this checkpoints,
			     ;; count9=limit9.
			     ;; We fake this as the "count for second half" or
			     ;; equivalently the "limit for the first half".
			     ;; These should ultimately be passed to count7 and
			     ;; limit7 which are ignored. We can't pass dummies
			     ;; because the call to \x.checkpoint(f,x,n) is
			     ;; wrapped in a call to il:checkpoint-*j which
			     ;; first does step 1 and this computes steps at
			     ;; the beginning.
			     (+ count (quotient (- count4 count) 2))
			     (+ count (quotient (- count4 count) 2))
			     path8))))
		      (make-il:variable-access-expression 'f)
		      (make-il:variable-access-expression 'x)))
		    (list (make-il:binding 'f value1)))
		   value2
		   (second value6)
		   ;; These are the count and limit for the first half of the
		   ;; computation. If (zero? (quotient (- count4 count) 2))
		   ;; then the evaluation could checkpoint right at the start
		   ;; without making any progress. But that can't happen.
		   ;; The -3 is a fudge for the binary expression and the
		   ;; variable access expressions f and x.
		   (- count 3)
		   (+ count (quotient (- count4 count) 2))
		   (append path '(4)))
		  (internal-error "step 4 checkpointed"))
		 continuation
		 value1
		 value2
		 value4
		 checkpoint5)
		;; This is a closure that behaves like \c.resume(c).
		(make-il:nonrecursive-closure
		 (make-il:lambda-expression
		  (make-il:variable-access-expression 'c)
		  (make-il:unary-expression
		   ;;\needswork: Should this close over continuation9?
		   (lambda (continuation10 value10 count10 limit10 path10)
		    ;; path10 is ignored
		    ;;\needswork: Could eliminate (il:checkpoint-count value10).
		    (when *debugging?*
		     (display "starting resume(c), path=")
		     (write path10)
		     (newline))
		    (unless (= count10 (il:checkpoint-count value10))
		     (internal-error
		      "(not (= count10 (il:checkpoint-count value10)))"
		      count10
		      (il:checkpoint-count value10)))
		    (unless (= count10 (+ count (quotient (- count4 count) 2)))
		     (internal-error
		      "(not (= count10 (+ count (quotient (- count4 count) 2))))"
		      count10
		      (+ count (quotient (- count4 count) 2))))
		    (unless (= (il:checkpoint-count value10)
			       (+ count (quotient (- count4 count) 2)))
		     (internal-error
		      "(not (= (il:checkpoint-count value10) (+ count (quotient (- count4 count) 2))))"
		      (il:checkpoint-count value10)
		      (+ count (quotient (- count4 count) 2))))
		    ;;\needswork: I don't know how there can be zero dummies.
		    ;; It might be that there can be more than one dummy due
		    ;; to not-safe-for-space structure sharing that is broken.
		    (when #f
		     (unless (<= (il:count-dummies
				  continuation9
				  (il:checkpoint-continuation value10))
				 1)
		      (internal-error "More than one dummy"
				      (il:count-dummies
				       continuation9
				       (il:checkpoint-continuation value10)))))
		    (il:eval (il:replace-dummy
			      continuation9
			      continuation10
			      (il:checkpoint-continuation value10))
			     (il:checkpoint-expression value10)
			     (il:checkpoint-environment value10)
			     ;; These are the count and limit for the second
			     ;; half of the computation.
			     (il:checkpoint-count value10)
			     limit10
			     path10)
		    ;;\needswork: I'm not sure whether this is OK or not.
		    ;;(internal-error "resume(c) checkpointed")
		    )
		   (make-il:variable-access-expression 'c)))
		 '())
		checkpoint5
		value3
		;; These are the count and limit for the second half of the
		;; computation. The -2 is a fudge for the unary expression and
		;; the variable access expression c.
		(+ count (quotient (- count4 count) 2) -2)
		limit
		(append path '(3)))
	       (internal-error "step 3 checkpointed")))))
	   continuation
	   value1
	   value2
	   value3))
	 (checkpoint4
	  ;; These are the count and limit for the whole computation.
	  (il:apply
	   continuation4 value1 value2 count limit (append path '(1)))))
   ;; When step 1 is called from step 3 which is called from step 4, the
   ;; call to primops checkpoints and doesn't call its continuation. So we have
   ;; to call it here.
   (il:call-continuation continuation4 checkpoint4 limit limit path)
   (internal-error "step 1 continuation checkpointed")))

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

 (define (duplicatesq? xs)
  (and (not (null? xs))
       (or (memq (first xs) (rest xs)) (duplicatesq? (rest xs)))))

 (define (find-if p l)
  (let loop ((l l))
   (cond ((null? l) #f)
	 ((p (first l)) (first l))
	 (else (loop (rest l))))))

 (define (unionq x y)
  (let loop ((l x) (c '()))
   (cond ((null? l) (append (reverse c) y))
	 ((memq (first l) y) (loop (rest l) c))
	 (else (loop (rest l) (cons (first l) c))))))

 (define (set-differenceq x y)
  (let loop ((l x) (c '()))
   (cond ((null? l) (reverse c))
	 ((memq (first l) y) (loop (rest l) c))
	 (else (loop (rest l) (cons (first l) c))))))

 (define (map-reduce g i f l . ls)
  (if (null? l)
      i
      (apply map-reduce
	     g
	     (g i (apply f (car l) (map car ls)))
	     f
	     (cdr l)
	     (map cdr ls))))

 (define (map-indexed f l)
  (let loop ((i 0) (l l) (c '()))
   (if (null? l)
       (reverse c)
       (loop (+ i 1) (rest l) (cons (f (first l) i) c)))))

 (define (internal-error . message) (error #f "Internal error" message))

 (define (compile-time-error message . arguments)
  (error #f (apply format message arguments)))

 (define (run-time-error message . arguments)
  (error #f (apply format message arguments)))

 (define (has-extension? pathname)
  (let loop ((l (reverse (string->list pathname))))
   (and (not (null? l))
	(not (char=? (first l) #\/))
	(or (char=? (first l) #\.) (loop (rest l))))))

 (define (default-extension pathname extension)
  (if (has-extension? pathname)
      pathname
      (string-append pathname "." extension)))

 (define *include-path* '())

 (define (search-include-path-without-extension pathname)
  (cond ((file-exists? pathname) pathname)
	((and (>= (string-length pathname) 1)
	      (char=? (string-ref pathname 0) #\/))
	 (compile-time-error "Cannot find: ~a" pathname))
	(else (let loop ((include-path *include-path*))
	       (cond ((null? include-path)
		      (compile-time-error "Cannot find: ~a" pathname))
		     ((file-exists?
		       (string-append (first include-path) "/" pathname))
		      (string-append (first include-path) "/" pathname))
		     (else (loop (rest include-path))))))))

 (define (search-include-path pathname)
  (search-include-path-without-extension (default-extension pathname "vlad")))

 (define (read-source pathname)
  (let ((pathname (default-extension pathname "vlad")))
   (unless (file-exists? pathname)
    (compile-time-error "Cannot find: ~a" pathname))
   (call-with-input-file pathname
    (lambda (input-port)
     (let loop ((es '()))
      (let ((e (read input-port)))
       (cond
	((eof-object? e) (reverse es))
	((and (list? e)
	      (= (length e) 2)
	      (eq? (first e) 'include)
	      (string? (second e)))
	 (loop
	  (append (reverse (read-source (search-include-path (second e)))) es)))
	(else (loop (cons e es))))))))))

 (define (concrete-variable? x)
  ;; removed alpha anf backpropagator perturbation forward sensitivity reverse
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
  (for-each
   (lambda (d)
    (unless (definition? d) (compile-time-error "Invalid definition: ~s" d)))
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
  (cond
   ((boolean? p) (syntax-check-parameter! `',p))
   ((real? p) (syntax-check-parameter! `',p))
   ((concrete-variable? p)
    (unless (concrete-variable? p)
     (compile-time-error "Invalid parameter: ~s" p))
    #f)
   ((and (list? p) (not (null? p)))
    (case (first p)
     ((quote) (unless (and (= (length p) 2) (value? (second p)))
	       (compile-time-error "Invalid parameter: ~s" p))
      #f)
     ((cons)
      (unless (= (length p) 3) (compile-time-error "Invalid parameter: ~s" p))
      (syntax-check-parameter! (second p))
      (syntax-check-parameter! (third p)))
     ((cons*) (syntax-check-parameter! (macro-expand p)))
     ((list) (syntax-check-parameter! (macro-expand p)))
     (else (compile-time-error "Invalid parameter: ~s" p))))
   (else (compile-time-error "Invalid parameter: ~s" p))))

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
	 (compile-time-error "Invalid expression: ~s" e))
	(case (length (second e))
	 ((0) `(lambda ((cons* ,@(second e)))
		,(macro-expand-body (rest (rest e)))))
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
		    (else (compile-time-error "Invalid expression: ~s" e))))
       ((let*)
	(unless (and (>= (length e) 3)
		     (list? (second e))
		     (every (lambda (b) (and (list? b) (= (length b) 2)))
			    (second e))
		     (valid-body? (rest (rest e))))
	 (compile-time-error "Invalid expression: ~s" e))
	(case (length (second e))
	 ((0) (macro-expand-body (rest (rest e))))
	 ((1) `(let ,(second e) ,@(rest (rest e))))
	 (else `(let (,(first (second e)))
		 (let* ,(rest (second e)) ,@(rest (rest e)))))))
       ((if)
	(unless (= (length e) 4)
	 (compile-time-error "Invalid expression: ~s" e))
	;; needs work: To ensure that you don't shadow if-procedure.
	`((if-procedure
	   ,(second e) (lambda () ,(third e)) (lambda () ,(fourth e)))))
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
	 (compile-time-error "Invalid expression: ~s" e))
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

 (define (parameter-variables p)
  ;; removed lambda and letrec parameters
  (cond ((il:constant-expression? p) '())
	((il:variable-access-expression? p)
	 (list (il:variable-access-expression-variable p)))
	((il:binary-expression? p)
	 (unionq (free-variables (il:binary-expression-expression1 p))
		 (free-variables (il:binary-expression-expression2 p))))
	(else (internal-error))))

 (define (free-variables e)
  (cond ((il:constant-expression? e) '())
	((il:variable-access-expression? e)
	 (list (il:variable-access-expression-variable e)))
	((il:lambda-expression? e)
	 (set-differenceq (free-variables (il:lambda-expression-expression e))
			  (free-variables (il:lambda-expression-parameter e))))
	((il:unary-expression? e)
	 (free-variables (il:unary-expression-expression e)))
	((il:binary-expression? e)
	 (unionq (free-variables (il:binary-expression-expression1 e))
		 (free-variables (il:binary-expression-expression2 e))))
	((il:letrec-expression? e)
	 (set-differenceq
	  (unionq (free-variables (il:letrec-expression-expression e))
		  (map-reduce unionq
			      '()
			      free-variables
			      (il:letrec-expression-expressions e)))
	  (il:letrec-expression-variables e)))
	(else (internal-error))))

 (define (syntax-check-expression! e)
  (let loop ((e e) (xs (map il:binding-variable *top-level-environment*)))
   (cond
    ((boolean? e) (loop `',e xs))
    ((real? e) (loop `',e xs))
    ((concrete-variable? e)
     (unless (memq e xs) (compile-time-error "Unbound variable: ~s" e))
     #f)
    ((and (list? e) (not (null? e)))
     (case (first e)
      ((quote)
       (unless (and (= (length e) 2) (value? (second e)))
	(compile-time-error "Invalid expression: ~s" e))
       #f)
      ((lambda)
       (unless (and (>= (length e) 3)
		    (list? (second e))
		    (valid-body? (rest (rest e))))
	(compile-time-error "Invalid expression: ~s" e))
       (case (length (second e))
	((0) (loop (macro-expand e) xs))
	((1)
	 (syntax-check-parameter! (first (second e)))
	 (let ((xs0 (parameter-variables
		     (internalize-expression (first (second e))))))
	  (when (duplicatesq? xs0)
	   (compile-time-error "Duplicate variables: ~s" e))
	  (loop (macro-expand-body (rest (rest e))) (append xs0 xs))))
	(else (loop (macro-expand e) xs))))
      ((letrec)
       (unless (and (>= (length e) 3)
		    (list? (second e))
		    (every
		     (lambda (b)
		      (and (list? b)
			   (= (length b) 2) (concrete-variable? (first b))))
		     (second e)))
	(compile-time-error "Invalid expression: ~s" e))
       (let ((xs0 (map first (second e))))
	(when (duplicatesq? xs0)
	 (compile-time-error "Duplicate variables: ~s" e))
	(for-each
	 (lambda (b)
	  (let ((e1 (macro-expand (second b))))
	   (unless (and (list? e1) (= (length e1) 3) (eq? (first e1) 'lambda))
	    (compile-time-error "Invalid expression: ~s" e))
	   (loop e1 (append xs0 xs))))
	 (second e))
	(loop (macro-expand-body (rest (rest e))) (append xs0 xs))))
      ((let) (loop (macro-expand e) xs))
      ((let*) (loop (macro-expand e) xs))
      ((if) (loop (macro-expand e) xs))
      ((cons)
       (unless (= (length e) 3) (compile-time-error "Invalid expression: ~s" e))
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
    (else (compile-time-error "Invalid expression: ~s" e)))))

 (define (il:cons continuation value1 value2 count limit path)
  (il:call-continuation continuation (cons value1 value2) count limit path))

 (define (new-cons-expression e1 e2) (make-il:binary-expression il:cons e1 e2))

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
      (make-il:letrec-expression
       (map first (second e))
       (map (lambda (b) (internalize-expression (macro-expand (second b))))
	    (second e))
       (internalize-expression (macro-expand-body (rest (rest e))))))
     ((let) (internalize-expression (macro-expand e)))
     ((let*) (internalize-expression (macro-expand e)))
     ((if) (internalize-expression (macro-expand e)))
     ((cons) (new-cons-expression (internalize-expression (second e))
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
   (else (internal-error))))

 (define (concrete->abstract e)
  (let ((e (internalize-expression e)))
   (list e
	 (map (lambda (x)
	       (find-if (lambda (b) (eq? x (il:binding-variable b)))
			*top-level-environment*))
	      (free-variables e)))))

 (define (make-unary-primitive variable f)
  ;;\needswork: type check
  (make-il:binding
   variable
   (make-il:nonrecursive-closure
    (make-il:lambda-expression
     (make-il:variable-access-expression 'x)
     (make-il:unary-expression
      (lambda (continuation value count limit path)
       (il:call-continuation continuation (f value) count limit path))
      (make-il:variable-access-expression 'x)))
    '())))

 (define (make-binary-primitive variable f)
  ;;\needswork: type check
  (make-il:binding
   variable
   (make-il:nonrecursive-closure
    (make-il:lambda-expression
     (new-cons-expression (make-il:variable-access-expression 'x1)
			  (make-il:variable-access-expression 'x2))
     (make-il:binary-expression
      (lambda (continuation value1 value2 count limit path)
       (il:call-continuation continuation (f value1 value2) count limit path))
      (make-il:variable-access-expression 'x1)
      (make-il:variable-access-expression 'x2)))
    '())))

 (define (make-ternary-primitive variable f)
  ;;\needswork: type check
  (make-il:binding
   variable
   (make-il:nonrecursive-closure
    (make-il:lambda-expression
     (new-cons-expression
      (make-il:variable-access-expression 'x1)
      (new-cons-expression (make-il:variable-access-expression 'x2)
			   (make-il:variable-access-expression 'x3)))
     (make-il:ternary-expression
      f
      (make-il:variable-access-expression 'x1)
      (make-il:variable-access-expression 'x2)
      (make-il:variable-access-expression 'x3)))
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
	(make-ternary-primitive 'if-procedure il:if-procedure)
	(make-unary-primitive 'real il:real)
	(make-unary-primitive 'write-real il:write-real)
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
	  (il:eval (il:make-continuation
		    13
		    (lambda (value count limit path)
		     ;; count, limit, and path are ignored
		     (write value)
		     (newline)
		     (loop (rest es) ds)))
		   e
		   bs
		   0
		   (/ 1.0 0.0)
		   '())
	  (internal-error "REPL checkpointed")))))
   (exit)))

 (define (vlad-I include-directory pathname)
  (set! *include-path* (list include-directory))
  (let loop ((es (read-source pathname)) (ds '()))
   (unless (null? es)
    (if (definition? (first es))
	(loop (rest es) (cons (first es) ds))
	(let ((e (expand-definitions (reverse ds) (first es))))
	 (syntax-check-expression! e)
	 (let* ((result (concrete->abstract e))
		(e (first result))
		(bs (second result)))
	  (il:eval (il:make-continuation
		    14
		    (lambda (value count limit path)
		     ;; count, limit, and path are ignored
		     (write value)
		     (newline)
		     (loop (rest es) ds)))
		   e
		   bs
		   0
		   (/ 1.0 0.0)
		   '())
	  (internal-error "REPL checkpointed")))))
   (exit))))
