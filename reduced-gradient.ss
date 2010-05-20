(library
 (reduced-gradient)
 (export uniform argmax)
 (import (except (rnrs) + - * / sqrt exp log expt sin cos atan = < > <= >=
		 zero? positive? negative? real? magnitude)
	 (rnrs r5rs (6))
	 (AD)
	 (QobiScheme))

 (define *reduced-gradient-debugging-print?* #t)

 (define (sqr x) (* x x))

 (define (uniform n) (map-n-vector (lambda (i) (/ n)) n))

 (define (negate f) (lambda (x) (- (f x))))

 (define (simplify-mixture p)
  (map-vector (lambda (p) (inexact->exact (round (* 100 p)))) p))

 (define (simplify-mixtures p) (map-vector simplify-mixture p))

 (define (safe-sum x)
  (let loop ((xs (sort (vector->list x) < identity)) (sum 0.0))
   (if (null? xs) sum (loop (rest xs) (+ (first xs) sum)))))

 (define (dependent-variable x)
  (let loop ((xs (sort (vector->list x) > identity)) (difference 1.0))
   (if (null? xs) difference (loop (rest xs) (- difference (first xs))))))

 (define (proper-mixture? x)
  (and (every-vector (lambda (x) (and (not (negative? x)) (<= x 1.0))) x)
       (< (abs (- (safe-sum x) 1.0)) 1e-14)))

 (define (pinned-at-zero? rx rgx i)
  (and (< (vector-ref rx i) 1e-4) (not (negative? (vector-ref rgx i)))))

 (define (argmin f x)
  (define (v- u v) (map-vector (lambda (u v) (map-vector - u v)) u v))
  (define (k*v k v)
   (map-vector (lambda (v) (map-vector (lambda (v) (* k v)) v)) v))
  (define (magnitude u)
   (sqrt
    (map-reduce-vector + 0.0 (lambda (u) (map-reduce-vector + 0.0 sqr u)) u)))
  (define (distance u v) (magnitude (v- u v)))
  (define (j x)
   (let loop ((j 0) (jmax -1) (max minus-infinity))
    (cond ((= j (vector-length x)) jmax)
	  ((> (vector-ref x j) max) (loop (+ j 1) j (vector-ref x j)))
	  (else (loop (+ j 1) jmax max)))))
  (define (reduce1 x)
   (map-vector
    (lambda (x) (list->vector (list-remove (vector->list x) (j x)))) x))
  (define (expand1 x rx)
   (map-vector (lambda (x rx)
		(list->vector
		 (list-insert (vector->list rx) (j x) (dependent-variable rx))))
	       x
	       rx))
  (define (reduced1 x)
   ((f-gradient-vector-vector-R (lambda (rx) (f (expand1 x rx)))) (reduce1 x)))
  (define (reduce2 x rgx)
   (map-vector
    (lambda (x rx rgx)
     (let ((j (j x)))
      (let loop ((i 0) (k 0) (rrx '()))
       (cond ((= i (vector-length x)) (list->vector (reverse rrx)))
	     ((= i j) (loop (+ i 1) k rrx))
	     ((pinned-at-zero? rx rgx k) (loop (+ i 1) (+ k 1) rrx))
	     (else (loop (+ i 1) (+ k 1) (cons (vector-ref rx k) rrx)))))))
    x
    (reduce1 x)
    rgx))
  (define (expand2 x rgx rrx)
   (map-vector
    (lambda (x rx rgx rrx)
     (let ((j (j x)))
      (let loop ((i 0) (k 0) (l 0) (ex '()))
       (cond
	((= i (vector-length x)) (list->vector (reverse ex)))
	((= i j) (loop (+ i 1) k l (cons (dependent-variable rrx) ex)))
	((pinned-at-zero? rx rgx k) (loop (+ i 1) (+ k 1) l (cons 0.0 ex)))
	(else (loop (+ i 1) (+ k 1) (+ l 1) (cons (vector-ref rrx l) ex)))))))
    x
    (reduce1 x)
    rgx
    rrx))
  (define (reduced2 x rgx)
   (map-vector
    (lambda (x rx rgx)
     (let ((j (j x)))
      (let loop ((i 0) (k 0) (rrgx '()))
       (cond ((= i (vector-length x)) (list->vector (reverse rrgx)))
	     ((= i j) (loop (+ i 1) k rrgx))
	     ((pinned-at-zero? rx rgx k) (loop (+ i 1) (+ k 1) rrgx))
	     (else (loop (+ i 1) (+ k 1) (cons (vector-ref rgx k) rrgx)))))))
    x
    (reduce1 x)
    rgx))
  (let* ((f-rgx (reduced1 x)) (rgx (second f-rgx)))
   (if (zero? (magnitude rgx))
       x
       (let loop ((x x)
		  (fx (first f-rgx))
		  (rgx rgx)
		  (rrgx (reduced2 x rgx))
		  (eta (/ (magnitude rgx)))
		  (i 0))
	(unless (every-vector proper-mixture? x) (fuck-up))
	(when *reduced-gradient-debugging-print?*
	 (display "x: ")
	 (write (simplify-mixtures x))
	 (newline)
	 (display "rrgx: ")
	 (write (map-vector
		 (lambda (x rx rgx rrgx)
		  (let ((j (j x)))
		   (let loop ((i 0) (k 0) (l 0) (ex '()))
		    (cond ((= i (vector-length x)) (list->vector (reverse ex)))
			  ((= i j) (loop (+ i 1) k  l (cons 'd ex)))
			  ((pinned-at-zero? rx rgx k)
			   (loop (+ i 1) (+ k 1) l (cons 'z ex)))
			  (else (loop (+ i 1)
				      (+ k 1)
				      (+ l 1)
				      (cons (vector-ref rrgx l) ex)))))))
		 x
		 (reduce1 x)
		 rgx
		 rrgx))
	 (newline)
	 (display "fx: ")
	 (write fx)
	 (newline)
	 (display "eta: ")
	 (write eta)
	 (newline)
	 (display "i: ")
	 (write i)
	 (newline)
	 (newline))
	(if (some-vector
	     (lambda (x rx rgx)
	      (let ((j (j x)))
	       (let loop ((i 0) (k 0))
		(cond
		 ((= i (vector-length x)) #f)
		 ((= i j) (loop (+ i 1) k))
		 ((pinned-at-zero? rx rgx k)
		  (or (not (zero? (vector-ref rx k))) (loop (+ i 1) (+ k 1))))
		 (else (loop (+ i 1) (+ k 1)))))))
	     x
	     (reduce1 x)
	     rgx)
	    (let* ((x-prime (expand2 x rgx (reduce2 x rgx)))
		   (f-rgx-prime (reduced1 x-prime))
		   (rgx-prime (second f-rgx-prime)))
	     (loop x-prime
		   (first f-rgx-prime)
		   rgx-prime
		   (reduced2 x-prime rgx-prime)
		   eta
		   i))
	    (let ((x-prime (expand2 x rgx (v- (reduce2 x rgx) (k*v eta rrgx)))))
	     (cond
	      ((some-vector
		(lambda (x-prime)
		 (some-vector
		  (lambda (x-prime) (or (negative? x-prime) (> x-prime 1.0)))
		  x-prime))
		x-prime)
	       (loop x fx rgx rrgx (/ eta 2.0) 0))
	      ((<= (distance x x-prime) 1e-10)
	       (when *reduced-gradient-debugging-print?*
		(display "distance is ")
		(write (distance x x-prime))
		(newline))
	       x)
	      (else
	       (let* ((f-rgx-prime (reduced1 x-prime))
		      (fx-prime (first f-rgx-prime))
		      (rgx-prime (second f-rgx-prime)))
		(if (< fx-prime fx)
		    (let ((rrgx-prime (reduced2 x-prime rgx-prime)))
		     (if (= i 2)
			 (loop
			  x-prime fx-prime rgx-prime rrgx-prime (* 2.0 eta) 0)
			 (loop
			  x-prime fx-prime rgx-prime rrgx-prime eta (+ i 1))))
		    (loop x fx rgx rrgx (/ eta 2.0) 0)))))))))))

 (define (argmax f x) (argmin (negate f) x)))
