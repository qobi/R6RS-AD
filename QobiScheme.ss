#!r6rs

(library
 (QobiScheme)
 (export first second third fourth fifth sixth rest last identity fuck-up
	 list-insert list-remove list-replace but-last sublist fold map-reduce
	 map-reduce-n map-reduce-vector some some-n some-vector every
	 every-vector one for-each-indexed for-each-n map-indexed map-n
	 map-vector map-n-vector enumerate removeq remove-if remove-if-not
	 positionq position-if find-if count-if-not unionq remove-duplicatesp
	 every-other merge sort matrix-ref minus-infinity)
 (import (rnrs))

 (define first car)

 (define second cadr)

 (define third caddr)

 (define fourth cadddr)

 (define (fifth x) (car (cddddr x)))

 (define (sixth x) (cadr (cddddr x)))

 (define rest cdr)

 (define (last x) (if (null? (rest x)) (first x) (last (rest x))))

 (define (identity x) x)

 (define (fuck-up) (error #f "This shouldn't happen"))

 (define (list-insert l i x)
  (if (zero? i)
      (cons x l)
      (cons (first l) (list-insert (rest l) (- i 1) x))))

 (define (list-remove l i)
  (if (zero? i) (rest l) (cons (first l) (list-remove (rest l) (- i 1)))))

 (define (list-replace l i x)
  (if (zero? i)
      (cons x (rest l))
      (cons (first l) (list-replace (rest l) (- i 1) x))))

 (define (but-last x) (reverse (rest (reverse x))))

 (define (sublist list start end)
  (if (zero? start)
      (let loop ((list list) (k end))
       (if (zero? k) '() (cons (car list) (loop (cdr list) (- k 1)))))
      (sublist (cdr list) (- start 1) (- end 1))))

 (define (fold f i l) (if (null? l) i (fold f (f i (first l)) (rest l))))

 (define (map-reduce g i f l . ls)
  (if (null? l)
      i
      (apply map-reduce
	     g
	     (g i (apply f (car l) (map car ls)))
	     f
	     (cdr l)
	     (map cdr ls))))

 (define (map-reduce-n g i f n)
  (if (zero? n) i (map-reduce-n g (g i (f (- n 1))) f (- n 1))))

 (define (map-reduce-vector g i f v . vs)
  (let loop ((j 0) (result i))
   (if (= j (vector-length v))
       result
       (loop (+ j 1)
	     (g result
		(apply f
		       (vector-ref v j)
		       (map (lambda (v) (vector-ref v j)) vs)))))))

 (define (some p l . &rest)
  (let loop ((l l) (&rest &rest))
   (and (not (null? l))
	(or (apply p (first l) (map first &rest))
	    (loop (rest l) (map rest &rest))))))

 (define (some-n p n)
  (let loop ((i 0)) (and (< i n) (or (p i) (loop (+ i 1))))))

 (define (some-vector p v . &rest)
  (let loop ((i 0))
   (and (< i (vector-length v))
	(or (apply p
		   (vector-ref v i)
		   (map (lambda (v) (vector-ref v i)) &rest))
	    (loop (+ i 1))))))

 (define (every p l . &rest)
  (let loop ((l l) (&rest &rest))
   (or (null? l)
       (and (apply p (first l) (map first &rest))
	    (loop (rest l) (map rest &rest))))))

 (define (every-vector p v . &rest)
  (let loop ((i 0))
   (or (>= i (vector-length v))
       (and (apply p
		   (vector-ref v i)
		   (map (lambda (v) (vector-ref v i)) &rest))
	    (loop (+ i 1))))))

 (define (one p l . &rest)
  (let loop ((l l) (&rest &rest))
   (and (not (null? l))
	(if (apply p (first l) (map first &rest))
	    (let loop ((l (rest l)) (&rest (map rest &rest)))
	     (or (null? l)
		 (and (not (apply p (first l) (map first &rest)))
		      (loop (rest l) (map rest &rest)))))
	    (loop (rest l) (map rest &rest))))))

 (define (for-each-indexed f l)
  (let loop ((i 0) (l l))
   (unless (null? l) (f (first l) i) (loop (+ i 1) (rest l)))))

 (define (for-each-n f n)
  (let loop ((i 0)) (when (< i n) (f i) (loop (+ i 1)))))

 (define (map-indexed f l)
  (let loop ((i 0) (l l) (c '()))
   (if (null? l)
       (reverse c)
       (loop (+ i 1) (rest l) (cons (f (first l) i) c)))))

 (define (map-n f n)
  (let loop ((i 0) (c '()))
   (if (< i n) (loop (+ i 1) (cons (f i) c)) (reverse c))))

 (define (map-vector f v . &rest)
  ;; needs work: Won't work correctly when F is nondeterministic.
  (let ((u (make-vector (vector-length v))))
   (for-each-n
    (lambda (i)
     (vector-set!
      u i
      (apply f (vector-ref v i) (map (lambda (v) (vector-ref v i)) &rest))))
    (vector-length v))
   u))

 (define (map-n-vector f n)
  ;; needs work: Won't work correctly when F is nondeterministic.
  (let ((v (make-vector n)))
   (let loop ((i 0))
    (when (< i n)
     (vector-set! v i (f i))
     (loop (+ i 1))))
   v))

 (define (enumerate n)
  (let loop ((i (- n 1)) (c '()))
   (if (>= i 0) (loop (- i 1) (cons i c)) c)))

 (define (removeq x l)
  (let loop ((l l) (c '()))
   (cond ((null? l) (reverse c))
	 ((eq? x (first l)) (loop (rest l) c))
	 (else (loop (rest l) (cons (first l) c))))))

 (define (remove-if p l)
  (let loop ((l l) (c '()))
   (cond ((null? l) (reverse c))
	 ((p (first l)) (loop (rest l) c))
	 (else (loop (rest l) (cons (first l) c))))))

 (define (remove-if-not p l)
  (let loop ((l l) (c '()))
   (cond ((null? l) (reverse c))
	 ((p (first l)) (loop (rest l) (cons (first l) c)))
	 (else (loop (rest l) c)))))

 (define (positionq x l)
  (let loop ((l l) (i 0))
   (cond ((null? l) #f)
	 ((eq? x (first l)) i)
	 (else (loop (rest l) (+ i 1))))))

 (define (position-if p l)
  (let loop ((l l) (i 0))
   (cond ((null? l) #f)
	 ((p (first l)) i)
	 (else (loop (rest l) (+ i 1))))))

 (define (find-if p l)
  (let loop ((l l))
   (cond ((null? l) #f)
	 ((p (first l)) (first l))
	 (else (loop (rest l))))))

 (define (count-if-not p l)
  (let loop ((l l) (c 0))
   (cond ((null? l) c)
	 ((p (first l)) (loop (rest l) c))
	 (else (loop (rest l) (+ c 1))))))

 (define (unionq x y)
  (let loop ((l x) (c '()))
   (cond ((null? l) (append (reverse c) y))
	 ((memq (first l) y) (loop (rest l) c))
	 (else (loop (rest l) (cons (first l) c))))))

 (define (remove-duplicatesp p x)
  (define (memp p x l)
   (cond ((null? l) #f) ((p x (first l)) l) (else (memp p x (rest l)))))
  (let loop ((x x) (c '()))
   (cond ((null? x) (reverse c))
	 ((memp p (first x) c) (loop (rest x) c))
	 (else (loop (rest x) (cons (first x) c))))))

 (define (every-other list)
  (cond ((null? list) '())
	((null? (rest list)) list)
	(else (cons (first list) (every-other (rest (rest list)))))))

 (define (merge list1 list2 predicate key)
  (cond ((null? list1) list2)
	((null? list2) list1)
	((predicate (key (first list1)) (key (first list2)))
	 (cons (first list1) (merge (rest list1) list2 predicate key)))
	(else (cons (first list2) (merge list1 (rest list2) predicate key)))))

 (define (sort list predicate key)
  (if (or (null? list) (null? (rest list)))
      list
      (merge (sort (every-other list) predicate key)
	     (sort (every-other (rest list)) predicate key)
	     predicate
	     key)))

 (define (matrix-ref a i j) (vector-ref (vector-ref a i) j))

 (define minus-infinity (log 0.0)))
