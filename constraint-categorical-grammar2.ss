#!r6rs

(library
 (constraint-categorical-grammar2)
 (export all-sentences)
 (import (rnrs)
	 (QobiScheme)
	 (nondeterministic-scheme)
	 (nondeterministic-constraints)
	 (nondeterministic-lifting))

 (define-record-type type (fields kind argument result))

 (define (unused? kind) (eq? kind 'unused))

 (define (used? kind) (not (eq? kind 'unused)))

 (define (implies p q) (or (not p) q))

 (define (create-type n)
  (if (zero? n)
      (make-type (new-domain-variable '(unused boolean thing)) #f #f)
      (let ((result (create-type (- n 1)))
	    (argument (create-type (- n 1)))
	    (kind-variable
	     (new-domain-variable '(unused boolean thing leftward rightward))))
       (assert-nondeterministic-constraint!
	(lambda (parent-kind child-kind)
	 (and (implies (memq parent-kind '(unused boolean thing))
		       (unused? child-kind))
	      (implies (memq parent-kind '(leftward rightward))
		       (used? child-kind))))
	kind-variable
	(type-kind result))
       (assert-nondeterministic-constraint!
	(lambda (parent-kind child-kind)
	 (and (implies (memq parent-kind '(unused boolean thing))
		       (unused? child-kind))
	      (implies (memq parent-kind '(leftward rightward))
		       (used? child-kind))))
	kind-variable
	(type-kind argument))
       (make-type kind-variable result argument))))

 (define (leftward-arrow-type?-constraint type)
  (memq-constraint (type-kind type) '(leftward)))

 (define (rightward-arrow-type?-constraint type)
  (memq-constraint (type-kind type) '(rightward)))

 (define (no-constituent?-constraint type)
  (memq-constraint (type-kind type) '(unused)))

 (define (constituent?-constraint type)
  (memq-constraint (type-kind type) '(boolean thing leftward rightward)))

 (define (equal-type?-constraint type1 type2)
  (if (and type1 type2)
      (and-constraint
       (eq?-constraint (type-kind type1) (type-kind type2))
       (or-constraint
	(memq-constraint (type-kind type1) '(unused boolean thing))
	(and-constraint
	 (equal-type?-constraint (type-argument type1) (type-argument type2))
	 (equal-type?-constraint (type-result type1) (type-result type2)))))
      (false-domain-variable)))

 (define (parse-type type)
  (cond ((eq? type 'boolean) (make-type (new-domain-variable '(boolean)) #f #f))
	((eq? type 'thing) (make-type (new-domain-variable '(thing)) #f #f))
	((and (list? type) (= (length type) 3) (eq? (first type) '<-))
	 (make-type (new-domain-variable '(leftward))
		    (parse-type (third type))
		    (parse-type (second type))))
	((and (list? type) (= (length type) 3) (eq? (first type) '->))
	 (make-type (new-domain-variable '(rightward))
		    (parse-type (second type))
		    (parse-type (third type))))
	(else (error #f "Bad type"))))

 (define *n* '(-> thing boolean))

 (define *np* `(-> ,*n* boolean))

 (define *d* `(-> ,*n* ,*np*))

 (define *s* 'boolean)

 (define *vp* `(<- ,*s* ,*np*))

 (define *v-np* `(-> ,*np* ,*vp*))

 (define *lexicon*
  ;; needs work: should abstract lexical entries
  (list (cons 'the (parse-type *d*))
	(cons 'x (parse-type *n*))
	(cons 'is-on (parse-type *v-np*))
	(cons 'center (parse-type *n*))))

 (define (create-word-variable)
  (new-domain-variable (remove-duplicates (map car *lexicon*))))

 (define (make-upper-triangular-matrix n initializer)
  (list->vector
   (map-n
    (lambda (i) (list->vector (map-n (lambda (j) (initializer)) (- n i 1))))
    n)))

 (define (upper-triangular-matrix-ref m i j)
  (vector-ref (vector-ref m i) (- j i 1)))

 (define (constraints! words)
  (let* ((n (+ (length words) 1))
	 ;; hardwired
	 (type (make-upper-triangular-matrix n (lambda () (create-type 4)))))
   (do ((i 0 (+ i 1))) ((= i (- n 1)))
    (assert! (map-reduce
	      or-constraint
	      (false-domain-variable)
	      (lambda (entry)
	       (and-constraint
		(memq-constraint (list-ref words i) (list (car entry)))
		(equal-type?-constraint
		 (upper-triangular-matrix-ref type i (+ i 1)) (cdr entry))))
	      *lexicon*)))
   (do ((i 0 (+ i 1))) ((= i (- n 2)))
    (do ((k (+ i 2) (+ k 1))) ((= k n))
     (assert!
      (or-constraint
       (no-constituent?-constraint (upper-triangular-matrix-ref type i k))
       (map-reduce-n
	or-constraint
	(false-domain-variable)
	(lambda (j)
	 (and-constraint (constituent?-constraint
			  (upper-triangular-matrix-ref type i (+ i j 1)))
			 (constituent?-constraint
			  (upper-triangular-matrix-ref type (+ i j 1) k))))
	(- k i 1))))))
   (do ((i 0 (+ i 1))) ((= i (- n 2)))
    (do ((j (+ i 1) (+ j 1))) ((= j (- n 1)))
     (do ((k (+ j 1) (+ k 1))) ((= k n))
      (let ((parent (upper-triangular-matrix-ref type i k))
	    (left (upper-triangular-matrix-ref type i j))
	    (right (upper-triangular-matrix-ref type j k)))
       (assert! (or-constraint
		 (no-constituent?-constraint parent)
		 (no-constituent?-constraint left)
		 (no-constituent?-constraint right)
		 (and-constraint
		  (leftward-arrow-type?-constraint right)
		  (equal-type?-constraint left (type-argument right))
		  (equal-type?-constraint parent (type-result right)))
		 (and-constraint
		  (rightward-arrow-type?-constraint left)
		  (equal-type?-constraint right (type-argument left))
		  (equal-type?-constraint parent (type-result left)))))))))
   (assert! (equal-type?-constraint
	     (upper-triangular-matrix-ref type 0 (- n 1)) (parse-type *s*)))))

 (define (all-sentences n)
  (initialize-domain-variables!)
  (domain (let ((words (map-n (lambda (i) (create-word-variable)) n)))
	   (constraints! words)
	   (nondeterministic-solution (domain-variables))
	   (map binding words)))))
