#!r6rs

(library
 (stochastic-recognizer)
 (export make-production a-tree yield phrase-probability1 yield-equal?
	 phrase-probability2 a-tree-yield-equal? phrase-probability3)
 (import (rnrs)
	 (QobiScheme)
	 (stochastic-scheme)
	 (stochastic-memoization))

 (define-record-type production (fields lhs rhs1 rhs2))

 (define-record-type tree (fields category left right))

 (define (a-tree category production-distributions)
  (let ((matching-production-distribution
	 (remove-if-not
	  (lambda (production-pair)
	   (eq? (production-lhs (car production-pair)) category))
	  production-distributions)))
   (if (null? matching-production-distribution)
       category
       (let ((production (draw matching-production-distribution)))
	(make-tree
	 category
	 (a-tree (production-rhs1 production) production-distributions)
	 (a-tree (production-rhs2 production) production-distributions))))))

 (define (yield tree)
  (if (symbol? tree)
      (list tree)
      (append (yield (tree-left tree)) (yield (tree-right tree)))))

 (define (phrase-probability1 categories category production-distributions)
  (probability
   (distribution (equal? categories
			 (yield (a-tree category production-distributions))))))

 (define (yield-equal? tree categories)
  (or (and (symbol? tree)
	   (null? (rest categories))
	   (eq? tree (first categories)))
      (and (tree? tree)
	   (some-n
	    (lambda (i)
	     (and
	      (yield-equal? (tree-left tree) (sublist categories 0 (+ i 1)))
	      (yield-equal? (tree-right tree)
			    (sublist categories (+ i 1) (length categories)))))
	    (- (length categories) 1)))))

 (define (phrase-probability2 categories category production-distributions)
  (probability
   (distribution
    (yield-equal? (a-tree category production-distributions) categories))))

 (define a-tree-yield-equal?
  (memoize-stochastic-coalescing-duplicates
   (lambda (categories category production-distributions)
    (let ((matching-production-distribution
	   (remove-if-not
	    (lambda (production-pair)
	     (eq? (production-lhs (car production-pair)) category))
	    production-distributions)))
     (or (and (null? matching-production-distribution)
	      (null? (rest categories))
	      (eq? category (first categories)))
	 (let ((production (draw matching-production-distribution)))
	  (some-n (lambda (i)
		   (and (a-tree-yield-equal?
			 (sublist categories 0 (+ i 1))
			 (production-rhs1 production)
			 production-distributions)
			(a-tree-yield-equal?
			 (sublist categories (+ i 1) (length categories))
			 (production-rhs2 production)
			 production-distributions)))
		  (- (length categories) 1))))))))

 (define (phrase-probability3 categories category production-distributions)
  (probability
   (distribution
    (a-tree-yield-equal? categories category production-distributions)))))
