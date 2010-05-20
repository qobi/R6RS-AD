#!r6rs

(library
 (nondeterministic-recognizer)
 (export make-production a-tree yield phrase1? yield-equal? phrase2?
	 a-tree-yield-equal? phrase3?)
 (import (rnrs)
	 (QobiScheme)
	 (nondeterministic-scheme)
	 (nondeterministic-memoization))

 (define-record-type production (fields lhs rhs1 rhs2))

 (define-record-type tree (fields category left right))

 (define (a-tree category productions)
  (let ((matching-productions
	 (remove-if-not
	  (lambda (production) (eq? (production-lhs production) category))
	  productions)))
   (if (null? matching-productions)
       category
       (let ((production (a-member-of matching-productions)))
	(make-tree category
		   (a-tree (production-rhs1 production) productions)
		   (a-tree (production-rhs2 production) productions))))))

 (define (yield tree)
  (if (symbol? tree)
      (list tree)
      (append (yield (tree-left tree)) (yield (tree-right tree)))))

 (define (phrase1? categories category productions)
  (possibly?
   (domain (equal? categories (yield (a-tree category productions))))))

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

 (define (phrase2? categories category productions)
  (possibly? (domain (yield-equal? (a-tree category productions) categories))))

 (define a-tree-yield-equal?
  (memoize-nondeterministic-removing-duplicates
   (lambda (categories category productions)
    (let ((matching-productions
	   (remove-if-not
	    (lambda (production) (eq? (production-lhs production) category))
	    productions)))
     (or (and (null? matching-productions)
	      (null? (rest categories))
	      (eq? category (first categories)))
	 (let ((production (a-member-of matching-productions)))
	  (some-n (lambda (i)
		   (and (a-tree-yield-equal?
			 (sublist categories 0 (+ i 1))
			 (production-rhs1 production)
			 productions)
			(a-tree-yield-equal?
			 (sublist categories (+ i 1) (length categories))
			 (production-rhs2 production)
			 productions)))
		  (- (length categories) 1))))))))

 (define (phrase3? categories category productions)
  (possibly? (domain (a-tree-yield-equal? categories category productions)))))
