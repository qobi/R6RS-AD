#!r6rs

(library
 (wwd)
 (export *empty* grid-xy? grid-zy? below? below next? next previous? previous
	 grid-points empty? grid-point-contents=? create-grid max-x max-y max-z
	 at grid-binding lift-grid write-grid implies iff
	 assert-lincoln-log-grammar-constraints!
	 left-edge? right-edge? empty?-constraint left-edge?-constraint
	 right-edge?-constraint valid-thing? thing-xy? thing-zy?
	 thing-width thing-height thing-left-of? thing-below? thing-inside?
	 from-to-by things wall?-constraint window?-constraint door?-constraint
	 solid?-constraint
	 parse-type pretty-type parse-expression pretty-expression pretty-value
	 pretty-environment type free-variables equal-type? equal-value?
	 create-typed-meaning evaluate call *s* *n* *np* *d* *vp* *v* *v-np*
	 *lexicon* a-typed-apply a-meaning-constraint create-word-variable
	 create-type-variable make-upper-triangular-matrix
	 upper-triangular-matrix-ref constraints all-domain-variables
	 all-sentences)
 (import (rnrs)
	 (QobiScheme)
	 (nondeterministic-scheme)
	 (rename (nondeterministic-constraints)
		 (binding nondeterministic-constraints:binding))
	 (nondeterministic-lifting))

 ;; x, y, and z are nonnegative integers
 ;; x and z are horizontal axes
 ;; y is vertical axis increasing upward
 ;; looking down along y increasing x is horizontal rightward axis
 ;; and increasing z is vertical upward axis
 ;; y=0 is the layer on the ground
 ;; even y are oriented along x
 ;; odd y are oriented along z
 (define-record-type grid-point (fields x y z))

 ;; notches: 1, 2, or 3, 0<=notch<notches an integer
 ;; each grid point is occupied by either a grid-point-contents or #f indicating
 ;; empty
 (define-record-type grid-point-contents (fields notches notch))

 ;; left, bottom, right, top, depth are nonnegative integers
 (define-record-type thing (fields left bottom right top depth))

 (define-record-type typed-meaning (fields type meaning))

 (define-record-type arrow-type (fields argument result))

 (define-record-type leftward-arrow-type (fields result argument))

 (define-record-type rightward-arrow-type (fields argument result))

 (define-record-type variable-access-expression (fields variable type))

 (define-record-type lambda-expression
  (fields variable expression variables types type))

 (define-record-type llambda-expression
  (fields variable expression variables types type))

 (define-record-type rlambda-expression
  (fields variable expression variables types type))

 (define-record-type application (fields callee argument type))

 (define-record-type and-expression (fields expressions))

 (define-record-type or-expression (fields expressions))

 (define-record-type not-expression (fields expression))

 (define-record-type some-expression (fields expression))

 (define-record-type every-expression (fields expression))

 (define-record-type at-least-expression (fields k expression))

 (define-record-type at-most-expression (fields k expression))

 (define-record-type exactly-expression (fields k expression))

 (define-record-type wall?-expression (fields expression))

 (define-record-type window?-expression (fields expression))

 (define-record-type door?-expression (fields expression))

 (define-record-type solid?-expression (fields expression))

 (define-record-type width=?-expression (fields expression k))

 (define-record-type height=?-expression (fields expression k))

 (define-record-type left-of?-expression (fields expression1 expression2))

 (define-record-type below?-expression (fields expression1 expression2))

 (define-record-type perpendicular?-expression (fields expression1 expression2))

 (define-record-type inside?-expression (fields expression1 expression2))

 (define-record-type binding (fields variable value))

 (define-record-type closure (fields environment expression))

 (define *empty* #f)

 ;; Grid points

 (define (grid-xy? grid-point) (even? (grid-point-y grid-point)))

 (define (grid-zy? grid-point) (odd? (grid-point-y grid-point)))

 (define (below? grid-point) (>= (grid-point-y grid-point) 1))

 (define (below grid-point)
  (make-grid-point (grid-point-x grid-point)
		   (- (grid-point-y grid-point) 1)
		   (grid-point-z grid-point)))

 (define (next? grid grid-point)
  (cond ((grid-xy? grid-point) (< (grid-point-x grid-point) (- (max-x grid) 1)))
	((grid-zy? grid-point) (< (grid-point-z grid-point) (- (max-z grid) 1)))
	(else (fuck-up))))

 (define (next grid-point)
  (cond ((grid-xy? grid-point)
	 (make-grid-point (+ (grid-point-x grid-point) 1)
			  (grid-point-y grid-point)
			  (grid-point-z grid-point)))
	((grid-zy? grid-point)
	 (make-grid-point (grid-point-x grid-point)
			  (grid-point-y grid-point)
			  (+ (grid-point-z grid-point) 1)))
	(else (fuck-up))))

 (define (previous? grid-point)
  (cond ((grid-xy? grid-point) (positive? (grid-point-x grid-point)))
	((grid-zy? grid-point) (positive? (grid-point-z grid-point)))
	(else (fuck-up))))

 (define (previous grid-point)
  (cond ((grid-xy? grid-point)
	 (make-grid-point (- (grid-point-x grid-point) 1)
			  (grid-point-y grid-point)
			  (grid-point-z grid-point)))
	((grid-zy? grid-point)
	 (make-grid-point (grid-point-x grid-point)
			  (grid-point-y grid-point)
			  (- (grid-point-z grid-point) 1)))
	(else (fuck-up))))

 (define (grid-points grid)
  (map-reduce-n
   append
   '()
   (lambda (x)
    (map-reduce-n
     append
     '()
     (lambda (y) (map-n (lambda (z) (make-grid-point x y z)) (max-z grid)))
     (max-y grid)))
   (max-x grid)))

 ;; Grid point contents

 (define (empty? grid-point-contents) (eq? grid-point-contents *empty*))

 (define (grid-point-contents=? grid-point-contents1 grid-point-contents2)
  (or (and (empty? grid-point-contents1) (empty? grid-point-contents2))
      (and (not (empty? grid-point-contents1))
	   (not (empty? grid-point-contents2))
	   (= (grid-point-contents-notches grid-point-contents1)
	      (grid-point-contents-notches grid-point-contents2))
	   (= (grid-point-contents-notch grid-point-contents1)
	      (grid-point-contents-notch grid-point-contents2)))))

 ;; The grid

 (define (create-grid x y z)
  (map-n-vector
   (lambda (x)
    (map-n-vector (lambda (y)
		   (map-n-vector (lambda (z)
				  (new-domain-variable
				   (list *empty*
					 (make-grid-point-contents 1 0)
					 (make-grid-point-contents 2 0)
					 (make-grid-point-contents 2 1)
					 (make-grid-point-contents 3 0)
					 (make-grid-point-contents 3 1)
					 (make-grid-point-contents 3 2))))
				 z))
		  y))
   x))

 (define (max-x grid) (vector-length grid))

 (define (max-y grid) (vector-length (vector-ref grid 0)))

 (define (max-z grid) (vector-length (vector-ref (vector-ref grid 0) 0)))

 (define (at grid grid-point)
  (vector-ref (vector-ref (vector-ref grid (grid-point-x grid-point))
			  (grid-point-y grid-point))
	      (grid-point-z grid-point)))

 (define (grid-binding grid)
  (map-n-vector
   (lambda (x)
    (map-n-vector
     (lambda (y)
      (map-n-vector
       (lambda (z)
	(nondeterministic-constraints:binding
	 (at grid (make-grid-point x y z))))
       (max-z grid)))
     (max-y grid)))
   (max-x grid)))

 (define (lift-grid grid)
  (map-n-vector
   (lambda (x)
    (map-n-vector
     (lambda (y)
      (map-n-vector
       (lambda (z)
	(new-domain-variable (list (at grid (make-grid-point x y z)))))
       (max-z grid)))
     (max-y grid)))
   (max-x grid)))

 (define (write-grid grid pathname)
  (call-with-output-file pathname
   (lambda (port)
    (for-each-n
     (lambda (x)
      (for-each-n
       (lambda (y)
	(for-each-n
	 (lambda (z)
	  (let ((grid-point-contents
		 (nondeterministic-constraints:binding
		  (at grid (make-grid-point x y z)))))
	   (unless (empty? grid-point-contents)
	    (write x port)
	    (display " " port)
	    (write y port)
	    (display " " port)
	    (write z port)
	    (display " " port)
	    (write (grid-point-contents-notches grid-point-contents) port)
	    (display " " port)
	    (write (grid-point-contents-notch grid-point-contents) port)
	    (newline port))))
	 (max-z grid)))
       (max-y grid)))
     (max-x grid)))))

 ;; The Grammar of Lincoln Logs

 (define (implies p q) (or (not p) q))

 (define (iff p q) (eq? p q))

 (define (assert-lincoln-log-grammar-constraints! grid)
  (for-each
   (lambda (grid-point)
    ;; 2-notch logs occupy two adjacent grid points
    ;; 2, 3
    (if (next? grid grid-point)
	(assert-nondeterministic-constraint!
	 (lambda (Zp Znp)
	  (iff (grid-point-contents=? Zp (make-grid-point-contents 2 0))
	       (grid-point-contents=? Znp (make-grid-point-contents 2 1))))
	 (at grid grid-point)
	 (at grid (next grid-point)))
	(assert-nondeterministic-constraint!
	 (lambda (Zp)
	  (not (grid-point-contents=? Zp (make-grid-point-contents 2 0))))
	 (at grid grid-point)))
    (unless (previous? grid-point)
     (assert-nondeterministic-constraint!
      (lambda (Zp)
       (not (grid-point-contents=? Zp (make-grid-point-contents 2 1))))
      (at grid grid-point)))
    ;; 3-notch logs occupy three adjacent grid points
    ;; 4, 6
    (if (next? grid grid-point)
	(assert-nondeterministic-constraint!
	 (lambda (Zp Znp)
	  (iff (grid-point-contents=? Zp (make-grid-point-contents 3 0))
	       (grid-point-contents=? Znp (make-grid-point-contents 3 1))))
	 (at grid grid-point)
	 (at grid (next grid-point)))
	(assert-nondeterministic-constraint!
	 (lambda (Zp)
	  (not (grid-point-contents=? Zp (make-grid-point-contents 3 0))))
	 (at grid grid-point)))
    (unless (previous? grid-point)
     (assert-nondeterministic-constraint!
      (lambda (Zp)
       (not (grid-point-contents=? Zp (make-grid-point-contents 3 1))))
      (at grid grid-point)))
    ;; 5, 8
    (if (and (next? grid grid-point) (next? grid (next grid-point)))
	(assert-nondeterministic-constraint!
	 (lambda (Zp znnp)
	  (iff (grid-point-contents=? Zp (make-grid-point-contents 3 0))
	       (grid-point-contents=? znnp (make-grid-point-contents 3 2))))
	 (at grid grid-point)
	 (at grid (next (next grid-point))))
	(assert-nondeterministic-constraint!
	 (lambda (Zp)
	  (not (grid-point-contents=? Zp (make-grid-point-contents 3 0))))
	 (at grid grid-point)))
    (unless (and (previous? grid-point) (previous? (previous grid-point)))
     (assert-nondeterministic-constraint!
      (lambda (Zp)
       (not (grid-point-contents=? Zp (make-grid-point-contents 3 2))))
      (at grid grid-point)))
    ;; 7, 9
    (if (next? grid grid-point)
	(assert-nondeterministic-constraint!
	 (lambda (Zp Znp)
	  (iff (grid-point-contents=? Zp (make-grid-point-contents 3 1))
	       (grid-point-contents=? Znp (make-grid-point-contents 3 2))))
	 (at grid grid-point)
	 (at grid (next grid-point)))
	(assert-nondeterministic-constraint!
	 (lambda (Zp)
	  (not (grid-point-contents=? Zp (make-grid-point-contents 3 1))))
	 (at grid grid-point)))
    ;; 1- and 2-notch logs must be supported at all notches
    ;; 10
    (when (below? grid-point)
     (assert-nondeterministic-constraint!
      (lambda (Zp Zbp)
       (implies (or (grid-point-contents=? Zp (make-grid-point-contents 1 0))
		    (grid-point-contents=? Zp (make-grid-point-contents 2 0))
		    (grid-point-contents=? Zp (make-grid-point-contents 2 1)))
		(not (empty? Zbp))))
      (at grid grid-point)
      (at grid (below grid-point))))
    ;; 3-notch logs must be supported at at least 2 out of 3 notches
    ;; 11
    (when (and (below? grid-point)
	       (next? grid grid-point)
	       (below? (next grid-point))
	       (next? grid (next grid-point))
	       (next? grid (next grid-point))
	       (below? (next (next grid-point))))
     (assert-nondeterministic-constraint!
      (lambda (Zp Zbp Zbnp Zbnnp)
       (implies (grid-point-contents=? Zp (make-grid-point-contents 3 0))
		(or (and (not (empty? Zbp)) (not (empty? Zbnp)))
		    (and (not (empty? Zbp)) (not (empty? Zbnnp)))
		    (and (not (empty? Zbnp)) (not (empty? Zbnnp))))))
      (at grid grid-point)
      (at grid (below grid-point))
      (at grid (below (next grid-point)))
      (at grid (below (next (next grid-point))))))
    ;; 12
    (when (and (below? grid-point)
	       (next? grid grid-point)
	       (below? (next grid-point))
	       (previous? grid-point)
	       (below? (previous grid-point)))
     (assert-nondeterministic-constraint!
      (lambda (Zp Zbp Zbnp Zbpp)
       (implies (grid-point-contents=? Zp (make-grid-point-contents 3 1))
		(or (and (not (empty? Zbp)) (not (empty? Zbnp)))
		    (and (not (empty? Zbp)) (not (empty? Zbpp)))
		    (and (not (empty? Zbnp)) (not (empty? Zbpp))))))
      (at grid grid-point)
      (at grid (below grid-point))
      (at grid (below (next grid-point)))
      (at grid (below (previous grid-point)))))
    ;; 13
    (when (and (below? grid-point)
	       (previous? grid-point)
	       (below? (previous grid-point))
	       (previous? (previous grid-point))
	       (previous? (previous grid-point))
	       (below? (previous (previous grid-point))))
     (assert-nondeterministic-constraint!
      (lambda (Zp Zbp Zbpp Zbppp)
       (implies (grid-point-contents=? Zp (make-grid-point-contents 3 2))
		(or (and (not (empty? Zbp)) (not (empty? Zbpp)))
		    (and (not (empty? Zbp)) (not (empty? Zbppp)))
		    (and (not (empty? Zbpp)) (not (empty? Zbppp))))))
      (at grid grid-point)
      (at grid (below grid-point))
      (at grid (below (previous grid-point)))
      (at grid (below (previous (previous grid-point)))))))
   (grid-points grid)))

 ;; Linguistic Constraints

 (define (left-edge? grid-point-contents)
  (and (not (empty? grid-point-contents))
       (zero? (grid-point-contents-notch grid-point-contents))))

 (define (right-edge? grid-point-contents)
  (and (not (empty? grid-point-contents))
       (= (grid-point-contents-notch grid-point-contents)
	  (- (grid-point-contents-notches grid-point-contents) 1))))

 (define (empty?-constraint grid-point-contents-variable)
  (let ((boolean-variable (create-boolean-variable)))
   (assert-nondeterministic-constraint!
    (lambda (boolean grid-point-contents)
     (eq? boolean (empty? grid-point-contents)))
    boolean-variable
    grid-point-contents-variable)
   boolean-variable))

 (define (left-edge?-constraint grid-point-contents-variable)
  (let ((boolean-variable (create-boolean-variable)))
   (assert-nondeterministic-constraint!
    (lambda (boolean grid-point-contents)
     (eq? boolean (left-edge? grid-point-contents)))
    boolean-variable
    grid-point-contents-variable)
   boolean-variable))

 (define (right-edge?-constraint grid-point-contents-variable)
  (let ((boolean-variable (create-boolean-variable)))
   (assert-nondeterministic-constraint!
    (lambda (boolean grid-point-contents)
     (eq? boolean (right-edge? grid-point-contents)))
    boolean-variable
    grid-point-contents-variable)
   boolean-variable))

 (define (valid-thing? thing)
  (and
   ;; Since this is < instead of <=, a tower of 1-notch logs doesn't count as
   ;; a wall.
   (< (thing-left thing) (thing-right thing))
   ;; If this would be < instead of <= then couldn't have 1-log-high walls,
   ;; windows, and doors.
   (<= (thing-bottom thing) (thing-top thing))
   (or (and (even? (thing-bottom thing)) (even? (thing-top thing)))
       (and (odd? (thing-bottom thing)) (odd? (thing-top thing))))))

 (define (thing-xy? thing) (even? (thing-bottom thing)))

 (define (thing-zy? thing) (odd? (thing-bottom thing)))

 ;; Because there is no +1, a wall made of 2-notch logs has width 1. And a wall
 ;; of width 1 can contain a window or door of width 1.
 (define (thing-width thing) (- (thing-right thing) (thing-left thing)))

 ;; The +1 is so that 1-log-high walls, windows, and doors have a height of 1.
 (define (thing-height thing)
  (+ (/ (- (thing-top thing) (thing-bottom thing)) 2) 1))

 (define (thing-left-of? thing1 thing2)
  ;; This doesn't constrain the vertical relation.
  ;; It doesn't allow horizontal overlap.
  ;; It does allow adjacency.
  (and (eq? (thing-xy? thing1) (thing-xy? thing2))
       (= (thing-depth thing1) (thing-depth thing2))
       (<= (thing-right thing1) (thing-left thing2))))

 (define (thing-below? thing1 thing2)
  ;; This doesn't constrain the horizontal relation.
  ;; It doesn't allow vertical overlap.
  ;; It doesn't allow adjacency.
  (and (eq? (thing-xy? thing1) (thing-xy? thing2))
       (= (thing-depth thing1) (thing-depth thing2))
       (< (thing-top thing1) (thing-bottom thing2))))

 (define (thing-perpendicular? thing1 thing2)
  (not (eq? (thing-xy? thing1) (thing-xy? thing2))))

 (define (thing-inside? thing1 thing2)
  (and (>= (thing-right thing1) (thing-right thing2))
       (<= (thing-left thing1) (thing-left thing2))
       (>= (thing-bottom thing1) (thing-bottom thing2))
       (<= (thing-top thing1) (thing-top thing2))
       (= (thing-depth thing1) (thing-depth thing2))))

 (define (from-to-by i j k)
  (if ((if (negative? k) < >) i j) '() (cons i (from-to-by (+ i k) j k))))

 (define (things grid)
  (append
   (map-reduce-n
    append
    '()
    (lambda (bottom)
     (map-reduce-n
      append
      '()
      (lambda (top)
       (map-reduce-n
	append
	'()
	(lambda (left)
	 (map-reduce-n
	  append
	  '()
	  (lambda (right)
	   (map-reduce-n
	    append
	    '()
	    (lambda (depth)
	     (let ((thing (make-thing left bottom right top depth)))
	      (if (and (thing-xy? thing) (valid-thing? thing))
		  (list thing)
		  '())))
	    (max-z grid)))
	  (max-x grid)))
	(max-x grid)))
      (max-y grid)))
    (max-y grid))
   (map-reduce-n
    append
    '()
    (lambda (bottom)
     (map-reduce-n
      append
      '()
      (lambda (top)
       (map-reduce-n
	append
	'()
	(lambda (left)
	 (map-reduce-n
	  append
	  '()
	  (lambda (right)
	   (map-reduce-n
	    append
	    '()
	    (lambda (depth)
	     (let ((thing (make-thing left bottom right top depth)))
	      (if (and (thing-zy? thing) (valid-thing? thing))
		  (list thing)
		  '())))
	    (max-x grid)))
	  (max-z grid)))
	(max-z grid)))
      (max-y grid)))
    (max-y grid))))

 (define (wall?-constraint grid thing)
  ;; A wall has
  ;; - its bottom along the ground
  ;;     there is no constraint as to the bottom being populated
  ;; - its left and right edges fully populated with outward log ends
  ;;     they must be fully populated and they must be outward log ends
  ;; - all grid points along its top edge populated
  ;; - no grid point along its top edge (except possibly the rightmost)
  ;;   populated with a right edge
  ;; - no grid point along its top edge (except possibly the leftmost)
  ;;   populated with a left edge
  ;; - no grid points on the row above its top edge populated
  ;; A wall need not be fully populated; it can have holes
  (or-constraint
   (if
    ;; - its bottom along the ground
    ;;     there is no constraint as to the bottom being populated
    (zero? (thing-bottom thing))
    (and-constraint
     ;; - its left and right edges fully populated with outward log ends
     ;;     they must be fully populated and they must be outward log ends
     (every-constraint
      (lambda (y)
       (and-constraint
	(left-edge?-constraint
	 (at grid
	     (make-grid-point (thing-left thing) y (thing-depth thing))))
	(right-edge?-constraint
	 (at grid
	     (make-grid-point (thing-right thing) y (thing-depth thing))))))
      (from-to-by (thing-bottom thing) (thing-top thing) 2))
     ;; - all grid points along its top edge populated
     (every-constraint
      (lambda (x)
       (not-constraint
	(empty?-constraint
	 (at grid
	     (make-grid-point x (thing-top thing) (thing-depth thing))))))
      (from-to-by (thing-left thing) (thing-right thing) 1))
     ;; - no grid point along its top edge (except possibly the rightmost)
     ;;   populated with a right edge
     (every-constraint
      (lambda (x)
       (not-constraint
	(right-edge?-constraint
	 (at grid
	     (make-grid-point x (thing-top thing) (thing-depth thing))))))
      (from-to-by (thing-left thing) (- (thing-right thing) 1) 1))
     ;; - no grid point along its top edge (except possibly the leftmost)
     ;;   populated with a left edge
     (every-constraint
      (lambda (x)
       (not-constraint
	(left-edge?-constraint
	 (at grid
	     (make-grid-point x (thing-top thing) (thing-depth thing))))))
      (from-to-by (+ (thing-left thing) 1) (thing-right thing) 1))
     ;; - no grid points on the row above its top edge populated
     (if (< (+ (thing-top thing) 2) (max-y grid))
	 (every-constraint
	  (lambda (x)
	   (empty?-constraint
	    (at grid
		(make-grid-point
		 x (+ (thing-top thing) 2) (thing-depth thing)))))
	  (from-to-by (thing-left thing) (thing-right thing) 1))
	 (true-domain-variable)))
    (false-domain-variable))
   (if
    ;; - its bottom along the ground
    ;;     there is no constraint as to the bottom being populated
    (= (thing-bottom thing) 1)
    (and-constraint
     ;; - its left and right edges fully populated with outward log ends
     ;;     they must be fully populated and they must be outward log ends
     (every-constraint
      (lambda (y)
       (and-constraint
	(left-edge?-constraint
	 (at grid
	     (make-grid-point (thing-depth thing) y (thing-left thing))))
	(right-edge?-constraint
	 (at grid
	     (make-grid-point (thing-depth thing) y (thing-right thing))))))
      (from-to-by (thing-bottom thing) (thing-top thing) 2))
     ;; - all grid points along its top edge populated
     (every-constraint
      (lambda (z)
       (not-constraint
	(empty?-constraint
	 (at grid
	     (make-grid-point (thing-depth thing) (thing-top thing) z)))))
      (from-to-by (thing-left thing) (thing-right thing) 1))
     ;; - no grid point along its top edge (except possibly the rightmost)
     ;;   populated with a right edge
     (every-constraint
      (lambda (z)
       (not-constraint
	(right-edge?-constraint
	 (at grid
	     (make-grid-point (thing-depth thing) (thing-top thing) z)))))
      (from-to-by (thing-left thing) (- (thing-right thing) 1) 1))
     ;; - no grid point along its top edge (except possibly the leftmost)
     ;;   populated with a left edge
     (every-constraint
      (lambda (z)
       (not-constraint
	(left-edge?-constraint
	 (at grid
	     (make-grid-point (thing-depth thing) (thing-top thing) z)))))
      (from-to-by (+ (thing-left thing) 1) (thing-right thing) 1))
     ;; - no grid points on the row above its top edge populated
     (if (< (+ (thing-top thing) 2) (max-y grid))
	 (every-constraint
	  (lambda (z)
	   (empty?-constraint
	    (at grid
		(make-grid-point
		 (thing-depth thing) (+ (thing-top thing) 2) z))))
	  (from-to-by (thing-left thing) (thing-right thing) 1))
	 (true-domain-variable)))
    (false-domain-variable))))

 (define (window?-constraint grid thing)
  ;; A window has
  ;; - its left and right edges fully populated with inward log ends
  ;;     they must be fully populated and they must be inward log ends
  ;; - no grid points between left+1 and right-1 and top and bottom populated
  ;; - all grid points on the row above its top edge populated
  ;; - no grid point on the row above its top edge (except possibly the
  ;;   rightmost) populated with a right edge
  ;; - no grid point on the row above its top edge (except possibly the
  ;;   leftmost) populated with a left edge
  ;; - all grid points on the row below its bottom edge populated
  ;; - no grid point on the row below its bottom edge (except possibly the
  ;;   rightmost) populated with a right edge
  ;; - no grid point on the row below its bottom edge (except possibly the
  ;;   leftmost) populated with a left edge
  (or-constraint
   (if (and (thing-xy? thing)
	    (>= (- (thing-bottom thing) 2) 0)
	    (< (+ (thing-top thing) 2) (max-y grid)))
       (and-constraint
	;; - its left and right edges fully populated with inward log ends
	;;     they must be fully populated and they must be inward log ends
	(every-constraint
	 (lambda (y)
	  (and-constraint
	   (right-edge?-constraint
	    (at grid
		(make-grid-point (thing-left thing) y (thing-depth thing))))
	   (left-edge?-constraint
	    (at grid
		(make-grid-point (thing-right thing) y (thing-depth thing))))))
	 (from-to-by (thing-bottom thing) (thing-top thing) 2))
	;; - no grid points between left+1 and right-1 and top and bottom
	;;   populated
	(every-constraint
	 (lambda (x)
	  (every-constraint
	   (lambda (y)
	    (empty?-constraint
	     (at grid (make-grid-point x y (thing-depth thing)))))
	   (from-to-by (thing-bottom thing) (thing-top thing) 2)))
	 (from-to-by (+ (thing-left thing) 1) (- (thing-right thing) 1) 1))
	;; - all grid points on the row above its top edge populated
	(every-constraint
	 (lambda (x)
	  (not-constraint
	   (empty?-constraint
	    (at grid
		(make-grid-point
		 x (+ (thing-top thing) 2) (thing-depth thing))))))
	 (from-to-by (thing-left thing) (thing-right thing) 1))
	;; - no grid point on the row above its top edge (except possibly the
	;;   rightmost) populated with a right edge
	(every-constraint
	 (lambda (x)
	  (not-constraint
	   (right-edge?-constraint
	    (at grid
		(make-grid-point
		 x (+ (thing-top thing) 2) (thing-depth thing))))))
	 (from-to-by (thing-left thing) (- (thing-right thing) 1) 1))
	;; - no grid point on the row above its top edge (except possibly the
	;;   leftmost) populated with a left edge
	(every-constraint
	 (lambda (x)
	  (not-constraint
	   (left-edge?-constraint
	    (at grid
		(make-grid-point
		 x (+ (thing-top thing) 2) (thing-depth thing))))))
	 (from-to-by (+ (thing-left thing) 1) (thing-right thing) 1))
	;; - all grid points on the row below its bottom edge populated
	(every-constraint
	 (lambda (x)
	  (not-constraint
	   (empty?-constraint
	    (at grid
		(make-grid-point
		 x (- (thing-bottom thing) 2) (thing-depth thing))))))
	 (from-to-by (thing-left thing) (thing-right thing) 1))
	;; - no grid point on the row below its bottom edge (except possibly the
	;;   rightmost) populated with a right edge
	(every-constraint
	 (lambda (x)
	  (not-constraint
	   (right-edge?-constraint
	    (at grid
		(make-grid-point
		 x (- (thing-bottom thing) 2) (thing-depth thing))))))
	 (from-to-by (thing-left thing) (- (thing-right thing) 1) 1))
	;; - no grid point on the row below its bottom edge (except possibly the
	;;   leftmost) populated with a left edge
	(every-constraint
	 (lambda (x)
	  (not-constraint
	   (left-edge?-constraint
	    (at grid
		(make-grid-point
		 x (- (thing-bottom thing) 2) (thing-depth thing))))))
	 (from-to-by (+ (thing-left thing) 1) (thing-right thing) 1)))
       (false-domain-variable))
   (if (and (thing-zy? thing)
	    (>= (- (thing-bottom thing) 2) 0)
	    (< (+ (thing-top thing) 2) (max-y grid)))
       (and-constraint
	;; - its left and right edges fully populated with inward log ends
	;;     they must be fully populated and they must be inward log ends
	(every-constraint
	 (lambda (y)
	  (and-constraint
	   (right-edge?-constraint
	    (at grid
		(make-grid-point (thing-depth thing) y (thing-left thing))))
	   (left-edge?-constraint
	    (at grid
		(make-grid-point (thing-depth thing) y (thing-right thing))))))
	 (from-to-by (thing-bottom thing) (thing-top thing) 2))
	;; - no grid points between left+1 and right-1 and top and bottom
	;;   populated
	(every-constraint
	 (lambda (z)
	  (every-constraint
	   (lambda (y)
	    (empty?-constraint
	     (at grid (make-grid-point (thing-depth thing) y z))))
	   (from-to-by (thing-bottom thing) (thing-top thing) 2)))
	 (from-to-by (+ (thing-left thing) 1) (- (thing-right thing) 1) 1))
	;; - all grid points on the row above its top edge populated
	(every-constraint
	 (lambda (z)
	  (not-constraint
	   (empty?-constraint
	    (at grid
		(make-grid-point
		 (thing-depth thing) (+ (thing-top thing) 2) z)))))
	 (from-to-by (thing-left thing) (thing-right thing) 1))
	;; - no grid point on the row above its top edge (except possibly the
	;;   rightmost) populated with a right edge
	(every-constraint
	 (lambda (z)
	  (not-constraint
	   (right-edge?-constraint
	    (at grid
		(make-grid-point
		 (thing-depth thing) (+ (thing-top thing) 2) z)))))
	 (from-to-by (thing-left thing) (- (thing-right thing) 1) 1))
	;; - no grid point on the row above its top edge (except possibly the
	;;   leftmost) populated with a left edge
	(every-constraint
	 (lambda (z)
	  (not-constraint
	   (left-edge?-constraint
	    (at grid
		(make-grid-point
		 (thing-depth thing) (+ (thing-top thing) 2) z)))))
	 (from-to-by (+ (thing-left thing) 1) (thing-right thing) 1))
	;; - all grid points on the row below its bottom edge populated
	(every-constraint
	 (lambda (z)
	  (not-constraint
	   (empty?-constraint
	    (at grid
		(make-grid-point
		 (thing-depth thing) (- (thing-bottom thing) 2) z)))))
	 (from-to-by (thing-left thing) (thing-right thing) 1))
	;; - no grid point on the row below its bottom edge (except possibly the
	;;   rightmost) populated with a right edge
	(every-constraint
	 (lambda (z)
	  (not-constraint
	   (right-edge?-constraint
	    (at grid
		(make-grid-point
		 (thing-depth thing) (- (thing-bottom thing) 2) z)))))
	 (from-to-by (thing-left thing) (- (thing-right thing) 1) 1))
	;; - no grid point on the row below its bottom edge (except possibly the
	;;   leftmost) populated with a left edge
	(every-constraint
	 (lambda (z)
	  (not-constraint
	   (left-edge?-constraint
	    (at grid
		(make-grid-point
		 (thing-depth thing) (- (thing-bottom thing) 2) z)))))
	 (from-to-by (+ (thing-left thing) 1) (thing-right thing) 1)))
       (false-domain-variable))))

 (define (door?-constraint grid thing)
  ;; A door has
  ;; - its bottom along the ground
  ;; - its left and right edges fully populated with inward log ends
  ;;     they must be fully populated and they must be inward log ends
  ;; - no grid points between left+1 and right-1 and top and bottom populated
  ;; - all grid points on the row above its top edge populated
  ;; - no grid point on the row above its top edge (except possibly the
  ;;   rightmost) populated with a right edge
  ;; - no grid point on the row above its top edge (except possibly the
  ;;   leftmost) populated with a left edge
  (or-constraint
   (if (and
	;; - its bottom along the ground
	(zero? (thing-bottom thing))
	(< (+ (thing-top thing) 2) (max-y grid)))
       (and-constraint
	;; - its left and right edges fully populated with inward log ends
	;;     they must be fully populated and they must be inward log ends
	(every-constraint
	 (lambda (y)
	  (and-constraint
	   (right-edge?-constraint
	    (at grid
		(make-grid-point (thing-left thing) y (thing-depth thing))))
	   (left-edge?-constraint
	    (at grid
		(make-grid-point (thing-right thing) y (thing-depth thing))))))
	 (from-to-by (thing-bottom thing) (thing-top thing) 2))
	;; - no grid points between left+1 and right-1 and top and bottom
	;;   populated
	(every-constraint
	 (lambda (x)
	  (every-constraint
	   (lambda (y)
	    (empty?-constraint
	     (at grid (make-grid-point x y (thing-depth thing)))))
	   (from-to-by (thing-bottom thing) (thing-top thing) 2)))
	 (from-to-by (+ (thing-left thing) 1) (- (thing-right thing) 1) 1))
	;; - all grid points on the row above its top edge populated
	(every-constraint
	 (lambda (x)
	  (not-constraint
	   (empty?-constraint
	    (at grid
		(make-grid-point
		 x (+ (thing-top thing) 2) (thing-depth thing))))))
	 (from-to-by (thing-left thing) (thing-right thing) 1))
	;; - no grid point on the row above its top edge (except possibly the
	;;   rightmost) populated with a right edge
	(every-constraint
	 (lambda (x)
	  (not-constraint
	   (right-edge?-constraint
	    (at grid
		(make-grid-point
		 x (+ (thing-top thing) 2) (thing-depth thing))))))
	 (from-to-by (thing-left thing) (- (thing-right thing) 1) 1))
	;; - no grid point on the row above its top edge (except possibly the
	;;   leftmost) populated with a left edge
	(every-constraint
	 (lambda (x)
	  (not-constraint
	   (left-edge?-constraint
	    (at grid
		(make-grid-point
		 x (+ (thing-top thing) 2) (thing-depth thing))))))
	 (from-to-by (+ (thing-left thing) 1) (thing-right thing) 1)))
       (false-domain-variable))
   (if (and
	;; - its bottom along the ground
	(= (thing-bottom thing) 1)
	(< (+ (thing-top thing) 2) (max-y grid)))
       (and-constraint
	;; - its left and right edges fully populated with inward log ends
	;;     they must be fully populated and they must be inward log ends
	(every-constraint
	 (lambda (y)
	  (and-constraint
	   (right-edge?-constraint
	    (at grid
		(make-grid-point (thing-depth thing) y (thing-left thing))))
	   (left-edge?-constraint
	    (at grid
		(make-grid-point (thing-depth thing) y (thing-right thing))))))
	 (from-to-by (thing-bottom thing) (thing-top thing) 2))
	;; - no grid points between left+1 and right-1 and top and bottom
	;;   populated
	(every-constraint
	 (lambda (z)
	  (every-constraint
	   (lambda (y)
	    (empty?-constraint
	     (at grid (make-grid-point (thing-depth thing) y z))))
	   (from-to-by (thing-bottom thing) (thing-top thing) 2)))
	 (from-to-by (+ (thing-left thing) 1) (- (thing-right thing) 1) 1))
	;; - all grid points on the row above its top edge populated
	(every-constraint
	 (lambda (z)
	  (not-constraint
	   (empty?-constraint
	    (at grid
		(make-grid-point
		 (thing-depth thing) (+ (thing-top thing) 2) z)))))
	 (from-to-by (thing-left thing) (thing-right thing) 1))
	;; - no grid point on the row above its top edge (except possibly the
	;;   rightmost) populated with a right edge
	(every-constraint
	 (lambda (z)
	  (not-constraint
	   (right-edge?-constraint
	    (at grid
		(make-grid-point
		 (thing-depth thing) (+ (thing-top thing) 2) z)))))
	 (from-to-by (thing-left thing) (- (thing-right thing) 1) 1))
	;; - no grid point on the row above its top edge (except possibly the
	;;   leftmost) populated with a left edge
	(every-constraint
	 (lambda (z)
	  (not-constraint
	   (left-edge?-constraint
	    (at grid
		(make-grid-point
		 (thing-depth thing) (+ (thing-top thing) 2) z)))))
	 (from-to-by (+ (thing-left thing) 1) (thing-right thing) 1)))
       (false-domain-variable))))

 (define (solid?-constraint grid thing)
  ;; A solid thing has
  ;; - every grid point between left and right and top and bottom populated
  ;; - no grid point between left and right-1 and top and bottom populated
  ;;   with a right-edge
  ;; - no grid point between left+1 and right and top and bottom populated
  ;;   with a left-edge
  (or-constraint
   (if (thing-xy? thing)
       (and-constraint
	;; - every grid point between left and right and top and bottom
	;;   populated
	(every-constraint
	 (lambda (x)
	  (every-constraint
	   (lambda (y)
	    (not-constraint
	     (empty?-constraint
	      (at grid (make-grid-point x y (thing-depth thing))))))
	   (from-to-by (thing-bottom thing) (thing-top thing) 2)))
	 (from-to-by (thing-left thing) (thing-right thing) 1))
	;; - no grid point between left and right-1 and top and bottom populated
	;;   with a right-edge
	(every-constraint
	 (lambda (x)
	  (every-constraint
	   (lambda (y)
	    (not-constraint
	     (right-edge?-constraint
	      (at grid (make-grid-point x y (thing-depth thing))))))
	   (from-to-by (thing-bottom thing) (thing-top thing) 2)))
	 (from-to-by (thing-left thing) (- (thing-right thing) 1) 1))
	;; - no grid point between left+1 and right and top and bottom populated
	;;   with a left-edge
	(every-constraint
	 (lambda (x)
	  (every-constraint
	   (lambda (y)
	    (not-constraint
	     (left-edge?-constraint
	      (at grid (make-grid-point x y (thing-depth thing))))))
	   (from-to-by (thing-bottom thing) (thing-top thing) 2)))
	 (from-to-by (+ (thing-left thing) 1) (thing-right thing) 1)))
       (false-domain-variable))
   (if (thing-zy? thing)
       (and-constraint
	;; - every grid point between left and right and top and bottom
	;;   populated
	(every-constraint
	 (lambda (z)
	  (every-constraint
	   (lambda (y)
	    (not-constraint
	     (empty?-constraint
	      (at grid (make-grid-point (thing-depth thing) y z)))))
	   (from-to-by (thing-bottom thing) (thing-top thing) 2)))
	 (from-to-by (thing-left thing) (thing-right thing) 1))
	;; - no grid point between left and right-1 and top and bottom populated
	;;   with a right-edge
	(every-constraint
	 (lambda (z)
	  (every-constraint
	   (lambda (y)
	    (not-constraint
	     (right-edge?-constraint
	      (at grid (make-grid-point (thing-depth thing) y z)))))
	   (from-to-by (thing-bottom thing) (thing-top thing) 2)))
	 (from-to-by (thing-left thing) (- (thing-right thing) 1) 1))
	;; - no grid point between left+1 and right and top and bottom populated
	;;   with a left-edge
	(every-constraint
	 (lambda (z)
	  (every-constraint
	   (lambda (y)
	    (not-constraint
	     (left-edge?-constraint
	      (at grid (make-grid-point (thing-depth thing) y z)))))
	   (from-to-by (thing-bottom thing) (thing-top thing) 2)))
	 (from-to-by (+ (thing-left thing) 1) (thing-right thing) 1)))
       (false-domain-variable))))

 (define (parse-type type)
  (cond ((eq? type 'boolean) 'boolean)
	((eq? type 'thing) 'thing)
	((and (list? type) (= (length type) 3) (eq? (first type) '->))
	 (make-arrow-type
	  (parse-type (second type)) (parse-type (third type))))
	((and (list? type) (= (length type) 3) (eq? (first type) '<=))
	 (make-leftward-arrow-type
	  (parse-type (second type)) (parse-type (third type))))
	((and (list? type) (= (length type) 3) (eq? (first type) '=>))
	 (make-rightward-arrow-type
	  (parse-type (second type)) (parse-type (third type))))
	(else (error #f "Bad type"))))

 (define (pretty-type type)
  (cond ((equal-type? type 'boolean) 'boolean)
	((equal-type? type 'thing) 'thing)
	((arrow-type? type)
	 `(-> ,(pretty-type (arrow-type-argument type))
	      ,(pretty-type (arrow-type-result type))))
	((leftward-arrow-type? type)
	 `(<= ,(pretty-type (leftward-arrow-type-result type))
	      ,(pretty-type (leftward-arrow-type-argument type))))
	((rightward-arrow-type? type)
	 `(=> ,(pretty-type (rightward-arrow-type-argument type))
	      ,(pretty-type (rightward-arrow-type-result type))))
	(else (fuck-up))))

 (define (parse-expression expression type)
  (let loop ((expression expression) (type type) (variables '()) (types '()))
   (cond
    ((memq expression variables)
     (make-variable-access-expression
      expression (list-ref types (positionq expression variables))))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'lambda)
	  (list? (second expression))
	  (= (length (second expression)) 1)
	  (symbol? (first (second expression))))
     (unless (arrow-type? type)
      (error #f "lambda expression not of arrow type"))
     (let* ((variable (first (second expression)))
	    (expression (loop (third expression)
			      (arrow-type-result type)
			      (cons (first (second expression)) variables)
			      (cons (arrow-type-argument type) types)))
	    (free-variables (removeq variable (free-variables expression))))
      (make-lambda-expression
       variable
       expression
       free-variables
       (map (lambda (variable) (list-ref types (positionq variable variables)))
	    free-variables)
       type)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'llambda)
	  (list? (second expression))
	  (= (length (second expression)) 1)
	  (symbol? (first (second expression))))
     (unless (leftward-arrow-type? type)
      (error #f "llambda expression not of leftward arrow type"))
     (let* ((variable (first (second expression)))
	    (expression (loop (third expression)
			      (leftward-arrow-type-result type)
			      (cons (first (second expression)) variables)
			      (cons (leftward-arrow-type-argument type)
				    types)))
	    (free-variables (removeq variable (free-variables expression))))
      (make-llambda-expression
       variable
       expression
       free-variables
       (map (lambda (variable) (list-ref types (positionq variable variables)))
	    free-variables)
       type)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'rlambda)
	  (list? (second expression))
	  (= (length (second expression)) 1)
	  (symbol? (first (second expression))))
     (unless (rightward-arrow-type? type)
      (error #f "rlambda expression not of rightward arrow type"))
     (let* ((variable (first (second expression)))
	    (expression (loop (third expression)
			      (rightward-arrow-type-result type)
			      (cons (first (second expression)) variables)
			      (cons (rightward-arrow-type-argument type)
				    types)))
	    (free-variables (removeq variable (free-variables expression))))
      (make-rlambda-expression
       variable
       expression
       free-variables
       (map (lambda (variable) (list-ref types (positionq variable variables)))
	    free-variables)
       type)))
    ((and (list? expression)
	  (>= (length expression) 1)
	  (eq? (first expression) 'and))
     (unless (equal-type? type 'boolean)
      (error #f "and expression not of type boolean"))
     (make-and-expression
      (map (lambda (expression) (loop expression 'boolean variables types))
	   (rest expression))))
    ((and (list? expression)
	  (>= (length expression) 1)
	  (eq? (first expression) 'or))
     (unless (equal-type? type 'boolean)
      (error #f "or expression not of type boolean"))
     (make-or-expression
      (map (lambda (expression) (loop expression 'boolean variables types))
	   (rest expression))))
    ((and (list? expression)
	  (= (length expression) 2)
	  (eq? (first expression) 'not))
     (unless (equal-type? type 'boolean)
      (error #f "not expression not of type boolean"))
     (make-not-expression (loop (second expression) 'boolean variables types)))
    ((and (list? expression)
	  (= (length expression) 2)
	  (eq? (first expression) 'some))
     (unless (equal-type? type 'boolean)
      (error #f "some expression not of type boolean"))
     (make-some-expression
      (loop
       (second expression) (make-arrow-type 'thing 'boolean) variables types)))
    ((and (list? expression)
	  (= (length expression) 2)
	  (eq? (first expression) 'every))
     (unless (equal-type? type 'boolean)
      (error #f "every expression not of type boolean"))
     (make-every-expression
      (loop
       (second expression) (make-arrow-type 'thing 'boolean) variables types)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'at-least)
	  (integer? (second expression))
	  (exact? (second expression)))
     (unless (equal-type? type 'boolean)
      (error #f "at-least expression not of type boolean"))
     (make-at-least-expression
      (second expression)
      (loop
       (third expression) (make-arrow-type 'thing 'boolean) variables types)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'at-most)
	  (integer? (second expression))
	  (exact? (second expression)))
     (unless (equal-type? type 'boolean)
      (error #f "at-most expression not of type boolean"))
     (make-at-most-expression
      (second expression)
      (loop
       (third expression) (make-arrow-type 'thing 'boolean) variables types)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'exactly)
	  (integer? (second expression))
	  (exact? (second expression)))
     (unless (equal-type? type 'boolean)
      (error #f "exactly expression not of type boolean"))
     (make-exactly-expression
      (second expression)
      (loop
       (third expression) (make-arrow-type 'thing 'boolean) variables types)))
    ((and (list? expression)
	  (= (length expression) 2)
	  (eq? (first expression) 'wall?))
     (unless (equal-type? type 'boolean)
      (error #f "wall? expression not of type boolean"))
     (make-wall?-expression (loop (second expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 2)
	  (eq? (first expression) 'window?))
     (unless (equal-type? type 'boolean)
      (error #f "window? expression not of type boolean"))
     (make-window?-expression
      (loop (second expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 2)
	  (eq? (first expression) 'door?))
     (unless (equal-type? type 'boolean)
      (error #f "door? expression not of type boolean"))
     (make-door?-expression (loop (second expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 2)
	  (eq? (first expression) 'solid?))
     (unless (equal-type? type 'boolean)
      (error #f "solid? expression not of type boolean"))
     (make-solid?-expression (loop (second expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'width=?)
	  (integer? (third expression))
	  (exact? (third expression)))
     (unless (equal-type? type 'boolean)
      (error #f "width=? expression not of type boolean"))
     (make-width=?-expression
      (loop (second expression) 'thing variables types) (third expression)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'height=?)
	  (integer? (third expression))
	  (exact? (third expression)))
     (unless (equal-type? type 'boolean)
      (error #f "height=? expression not of type boolean"))
     (make-height=?-expression
      (loop (second expression) 'thing variables types) (third expression)))

    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'left-of?))
     (unless (equal-type? type 'boolean)
      (error #f "left-of? expression not of type boolean"))
     (make-left-of?-expression
      (loop (second expression) 'thing variables types)
      (loop (third expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'below?))
     (unless (equal-type? type 'boolean)
      (error #f "below? expression not of type boolean"))
     (make-below?-expression (loop (second expression) 'thing variables types)
			     (loop (third expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'perpendicular?))
     (unless (equal-type? type 'boolean)
      (error #f "perpendicular? expression not of type boolean"))
     (make-perpendicular?-expression
      (loop (second expression) 'thing variables types)
      (loop (third expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'inside?))
     (unless (equal-type? type 'boolean)
      (error #f "inside? expression not of type boolean"))
     (make-inside?-expression (loop (second expression) 'thing variables types)
			      (loop (third expression) 'thing variables types)))
    ((and (list? expression) (= (length expression) 3))
     ;; needs work: should do type inference
     (let ((callee-type (parse-type (third expression))))
      (unless (or (and (arrow-type? callee-type)
		       (equal-type? (arrow-type-result callee-type) type))
		  ;; needs work: because of "is"
		  (and (rightward-arrow-type? callee-type)
		       (equal-type? (rightward-arrow-type-result callee-type)
				    type)))
       (error #f "Type error"))
      (make-application
       (loop (first expression) callee-type variables types)
       (loop
	(second expression)
	((if (arrow-type? callee-type)
	     arrow-type-argument
	     ;; needs work: because of "is"
	     rightward-arrow-type-argument)
	 callee-type)
	variables types)
       type)))
    (else (error #f "Bad expression")))))

 (define (pretty-expression expression)
  (cond
   ((variable-access-expression? expression)
    (variable-access-expression-variable expression))
   ((lambda-expression? expression)
    `(lambda (,(lambda-expression-variable expression))
      ,(pretty-expression (lambda-expression-expression expression))))
   ((llambda-expression? expression)
    `(llambda (,(llambda-expression-variable expression))
	      ,(pretty-expression (llambda-expression-expression expression))))
   ((rlambda-expression? expression)
    `(rlambda (,(rlambda-expression-variable expression))
	      ,(pretty-expression (rlambda-expression-expression expression))))
   ((and-expression? expression)
    `(and ,@(map pretty-expression (and-expression-expressions expression))))
   ((or-expression? expression)
    `(or ,@(map pretty-expression (or-expression-expressions expression))))
   ((not-expression? expression)
    `(not ,(pretty-expression (not-expression-expression expression))))
   ((some-expression? expression)
    `(some ,(pretty-expression (some-expression-expression expression))))
   ((every-expression? expression)
    `(every ,(pretty-expression (every-expression-expression expression))))
   ((at-least-expression? expression)
    `(at-least
      ,(at-least-expression-k expression)
      ,(pretty-expression (at-least-expression-expression expression))))
   ((at-most-expression? expression)
    `(at-most
      ,(at-most-expression-k expression)
      ,(pretty-expression (at-most-expression-expression expression))))
   ((exactly-expression? expression)
    `(exactly
      ,(exactly-expression-k expression)
      ,(pretty-expression (exactly-expression-expression expression))))
   ((wall?-expression? expression)
    `(wall? ,(pretty-expression (wall?-expression-expression expression))))
   ((window?-expression? expression)
    `(window? ,(pretty-expression (window?-expression-expression expression))))
   ((door?-expression? expression)
    `(door? ,(pretty-expression (door?-expression-expression expression))))
   ((solid?-expression? expression)
    `(solid? ,(pretty-expression (solid?-expression-expression expression))))
   ((width=?-expression? expression)
    `(width=? ,(pretty-expression (width=?-expression-expression expression))
	      ,(width=?-expression-k expression)))
   ((height=?-expression? expression)
    `(height=? ,(pretty-expression (height=?-expression-expression expression))
	       ,(height=?-expression-k expression)))
   ((left-of?-expression? expression)
    `(left-of?
      ,(pretty-expression (left-of?-expression-expression1 expression))
      ,(pretty-expression (left-of?-expression-expression2 expression))))
   ((below?-expression? expression)
    `(below? ,(pretty-expression (below?-expression-expression1 expression))
	     ,(pretty-expression (below?-expression-expression2 expression))))
   ((perpendicular?-expression? expression)
    `(perpendicular?
      ,(pretty-expression (perpendicular?-expression-expression1 expression))
      ,(pretty-expression (perpendicular?-expression-expression2 expression))))
   ((inside?-expression? expression)
    `(inside?
      ,(pretty-expression (inside?-expression-expression1 expression))
      ,(pretty-expression (inside?-expression-expression2 expression))))
   ((application? expression)
    `(,(pretty-expression (application-callee expression))
      ,(pretty-expression (application-argument expression))))
   (else (fuck-up))))

 (define (pretty-value value)
  (cond ((boolean? value) value)
	((closure? value)
	 (cons 'closure (pretty-environment (closure-environment value))))
	(else value)))

 (define (pretty-environment environment)
  (map
   (lambda (binding)
    (list (binding-variable binding) (pretty-value (binding-value binding))))
   environment))

 (define (type expression)
  (cond ((variable-access-expression? expression)
	 (variable-access-expression-type expression))
	((lambda-expression? expression) (lambda-expression-type expression))
	((llambda-expression? expression) (llambda-expression-type expression))
	((rlambda-expression? expression) (rlambda-expression-type expression))
	((and-expression? expression) 'boolean)
	((or-expression? expression) 'boolean)
	((not-expression? expression) 'boolean)
	((some-expression? expression) 'boolean)
	((every-expression? expression) 'boolean)
	((at-least-expression? expression) 'boolean)
	((at-most-expression? expression) 'boolean)
	((exactly-expression? expression) 'boolean)
	((wall?-expression? expression) 'boolean)
	((window?-expression? expression) 'boolean)
	((door?-expression? expression) 'boolean)
	((solid?-expression? expression) 'boolean)
	((height=?-expression? expression) 'boolean)
	((width=?-expression? expression) 'boolean)
	((left-of?-expression? expression) 'boolean)
	((below?-expression? expression) 'boolean)
	((perpendicular?-expression? expression) 'boolean)
	((inside?-expression? expression) 'boolean)
	((application? expression) (application-type expression))
	(else (fuck-up))))

 (define (free-variables expression)
  (cond
   ((variable-access-expression? expression)
    (list (variable-access-expression-variable expression)))
   ((lambda-expression? expression) (lambda-expression-variables expression))
   ((llambda-expression? expression) (llambda-expression-variables expression))
   ((rlambda-expression? expression) (rlambda-expression-variables expression))
   ((and-expression? expression)
    (map-reduce
     unionq '() free-variables (and-expression-expressions expression)))
   ((or-expression? expression)
    (map-reduce
     unionq '() free-variables (or-expression-expressions expression)))
   ((not-expression? expression)
    (free-variables (not-expression-expression expression)))
   ((some-expression? expression)
    (free-variables (some-expression-expression expression)))
   ((every-expression? expression)
    (free-variables (every-expression-expression expression)))
   ((at-least-expression? expression)
    (free-variables (at-least-expression-expression expression)))
   ((at-most-expression? expression)
    (free-variables (at-most-expression-expression expression)))
   ((exactly-expression? expression)
    (free-variables (exactly-expression-expression expression)))
   ((wall?-expression? expression)
    (free-variables (wall?-expression-expression expression)))
   ((window?-expression? expression)
    (free-variables (window?-expression-expression expression)))
   ((door?-expression? expression)
    (free-variables (door?-expression-expression expression)))
   ((solid?-expression? expression)
    (free-variables (solid?-expression-expression expression)))
   ((width=?-expression? expression)
    (free-variables (width=?-expression-expression expression)))
   ((height=?-expression? expression)
    (free-variables (height=?-expression-expression expression)))
   ((left-of?-expression? expression)
    (unionq (free-variables (left-of?-expression-expression1 expression))
	    (free-variables (left-of?-expression-expression2 expression))))
   ((below?-expression? expression)
    (unionq (free-variables (below?-expression-expression1 expression))
	    (free-variables (below?-expression-expression2 expression))))
   ((perpendicular?-expression? expression)
    (unionq
     (free-variables (perpendicular?-expression-expression1 expression))
     (free-variables (perpendicular?-expression-expression2 expression))))
   ((inside?-expression? expression)
    (unionq (free-variables (inside?-expression-expression1 expression))
	    (free-variables (inside?-expression-expression2 expression))))
   ((application? expression)
    (unionq (free-variables (application-callee expression))
	    (free-variables (application-argument expression))))
   (else (fuck-up))))

 (define (equal-type? type1 type2)
  (or (eq? type1 type2)
      (and (arrow-type? type1)
	   (arrow-type? type2)
	   (equal-type? (arrow-type-argument type1) (arrow-type-argument type2))
	   (equal-type? (arrow-type-result type1) (arrow-type-result type2)))
      (and (leftward-arrow-type? type1)
	   (leftward-arrow-type? type2)
	   (equal-type? (leftward-arrow-type-argument type1)
			(leftward-arrow-type-argument type2))
	   (equal-type? (leftward-arrow-type-result type1)
			(leftward-arrow-type-result type2)))
      (and (rightward-arrow-type? type1)
	   (rightward-arrow-type? type2)
	   (equal-type? (rightward-arrow-type-argument type1)
			(rightward-arrow-type-argument type2))
	   (equal-type? (rightward-arrow-type-result type1)
			(rightward-arrow-type-result type2)))))

 (define (equal-value? value1 value2)
  (or (eq? value1 value2)
      ;; needs work
      (and
       (closure? value1)
       (closure? value2)
       (eq? (closure-expression value1) (closure-expression value2))
       (every
	(lambda (binding1 binding2)
	 (unless (eq? (binding-variable binding1) (binding-variable binding2))
	  (fuck-up))
	 (equal-value? (binding-value binding1) (binding-value binding2)))
	(closure-environment value1)
	(closure-environment value2)))))

 (define (create-typed-meaning type expression)
  (let* ((type (parse-type type))
	 (expression (parse-expression expression type)))
   (unless (or (and (lambda-expression? expression)
		    (null? (lambda-expression-variables expression)))
	       (and (llambda-expression? expression)
		    (null? (llambda-expression-variables expression)))
	       (and (rlambda-expression? expression)
		    (null? (rlambda-expression-variables expression))))
    (fuck-up))
   (make-typed-meaning type expression)))

 (define (evaluate expression environment grid)
  ;; needs work: to memoize on expression and environment and limit size of
  ;;             environment
  (cond
   ((variable-access-expression? expression)
    (binding-value
     (find-if (lambda (binding)
	       (eq? (binding-variable binding)
		    (variable-access-expression-variable expression)))
	      environment)))
   ((lambda-expression? expression)
    (make-closure
     (remove-if-not (lambda (binding)
		     (memq (binding-variable binding)
			   (lambda-expression-variables expression)))
		    environment)
     expression))
   ((llambda-expression? expression)
    (make-closure
     (remove-if-not (lambda (binding)
		     (memq (binding-variable binding)
			   (llambda-expression-variables expression)))
		    environment)
     expression))
   ((rlambda-expression? expression)
    (make-closure
     (remove-if-not (lambda (binding)
		     (memq (binding-variable binding)
			   (rlambda-expression-variables expression)))
		    environment)
     expression))
   ((and-expression? expression)
    (every-constraint
     (lambda (expression) (evaluate expression environment grid))
     (and-expression-expressions expression)))
   ((or-expression? expression)
    (some-constraint
     (lambda (expression) (evaluate expression environment grid))
     (or-expression-expressions expression)))
   ((not-expression? expression)
    (not-constraint
     (evaluate (not-expression-expression expression) environment grid)))
   ((some-expression? expression)
    (let ((value
	   (evaluate (some-expression-expression expression) environment grid)))
     (some-constraint (lambda (thing) (call value thing grid)) (things grid))))
   ((every-expression? expression)
    (let ((value (evaluate
		  (every-expression-expression expression) environment grid)))
     (every-constraint (lambda (thing) (call value thing grid)) (things grid))))
   ((at-least-expression? expression)
    (let ((value
	   (evaluate
	    (at-least-expression-expression expression) environment grid)))
     (at-least-constraint (at-least-expression-k expression)
			  (lambda (thing) (call value thing grid))
			  (things grid))))
   ((at-most-expression? expression)
    (let ((value
	   (evaluate
	    (at-most-expression-expression expression) environment grid)))
     (at-most-constraint (at-most-expression-k expression)
			 (lambda (thing) (call value thing grid))
			 (things grid))))
   ((exactly-expression? expression)
    (let ((value
	   (evaluate
	    (exactly-expression-expression expression) environment grid)))
     (exactly-constraint (exactly-expression-k expression)
			 (lambda (thing) (call value thing grid))
			 (things grid))))
   ((wall?-expression? expression)
    (wall?-constraint
     grid
     (evaluate (wall?-expression-expression expression) environment grid)))
   ((window?-expression? expression)
    (window?-constraint
     grid
     (evaluate (window?-expression-expression expression) environment grid)))
   ((door?-expression? expression)
    (door?-constraint
     grid
     (evaluate (door?-expression-expression expression) environment grid)))
   ((solid?-expression? expression)
    (solid?-constraint
     grid
     (evaluate (solid?-expression-expression expression) environment grid)))
   ((width=?-expression? expression)
    (if (= (thing-width
	    (evaluate
	     (width=?-expression-expression expression) environment grid))
	   (width=?-expression-k expression))
	(true-domain-variable)
	(false-domain-variable)))
   ((height=?-expression? expression)
    (if (= (thing-height
	    (evaluate
	     (height=?-expression-expression expression) environment grid))
	   (height=?-expression-k expression))
	(true-domain-variable)
	(false-domain-variable)))
   ((left-of?-expression? expression)
    (if (thing-left-of?
	 (evaluate
	  (left-of?-expression-expression1 expression) environment grid)
	 (evaluate
	  (left-of?-expression-expression2 expression) environment grid))
	(true-domain-variable)
	(false-domain-variable)))
   ((below?-expression? expression)
    (if (thing-below?
	 (evaluate
	  (below?-expression-expression1 expression) environment grid)
	 (evaluate
	  (below?-expression-expression2 expression) environment grid))
	(true-domain-variable)
	(false-domain-variable)))
   ((perpendicular?-expression? expression)
    (if (thing-perpendicular?
	 (evaluate
	  (perpendicular?-expression-expression1 expression) environment grid)
	 (evaluate
	  (perpendicular?-expression-expression2 expression) environment grid))
	(true-domain-variable)
	(false-domain-variable)))
   ((inside?-expression? expression)
    (if (thing-inside?
	 (evaluate
	  (inside?-expression-expression1 expression) environment grid)
	 (evaluate
	  (inside?-expression-expression2 expression) environment grid))
	(true-domain-variable)
	(false-domain-variable)))
   ((application? expression)
    (call (evaluate (application-callee expression) environment grid)
	  (evaluate (application-argument expression) environment grid)
	  grid))
   (else (fuck-up))))

 (define (call callee-value argument-value grid)
  (cond ((lambda-expression? (closure-expression callee-value))
	 (evaluate
	  (lambda-expression-expression (closure-expression callee-value))
	  (cons (make-binding
		 (lambda-expression-variable (closure-expression callee-value))
		 argument-value)
		(closure-environment callee-value))
	  grid))
	((llambda-expression? (closure-expression callee-value))
	 (evaluate
	  (llambda-expression-expression (closure-expression callee-value))
	  (cons (make-binding
		 (llambda-expression-variable (closure-expression callee-value))
		 argument-value)
		(closure-environment callee-value))
	  grid))
	((rlambda-expression? (closure-expression callee-value))
	 (evaluate
	  (rlambda-expression-expression (closure-expression callee-value))
	  (cons (make-binding
		 (rlambda-expression-variable (closure-expression callee-value))
		 argument-value)
		(closure-environment callee-value))
	  grid))
	(else (fuck-up))))

 (define *s* 'boolean)

 (define *n* '(-> thing boolean))

 (define *np* `(-> ,*n* boolean))

 (define *d* `(=> ,*n* ,*np*))

 (define *a* `(=> ,*n* ,*n*))

 (define *vp* `(<= ,*s* ,*np*))

 (define *v* *vp*)

 (define *v-np* `(=> ,*np* ,*vp*))

 (define *v-a* `(=> ,*a* ,*vp*))

 (define *lexicon*
  (list
   (cons 'some
	 (create-typed-meaning
	  *d*
	  '(rlambda (noun1)
		    (lambda (noun2)
		     (some (lambda (thing)
			    (and (noun1 thing (-> thing boolean))
				 (noun2 thing (-> thing boolean)))))))))
   (cons 'every
	 (create-typed-meaning
	  *d*
	  '(rlambda (noun1)
		    (lambda (noun2)
		     (every (lambda (thing)
			     (or (not (noun1 thing (-> thing boolean)))
				 (noun2 thing (-> thing boolean)))))))))
   (cons 'one
	 (create-typed-meaning
	  *d*
	  '(rlambda (noun1)
		    (lambda (noun2)
		     (exactly
		      1
		      (lambda (thing)
		       (and (noun1 thing (-> thing boolean))
			    (noun2 thing (-> thing boolean)))))))))
   (cons 'two
	 (create-typed-meaning
	  *d*
	  '(rlambda (noun1)
		    (lambda (noun2)
		     (exactly
		      2
		      (lambda (thing)
		       (and (noun1 thing (-> thing boolean))
			    (noun2 thing (-> thing boolean)))))))))
   (cons 'three
	 (create-typed-meaning
	  *d*
	  '(rlambda (noun1)
		    (lambda (noun2)
		     (exactly
		      3
		      (lambda (thing)
		       (and (noun1 thing (-> thing boolean))
			    (noun2 thing (-> thing boolean)))))))))
   (cons 'four
	 (create-typed-meaning
	  *d*
	  '(rlambda (noun1)
		    (lambda (noun2)
		     (exactly
		      4
		      (lambda (thing)
		       (and (noun1 thing (-> thing boolean))
			    (noun2 thing (-> thing boolean)))))))))
   (cons 'five
	 (create-typed-meaning
	  *d*
	  '(rlambda (noun1)
		    (lambda (noun2)
		     (exactly
		      5
		      (lambda (thing)
		       (and (noun1 thing (-> thing boolean))
			    (noun2 thing (-> thing boolean)))))))))
   (cons 'six
	 (create-typed-meaning
	  *d*
	  '(rlambda (noun1)
		    (lambda (noun2)
		     (exactly
		      6
		      (lambda (thing)
		       (and (noun1 thing (-> thing boolean))
			    (noun2 thing (-> thing boolean)))))))))
   (cons 'seven
	 (create-typed-meaning
	  *d*
	  '(rlambda (noun1)
		    (lambda (noun2)
		     (exactly
		      7
		      (lambda (thing)
		       (and (noun1 thing (-> thing boolean))
			    (noun2 thing (-> thing boolean)))))))))
   (cons 'wall (create-typed-meaning *n* '(lambda (thing) (wall? thing))))
   (cons 'window (create-typed-meaning *n* '(lambda (thing) (window? thing))))
   (cons 'door (create-typed-meaning *n* '(lambda (thing) (door? thing))))
   (cons 'solid
	 (create-typed-meaning
	  *a*
	  '(rlambda (noun)
		    (lambda (thing)
		     (and (noun thing (-> thing boolean)) (solid? thing))))))
   ;; lexicalization
   (cons
    'one-high
    (create-typed-meaning
     *a*
     '(rlambda (noun)
	       (lambda (thing)
		(and (noun thing (-> thing boolean)) (height=? thing 1))))))
   ;; lexicalization
   (cons
    'two-high
    (create-typed-meaning
     *a*
     '(rlambda (noun)
	       (lambda (thing)
		(and (noun thing (-> thing boolean)) (height=? thing 2))))))
   ;; lexicalization
   (cons
    'three-high
    (create-typed-meaning
     *a*
     '(rlambda (noun)
	       (lambda (thing)
		(and (noun thing (-> thing boolean)) (height=? thing 3))))))
   ;; lexicalization
   (cons 'one-wide
	 (create-typed-meaning
	  *a*
	  '(rlambda (noun)
		    (lambda (thing)
		     (and (noun thing (-> thing boolean)) (width=? thing 1))))))
   ;; lexicalization
   (cons 'two-wide
	 (create-typed-meaning
	  *a*
	  '(rlambda (noun)
		    (lambda (thing)
		     (and (noun thing (-> thing boolean)) (width=? thing 2))))))
   ;; lexicalization
   (cons 'three-wide
	 (create-typed-meaning
	  *a*
	  '(rlambda (noun)
		    (lambda (thing)
		     (and (noun thing (-> thing boolean)) (width=? thing 3))))))
   (cons 'exists
	 (create-typed-meaning
	  *v*
	  '(llambda (np1)
		    (np1 (lambda (thing) (and))
			 (-> (-> thing boolean) boolean)))))
   (cons 'has
	 (create-typed-meaning
	  *v-np*
	  '(rlambda (np2)
		    (llambda (np1)
			     (np1 (lambda (thing1)
				   (np2 (lambda (thing2)
					 (inside? thing2 thing1))
					(-> (-> thing boolean) boolean)))
				  (-> (-> thing boolean) boolean))))))
   (cons 'has
	 (create-typed-meaning
	  *v-np*
	  '(rlambda (np2)
		    (llambda (np1)
			     (np2 (lambda (thing2)
				   (np1 (lambda (thing1)
					 (inside? thing2 thing1))
					(-> (-> thing boolean) boolean)))
				  (-> (-> thing boolean) boolean))))))
   ;; lexicalization
   (cons 'is-to-the-left-of
	 (create-typed-meaning
	  *v-np*
	  '(rlambda (np2)
		    (llambda (np1)
			     (np1 (lambda (thing1)
				   (np2 (lambda (thing2)
					 (left-of? thing1 thing2))
					(-> (-> thing boolean) boolean)))
				  (-> (-> thing boolean) boolean))))))
   ;; lexicalization
   (cons 'is-to-the-left-of
	 (create-typed-meaning
	  *v-np*
	  '(rlambda (np2)
		    (llambda (np1)
			     (np2 (lambda (thing2)
				   (np1 (lambda (thing1)
					 (left-of? thing1 thing2))
					(-> (-> thing boolean) boolean)))
				  (-> (-> thing boolean) boolean))))))
   ;; lexicalization
   (cons 'is-to-the-right-of
	 (create-typed-meaning
	  *v-np*
	  '(rlambda (np2)
		    (llambda (np1)
			     (np1 (lambda (thing1)
				   (np2 (lambda (thing2)
					 (left-of? thing2 thing1))
					(-> (-> thing boolean) boolean)))
				  (-> (-> thing boolean) boolean))))))
   ;; lexicalization
   (cons 'is-to-the-right-of
	 (create-typed-meaning
	  *v-np*
	  '(rlambda (np2)
		    (llambda (np1)
			     (np2 (lambda (thing2)
				   (np1 (lambda (thing1)
					 (left-of? thing2 thing1))
					(-> (-> thing boolean) boolean)))
				  (-> (-> thing boolean) boolean))))))
   ;; lexicalization
   (cons 'is-below
	 (create-typed-meaning
	  *v-np*
	  '(rlambda (np2)
		    (llambda (np1)
			     (np1 (lambda (thing1)
				   (np2 (lambda (thing2)
					 (below? thing1 thing2))
					(-> (-> thing boolean) boolean)))
				  (-> (-> thing boolean) boolean))))))
   ;; lexicalization
   (cons 'is-below
	 (create-typed-meaning
	  *v-np*
	  '(rlambda (np2)
		    (llambda (np1)
			     (np2 (lambda (thing2)
				   (np1 (lambda (thing1)
					 (below? thing1 thing2))
					(-> (-> thing boolean) boolean)))
				  (-> (-> thing boolean) boolean))))))
   ;; lexicalization
   (cons 'is-above
	 (create-typed-meaning
	  *v-np*
	  '(rlambda (np2)
		    (llambda (np1)
			     (np1 (lambda (thing1)
				   (np2 (lambda (thing2)
					 (below? thing2 thing1))
					(-> (-> thing boolean) boolean)))
				  (-> (-> thing boolean) boolean))))))
   ;; lexicalization
   (cons 'is-above
	 (create-typed-meaning
	  *v-np*
	  '(rlambda (np2)
		    (llambda (np1)
			     (np2 (lambda (thing2)
				   (np1 (lambda (thing1)
					 (below? thing2 thing1))
					(-> (-> thing boolean) boolean)))
				  (-> (-> thing boolean) boolean))))))
   ;; lexicalization
   (cons 'is-perpendicular-to
	 (create-typed-meaning
	  *v-np*
	  '(rlambda (np2)
		    (llambda (np1)
			     (np1 (lambda (thing1)
				   (np2 (lambda (thing2)
					 (perpendicular? thing1 thing2))
					(-> (-> thing boolean) boolean)))
				  (-> (-> thing boolean) boolean))))))
   ;; lexicalization
   (cons 'is-perpendicular-to
	 (create-typed-meaning
	  *v-np*
	  '(rlambda (np2)
		    (llambda (np1)
			     (np2 (lambda (thing2)
				   (np1 (lambda (thing1)
					 (perpendicular? thing1 thing2))
					(-> (-> thing boolean) boolean)))
				  (-> (-> thing boolean) boolean))))))
   (cons 'is
	 (create-typed-meaning
	  *v-a*
	  '(rlambda (a)
		    (llambda (np)
			     (np (lambda (thing)
				  ((a
				    (lambda (thing) (and))
				    (=> (-> thing boolean) (-> thing boolean)))
				   thing
				   (-> thing boolean)))
				 (-> (-> thing boolean) boolean))))))))

 (define (a-typed-apply left right grid)
  (amb (if (and (leftward-arrow-type? (typed-meaning-type right))
		(equal-type?
		 (typed-meaning-type left)
		 (leftward-arrow-type-argument (typed-meaning-type right))))
	   (make-typed-meaning
	    (leftward-arrow-type-result (typed-meaning-type right))
	    (call (typed-meaning-meaning right)
		  (typed-meaning-meaning left)
		  grid))
	   (fail))
       (if (and (rightward-arrow-type? (typed-meaning-type left))
		(equal-type?
		 (typed-meaning-type right)
		 (rightward-arrow-type-argument (typed-meaning-type left))))
	   (make-typed-meaning
	    (rightward-arrow-type-result (typed-meaning-type left))
	    (call (typed-meaning-meaning left)
		  (typed-meaning-meaning right)
		  grid))
	   (fail))))

 (define (a-meaning-constraint words grid)
  (let ((typed-meaning
	 (let loop ((words words))
	  (if (= (length words) 1)
	      (let ((lexical-entry (a-member-of *lexicon*)))
	       (unless (eq? (first words) (car lexical-entry)) (fail))
	       (make-typed-meaning
		(typed-meaning-type (cdr lexical-entry))
		(evaluate (typed-meaning-meaning (cdr lexical-entry))
			  '()
			  grid)))
	      (let ((i (+ (a-member-of (enumerate (- (length words) 1))) 1)))
	       (a-typed-apply (loop (sublist words 0 i))
			      (loop (sublist words i (length words)))
			      grid))))))
   (unless (eq? (typed-meaning-type typed-meaning) 'boolean) (fail))
   (typed-meaning-meaning typed-meaning)))

 (define (create-word-variable)
  (create-domain-variable (remove-duplicates (map car *lexicon*))))

 (define (create-type-variable)
  (create-domain-variable
   (cons #f
	 (remove-duplicatesp
	  equal-type?
	  (map-reduce append
		      '()
		      (lambda (entry)
		       (let loop ((type (typed-meaning-type (cdr entry))))
			(cons type
			      (cond ((arrow-type? type)
				     (loop (arrow-type-result type)))
				    ((leftward-arrow-type? type)
				     (loop (leftward-arrow-type-result type)))
				    ((rightward-arrow-type? type)
				     (loop (rightward-arrow-type-result type)))
				    (else '())))))
		      *lexicon*)))))

 (define (make-upper-triangular-matrix n initializer)
  (list->vector
   (map-n
    (lambda (i) (list->vector (map-n (lambda (j) (initializer)) (- n i 1))))
    n)))

 (define (upper-triangular-matrix-ref m i j)
  (vector-ref (vector-ref m i) (- j i 1)))

 (define (constraints words)
  (let* ((n (+ (length words) 1))
	 (type (make-upper-triangular-matrix n create-type-variable)))
   (do ((i 0 (+ i 1))) ((= i (- n 1)))
    (assert-nondeterministic-constraint!
     (lambda (type word)
      (some (lambda (entry)
	     (and (eq? (car entry) word)
		  (equal-type? (typed-meaning-type (cdr entry)) type)))
	    *lexicon*))
     (upper-triangular-matrix-ref type i (+ i 1))
     (list-ref words i)))
   (do ((i 0 (+ i 1))) ((= i (- n 2)))
    (do ((k (+ i 2) (+ k 1))) ((= k n))
     (apply assert-nondeterministic-constraint!
	    (lambda (type . types)
	     (or (not type)
		 (some (lambda (left right) (and left right))
		       (sublist types 0 (/ (length types) 2))
		       (sublist types (/ (length types) 2) (length types)))))
	    (upper-triangular-matrix-ref type i k)
	    (append
	     (map-n (lambda (j) (upper-triangular-matrix-ref type i (+ i j 1)))
		    (- k i 1))
	     (map-n (lambda (j) (upper-triangular-matrix-ref type (+ i j 1) k))
		    (- k i 1))))))
   (do ((i 0 (+ i 1))) ((= i (- n 2)))
    (do ((j (+ i 1) (+ j 1))) ((= j (- n 1)))
     (do ((k (+ j 1) (+ k 1))) ((= k n))
      (assert-nondeterministic-constraint!
       (lambda (parent left right)
	(or (not parent)
	    (not left)
	    (not right)
	    (and (leftward-arrow-type? right)
		 (equal-type? left (leftward-arrow-type-argument right))
		 (equal-type? parent (leftward-arrow-type-result right)))
	    (and (rightward-arrow-type? left)
		 (equal-type? right (rightward-arrow-type-argument left))
		 (equal-type? parent (rightward-arrow-type-result left)))))
       (upper-triangular-matrix-ref type i k)
       (upper-triangular-matrix-ref type i j)
       (upper-triangular-matrix-ref type j k)))))
   (assert-nondeterministic-constraint!
    (lambda (type) (eq? type 'boolean))
    (upper-triangular-matrix-ref type 0 (- n 1)))
   type))

 (define (all-domain-variables type)
  (map-reduce append '() vector->list (vector->list type)))

 (define (all-sentences n)
  (domain (let* ((words (map-n (lambda (i) (create-word-variable)) n))
		 (type (constraints words)))
	   (nondeterministic-solution
	    (append (all-domain-variables type) words))
	   (map nondeterministic-constraints:binding words)))))
