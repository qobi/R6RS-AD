#!r6rs

(import (rnrs)
	(QobiScheme)
	(nondeterministic-scheme)
	(nondeterministic-constraints)
	(nondeterministic-lifting)
	(wwd))

(define (write-grids x y z sentences)
 (set-nondeterministic-strategy! 'ac)
 (initialize-domain-variables!)
 (system "rm solution-*.logs")
 (domain
  (let ((i 0) (grid (create-grid x y z)))
   (assert-lincoln-log-grammar-constraints! grid)
   (for-each (lambda (sentence) (assert! (a-meaning-constraint sentence grid)))
	     sentences)
   (nondeterministic-solution (domain-variables))
   (write-grid grid (string-append "solution-" (number->string i) ".logs"))
   (set! i (+ i 1))
   (fail)))
 (system "./gui"))

(define (possibly-true? words grid)
 (initialize-domain-variables!)
 (call-with-current-continuation
  (lambda (return)
   (domain (let ((grid (lift-grid grid)))
	    (assert-lincoln-log-grammar-constraints! grid)
	    (assert! (a-meaning-constraint words grid))
	    (nondeterministic-solution (domain-variables))
	    (return #t)))
   #f)))

(define (all-grids x y z sentences)
 (domain (let ((grid (create-grid x y z)))
	  (assert-lincoln-log-grammar-constraints! grid)
	  (for-each
	   (lambda (sentence) (assert! (a-meaning-constraint sentence grid)))
	   sentences)
	  (nondeterministic-solution (domain-variables))
	  (grid-binding grid))))

(define (first-grid x y z sentences)
 (set-nondeterministic-strategy! 'ac)
 (initialize-domain-variables!)
 (call-with-current-continuation
  (lambda (return)
   (domain (let ((grid (create-grid x y z)))
	    (assert-lincoln-log-grammar-constraints! grid)
	    (for-each
	     (lambda (sentence) (assert! (a-meaning-constraint sentence grid)))
	     sentences)
	    (nondeterministic-solution (domain-variables))
	    (return (grid-binding grid))))
   #f)))

(define (all-grids-capped n x y z sentences)
 (initialize-domain-variables!)
 (call-with-current-continuation
  (lambda (return)
   (domain (let ((grid (create-grid x y z)) (grids '()))
	    (assert-lincoln-log-grammar-constraints! grid)
	    (for-each
	     (lambda (sentence) (assert! (a-meaning-constraint sentence grid)))
	     sentences)
	    (nondeterministic-solution (domain-variables))
	    (when (= (length grids) n) (return (reverse grids)))
	    (set! grids (cons (grid-binding grid) grids))
	    (grid-binding grid))))))

(define (all-true-sentences-of-length n grid)
 (remove-if-not (lambda (words) (possibly-true? words grid))
		(all-sentences n)))

(define (description n grid)
 (set-nondeterministic-strategy! 'ac)
 (initialize-domain-variables!)
 (call-with-current-continuation
  (lambda (return)
   (let loop ((candidates (all-true-sentences-of-length n grid))
	      (sentences '()))
    (let ((alternative
	   (map-reduce
	    (lambda (alternative1 alternative2)
	     (write (list alternative1 alternative2)) (newline) ;debugging
	     (when (= (second alternative2) 1) (return (first alternative2)))
	     (if (<= (second alternative1) (second alternative2))
		 alternative1
		 alternative2))
	    (list #f
		  (length (all-grids-capped 100
					    (max-x grid)
					    (max-y grid)
					    (max-z grid)
					    sentences)))
	    (lambda (candidate)
	     (write candidate) (newline) ;debugging
	     (list candidate
		   (length (all-grids-capped 100
					     (max-x grid)
					     (max-y grid)
					     (max-z grid)
					     (cons candidate sentences)))))
	    candidates)))
     (if (eq? (first alternative) #f)
	 sentences
	 (loop (removeq (first alternative) candidates)
	       (cons (first alternative) sentences))))))))

(define (description2 n grid)
 (set-nondeterministic-strategy! 'ac)
 (initialize-domain-variables!)
 (let loop ((candidates
	     (map-reduce-n
	      append
	      '()
	      (lambda (i) (all-true-sentences-of-length (+ i 1) grid))
	      n))
	    (keep '()))
  (cond ((null? candidates) keep)
	;; needs work: hardwired to 2; should be to duplicity in full set
	((= (length (all-grids-capped 2
				      (max-x grid) (max-y grid) (max-z grid)
				      (append (rest candidates) keep)))
	    2)
	 (write (list 'keep (first candidates))) (newline) ;debugging
	 (loop (rest candidates) (cons (first candidates) keep)))
	(else
	 (write (list 'drop (first candidates))) (newline) ;debugging
	 (loop (rest candidates) keep)))))

(define (test1)
 (set-nondeterministic-strategy! 'ac)
 (initialize-domain-variables!)
 (system "rm solution-*.logs")
 (domain
  (let ((i 0) (grid (create-grid 2 1 2)))
   (assert-lincoln-log-grammar-constraints! grid)
   (nondeterministic-solution (domain-variables))
   (write-grid grid (string-append "solution-" (number->string i) ".logs"))
   (set! i (+ i 1))
   (fail)))
 (system "./gui"))

(define (test2)
 (set-nondeterministic-strategy! 'ac)
 (initialize-domain-variables!)
 (system "rm solution-*.logs")
 (domain
  (let ((i 0) (grid (create-grid 1 4 1)))
   (assert-lincoln-log-grammar-constraints! grid)
   (nondeterministic-solution (domain-variables))
   (write-grid grid (string-append "solution-" (number->string i) ".logs"))
   (set! i (+ i 1))
   (fail)))
 (system "./gui"))

(define (test3)
 (set-nondeterministic-strategy! 'ac)
 (initialize-domain-variables!)
 (system "rm solution-*.logs")
 (domain
  (let ((i 0) (grid (create-grid 2 8 1)))
   (assert-lincoln-log-grammar-constraints! grid)
   (assert! (some-constraint
	     (lambda (thing) (wall?-constraint grid thing)) (things grid)))
   (nondeterministic-solution (domain-variables))
   (write-grid grid (string-append "solution-" (number->string i) ".logs"))
   (set! i (+ i 1))
   (fail)))
 (system "./gui"))

(define (test4)
 (set-nondeterministic-strategy! 'ac)
 (initialize-domain-variables!)
 (system "rm solution-*.logs")
 (domain
  (let ((i 0) (grid (create-grid 2 8 1)))
   (assert-lincoln-log-grammar-constraints! grid)
   (assert! (some-constraint
	     (lambda (thing) (window?-constraint grid thing)) (things grid)))
   (nondeterministic-solution (domain-variables))
   (write-grid grid (string-append "solution-" (number->string i) ".logs"))
   (set! i (+ i 1))
   (fail)))
 (system "./gui"))

(define (test5)
 (set-nondeterministic-strategy! 'ac)
 (initialize-domain-variables!)
 (system "rm solution-*.logs")
 (domain
  (let ((i 0) (grid (create-grid 2 8 1)))
   (assert-lincoln-log-grammar-constraints! grid)
   (assert! (some-constraint
	     (lambda (thing) (door?-constraint grid thing)) (things grid)))
   (nondeterministic-solution (domain-variables))
   (write-grid grid (string-append "solution-" (number->string i) ".logs"))
   (set! i (+ i 1))
   (fail)))
 (system "./gui"))

;;; works, 2 solutions probably 2x lexical
(define (test6) (write-grids 2 5 1 '((some wall has some window))))

(define (test7)
 (set-nondeterministic-strategy! 'ac)
 (initialize-domain-variables!)
 (system "rm solution-*.logs")
 (domain
  (let ((i 0) (grid (create-grid 2 6 1)))
   (assert-lincoln-log-grammar-constraints! grid)
   (assert! (some-constraint
	     (lambda (thing1)
	      (and-constraint
	       (wall?-constraint grid thing1)
	       (some-constraint
		(lambda (thing2)
		 (and-constraint (window?-constraint grid thing2)
				 (if (thing-inside? thing2 thing1)
				     (true-domain-variable)
				     (false-domain-variable))))
		(things grid))))
	     (things grid)))
   (nondeterministic-solution (domain-variables))
   (write-grid grid (string-append "solution-" (number->string i) ".logs"))
   (set! i (+ i 1))
   (fail)))
 (system "./gui"))

(define (test8)
 (set-nondeterministic-strategy! 'ac)
 (initialize-domain-variables!)
 (system "rm solution-*.logs")
 (domain
  (let ((i 0) (grid (create-grid 2 6 1)))
   (assert-lincoln-log-grammar-constraints! grid)
   (assert!
    (evaluate
     (parse-expression
      '(some
	(lambda (thing1)
	 (and (wall? thing1)
	      (some (lambda (thing2)
		     (and (window? thing2) (inside? thing2 thing1)))))))
      (parse-type *s*))
     '()
     grid))
   (nondeterministic-solution (domain-variables))
   (write-grid grid (string-append "solution-" (number->string i) ".logs"))
   (set! i (+ i 1))
   (fail)))
 (system "./gui"))

(define (test9)
 (set-nondeterministic-strategy! 'ac)
 (initialize-domain-variables!)
 (system "rm solution-*.logs")
 (domain
  (let ((i 0) (grid (create-grid 2 6 1)))
   (assert-lincoln-log-grammar-constraints! grid)
   (assert! (and-constraint
	     (some-constraint
	      (lambda (thing) (wall?-constraint grid thing))
	      (things grid))
	     (not-constraint
	      (some-constraint
	       (lambda (thing) (window?-constraint grid thing))
	       (things grid)))
	     (not-constraint
	      (some-constraint
	       (lambda (thing) (door?-constraint grid thing))
	       (things grid)))))
   (nondeterministic-solution (domain-variables))
   (write-grid grid (string-append "solution-" (number->string i) ".logs"))
   (set! i (+ i 1))
   (fail)))
 (system "./gui"))

;;; works, 1 solution
(define (test10) (write-grids 2 7 1 '((some window exists) (some door exists))))

;;; works, 1 solution
(define (test11) (write-grids 2 9 1 '((two window exists))))

(define (test12 n)
 (set-nondeterministic-strategy! 'ac)
 (all-sentences n))

(define (test13)
 (set-nondeterministic-strategy! 'ac)
 (initialize-domain-variables!)
 (all-true-sentences-of-length
  3 (first-grid 2 8 1 '((some window exists) (some door exists)))))

(define (test13a)
 (description 3 (first-grid 2 8 1 '((some window exists) (some door exists)))))

(define (test14)
 (set-nondeterministic-strategy! 'ac)
 (initialize-domain-variables!)
 (all-true-sentences-of-length 3 (first-grid 2 10 1 '((two window exists)))))

(define (test14a) (description 3 (first-grid 2 10 1 '((two window exists)))))

(define (test15)
 ;; 224 solutions, lots of non-things
 (write-grids
  2 5 3 '((four wall exists) (two window exists) (four door exists))))

;;; works, 1 solution
(define (test16) (write-grids 2 4 3 '((seven door exists))))

;;; works, 1 solution
(define (test17) (write-grids 2 5 1 '((some solid three-high wall exists))))

(define (test18)
 (write-grids
  2 6 3 '((every wall is solid) (every wall is three-high) (five wall exists))))

(define (test18a)
 (write-grids 2 6 3 '((every wall is three-high) (five solid wall exists))))

(define (test18b)
 (write-grids 2 6 3 '((every wall is solid) (five three-high wall exists))))

(define (test18c) (write-grids 2 6 3 '((five solid three-high wall exists))))

(define (test19)
 ;; 25 solutions, some disconnected, lots of non-things
 (write-grids 2 5 3 '((two solid wall exists) (three window exists))))

(define (test20)
 (set-nondeterministic-strategy! 'ac)
 (initialize-domain-variables!)
 (system "rm solution-*.logs")
 (domain
  (let ((i 0) (grid (create-grid 2 5 3)))
   (assert-lincoln-log-grammar-constraints! grid)
   (assert! (every-constraint
	     (lambda (thing1)
	      (or-constraint
	       (not-constraint (wall?-constraint grid thing1))
	       (some-constraint
		(lambda (thing2)
		 (and-constraint
		  (or-constraint (window?-constraint grid thing2)
				 (wall?-constraint grid thing2))
		  (if (thing-inside? thing2 thing1)
		      (true-domain-variable)
		      (false-domain-variable))))
		(things grid))
	       (solid?-constraint grid thing1)))
	     (things grid)))
   (nondeterministic-solution (domain-variables))
   (write-grid grid (string-append "solution-" (number->string i) ".logs"))
   (set! i (+ i 1))
   (fail)))
 (system "./gui"))

(define (test21)
 (set-nondeterministic-strategy! 'ac)
 (initialize-domain-variables!)
 (system "rm solution-*.logs")
 (domain
  (let ((i 0) (grid (create-grid 2 5 3)))
   (assert-lincoln-log-grammar-constraints! grid)
   (assert! (every-constraint
	     (lambda (thing1)
	      (or-constraint
	       (not-constraint (wall?-constraint grid thing1))
	       (solid?-constraint grid thing1)))
	     (things grid)))
   (nondeterministic-solution (domain-variables))
   (write-grid grid (string-append "solution-" (number->string i) ".logs"))
   (set! i (+ i 1))
   (fail)))
 (system "./gui"))

(define (test22)
 ;; works, 1 solution
 (write-grids 2 6 3 '((two solid two-wide three-high wall exists)
		      (three solid one-wide three-high wall exists))))

(define (test23)
 (write-grids 2 6 3 '((five wall exists)
		      (every wall is three-high)
		      (two wall is two-wide)
		      (three wall is one-wide)
		      (one window exists)
		      (two door exists)
		      (every door is two-high)
		      (three wall is solid))))

(define (test24)
 ;; works, 12 solutions
 ;; 3x for wall containing door, 2x mirror, probably 2x lexical
 (write-grids 2 6 3 '((three one-wide wall exists)
		      (two two-wide wall exists)
		      (two solid one-wide wall exists)
		      (one solid two-wide wall exists)
		      (every wall is three-high)
		      (two two-high door exists)
		      (some window is-to-the-left-of some door))))

(define (test25)
 (write-grids 2 6 3 '((two one-wide wall exists)
		      (two two-wide wall exists)
		      (two solid one-wide wall exists)
		      (one solid two-wide wall exists)
		      (every wall is three-high)
		      (some window is-to-the-left-of some two-high door))))

;;; works, 1 solution
(define (test26) (write-grids 2 6 3 '((seven two-high door exists))))

(define (test26a)
 (description 4 (first-grid 2 6 3 '((seven two-high door exists)))))

;;; works, 35 solutions
(define (test27)
 (write-grids 2 6 3 '((four two-high door exists) (three window exists))))

(define (test28)
 (description
  4 (first-grid 2 6 3 '((every wall is three-high) (five solid wall exists)))))

(define (test29)
 (description2
  4 (first-grid 2 4 3 '((two solid two-wide two-high wall exists)
			(three solid one-wide two-high wall exists)))))

;;(test29)
