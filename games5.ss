#!r6rs

(library
 (games5)
 (export make-state state-board state-cache-for-x state-cache-for-o state-player
	 *lexicon* remove-duplicates
	 test-lexicon test-grammar test-parse->lf test-semantics
	 sentence->rule sentences->rules
	 initial-state initial-state? win? draw? legal-moves random-game valid?
	 *tic-tac-toe* *hexapawn*)
 (import (rnrs)
	 (QobiScheme)
	 (nondeterministic-scheme)
	 (maximizing-nondeterministic-promises))

;;; 1. observer learns rules, renders them linguistically to a hearer who plays
;;; 2. learner asks linguistic yes/no questions to disambiguate ambiguous
;;;    training data
;;; 3. learner asks robotic yes/no questions to disambiguate ambiguous training
;;;    data
;;; needs work:
;;; 1. we cheat throughout and treat "piece of player" as a type rather than as
;;;    a token
;;; 2. ambiguity between position (collection) and state for board, cache, row,
;;;    column, diagonal, and square
;;; 3. remaining quantifier scoping ambiguity
;;;    one simple thing is to rule out every nested in some which suffices for
;;;    all of the current examples
;;;    currently don't do anythings since the only ambiguity affects piece and
;;;    we cheat on the type-token distinction
;;; 4. relative-clause ambiguity

;;; Is this a win for x?
;;; Is this a draw?
;;; Is this an initial state?
;;; Is this a move?

;;; It is awkward to require the player to be explicit for opponent, cache,
;;; piece, distant, close, forward-adjacent, and forward-diagonal.

;;; Characteristics that are part of the bias:
;;;  1. Can have multiple sentences for the outcome predicate instead of
;;;     coordinating the when.
;;;  2. Can have multiple sentences for the legal-move generator instead of
;;;     coordinating the by.
;;;  3. Draw predicate can refer to win predicate and the legal-move generator.
;;;  4. Initial state only specifies positions of pieces not empty squares.
;;;  5. Assumes turn taking and X goes first.
;;;  6. Every square can have at most one piece.
;;;  7. All games moves involve a sequence of piece moves, which in turn
;;;     involve picking up and putting down pices.
;;;  8. There is conservation of matter. Pieces don't appear and disappear.
;;;     They have to be somewhere, hence the cache is explicit in the state
;;;     representation.
;;;  9. Players can only win when they make a move.

;;; needs work: In the tic-tac-toe and hexapawn legal-move generators you don't
;;;             have to say to empty anymore.

 (define-record-type state (fields board cache-for-x cache-for-o player))

 (define-record-type binding (fields variable thing))

 (define-record-type player (fields player))

 (define-record-type piece (fields player))

 (define-record-type board-square (fields row column))

 (define-record-type row (fields row))

 (define-record-type column (fields column))

 (define-record-type diagonal (fields slope))

 (define-record-type cache-square (fields player i))

 (define-record-type cache (fields player))

 (define-record-type move (fields))

 (define *lexicon*
  '((d a)
    (d some)
    (d every)
    (d that)
    (d no)
    (d the)
    ;;
    (n player ())
    (n opponent ())
    (n opponent ((pp of player)))
    (n row ())
    (n column ())
    (n diagonal ())
    (n cache ())
    (n cache ((pp for player)))
    (n square ())
    (n square ((pp of line)))
    (n square ((pp in line)))
    (n piece ())
    (n piece ((pp of player)))
    (n move ())
    ;;
    (a distant ((n row)))
    (a distant ((n row) (pp for player)))
    (a close ((n row)))
    (a close ((n row) (pp for player)))
    ;; lexicalization
    (a forward-adjacent ((n square)))
    (a forward-adjacent ((n square) (pp for player) (pp of square)))
    ;; lexicalization
    (a forward-diagonal ((n square)))
    (a forward-diagonal ((n square) (pp for player) (pp of square)))
    (a board ((n square)))
    (a cache ((n square)))
    (a cache ((n square) (pp for player)))
    (a empty ((nbar line)))
    (a empty ((nbar square)))
    ;;
    (p in ((np line)))
    (p for ((np player)))
    (p of ((np player)))
    (p of ((np square)))
    (p from ((np square)))
    (p to ((np square)))
    ;; needs work: should only allow moving
    (p by (vp))
    ;; needs work: should only allow wins/1, draws/1, and has
    (p when (s))
    ;;
    (v wins ())
    ;; needs work: should constrain allowed types
    (v wins ((pp when)))
    ;; needs work: should constrain allowed types
    (v draws ((pp when)))
    (v has ((np piece)))
    (v has ((np move)))
    ;; needs work: should constrain allowed types
    (v moves ((pp by)))
    (v moving ((np piece) (pp from square) (pp to square)))
    ;;
    (coord then)
    (coord and)
    ;;
    (c that)))

 (define (coordinated? x)
  (and (= (length x) 4)
       (eq? (first (third x)) 'coord)
       (eq? (first (second x)) (first (fourth x)))))

 (define (head-n nbar)
  (unless (eq? (first nbar) 'nbar) (fuck-up))
  ;; For now, can't coordinate NBAR.
  (cond ((coordinated? nbar) (fail))
	((and (= (length nbar) 3)
	      (eq? (first (second nbar)) 'nbar)
	      (eq? (first (third nbar)) 'r))
	 (head-n (second nbar)))
	((and (= (length nbar) 3)
	      (eq? (first (second nbar)) 'a)
	      (eq? (first (third nbar)) 'nbar))
	 (head-n (third nbar)))
	((eq? (first (second nbar)) 'n) (second (second nbar)))
	((eq? (first (second nbar)) 'a) (second (third nbar)))
	(else (fuck-up))))

 (define (head-a? nbar)
  (unless (eq? (first nbar) 'nbar) (fuck-up))
  ;; For now, can't coordinate NBAR.
  (cond ((coordinated? nbar) (fail))
	((and (= (length nbar) 3)
	      (eq? (first (second nbar)) 'nbar)
	      (eq? (first (third nbar)) 'r))
	 (head-a? (second nbar)))
	;; The A of A NBAR is not considered a head.
	((and (= (length nbar) 3)
	      (eq? (first (second nbar)) 'a)
	      (eq? (first (third nbar)) 'nbar))
	 (head-a? (third nbar)))
	((eq? (first (second nbar)) 'n) #f)
	((eq? (first (second nbar)) 'a) #t)
	(else (fuck-up))))

 (define (head-a nbar)
  (unless (eq? (first nbar) 'nbar) (fuck-up))
  ;; For now, can't coordinate NBAR.
  (cond ((coordinated? nbar) (fail))
	((and (= (length nbar) 3)
	      (eq? (first (second nbar)) 'nbar)
	      (eq? (first (third nbar)) 'r))
	 (head-a (second nbar)))
	;; The A of A NBAR is not considered a head.
	((and (= (length nbar) 3)
	      (eq? (first (second nbar)) 'a)
	      (eq? (first (third nbar)) 'nbar))
	 (head-a (third nbar)))
	((eq? (first (second nbar)) 'n) (fuck-up))
	((eq? (first (second nbar)) 'a) (second (second nbar)))
	(else (fuck-up))))

 (define (is-a? n class)
  (case class
   ((player) (memq n '(player opponent)))
   ((line) (memq n '(row column diagonal cache)))
   ((square) (memq n '(square)))
   ((piece) (memq n '(piece)))
   ((move) (memq n '(move)))
   (else (fuck-up))))

 (define (an-x category words)
  (unless (memq category '(d n a p v coord c nbar np pp vp s r)) (fuck-up))
  (when (null? words) (fail))
  (amb
   (list
    (a-member-of
     (remove-if-not
      (lambda (entry)
       (and (eq? (second entry) (first words)) (eq? (first entry) category)))
      *lexicon*))
    (rest words))
   (let loop ((words words))
    (let ((result
	   (case category
	    ((np) (let* ((result (an-x 'd words))
			 (d (first result))
			 (result (an-x 'nbar (second result))))
		   (list (list 'np d (first result)) (second result))))
	    ((nbar pp vp)
	     (let* ((result (an-x (case category
				   ((nbar) (amb 'n 'a))
				   ((pp) 'p)
				   ((vp) 'v)
				   (else (fuck-up)))
				  words))
		    (head (first result)))
	      (let loop ((subcategorizations (third head))
			 (words (second result))
			 (complements '()))
	       (if (null? subcategorizations)
		   (let loop ((x (cons category
				       (cons head (reverse complements))))
			      (words words))
		    (amb (list x words)
			 (begin (unless (eq? category 'nbar) (fail))
				(let ((result (an-x 'r words)))
				 (loop (list 'nbar x (first result))
				       (second result))))))
		   (let* ((subcategorization (first subcategorizations))
			  (category (if (list? subcategorization)
					(first subcategorization)
					subcategorization)))
		    (unless (eq? (or (eq? category 'n)
				     (eq? category 'np)
				     (eq? category 'pp)
				     (eq? category 'nbar))
				 (list? subcategorization))
		     (fuck-up))
		    (let ((result (an-x category words)))
		     ;; here I am: We don't yet check the third element of a PP
		     ;;            subcategorization.
		     (when (list? subcategorization)
		      (case category
		       ((n) (unless (eq? (second subcategorization)
					 (second (first result)))
			     (fail)))
		       ((np)
			;; For now, can't coordinate NP.
			(when (coordinated? (first result)) (fail))
			;; This assumes that an NP subcategorization
			;; element subcategorizes the head noun.
			(unless (is-a? (head-n (third (first result)))
				       (second subcategorization))
			 (fail)))
		       ((pp) (unless (eq? (second subcategorization)
					  (second (second (first result))))
			      (fail)))
		       ;; This assumes that an NBAR subcategorization
		       ;; element subcategorizes the head noun.
		       ((nbar) (unless (is-a? (head-n (first result))
					      (second subcategorization))
				(fail)))
		       (else (fuck-up))))
		     ;; In our hokey grammar, in an A N construct, the A
		     ;; subcategorizes and the subcategorization frame of the
		     ;; N must be empty.
		     (when (and (eq? category 'n)
				(not (null? (third (first result)))))
		      (fail))
		     (loop (rest subcategorizations)
			   (second result)
			   (cons (first result) complements))))))))
	    ((s) (let* ((result (an-x 'np words))
			(np (first result))
			(result (an-x 'vp (second result))))
		  (list (list 's np (first result)) (second result))))
	    ((r) (let* ((result (an-x 'c words))
			(c (first result))
			(result (an-x 'vp (second result))))
		  (list (list 'r c (first result)) (second result))))
	    (else (fail)))))
     (amb result
	  (let* ((x (first result))
		 (result (an-x 'coord (second result)))
		 (coord (first result))
		 (result (loop (second result))))
	   (list (list category x coord (first result)) (second result))))))))

 (define (a-parse words)
  (let ((result (an-x 's words)))
   (unless (null? (second result)) (fail))
   (first result)))

 (define (np? parse) (and (list? parse) (eq? (first parse) 'np)))

 (define (p-vp? parse)
  (and (list? parse) (eq? (first parse) 'pp) (eq? (first (third parse)) 'vp)))

 (define (p-s? parse)
  (and (list? parse) (eq? (first parse) 'pp) (eq? (first (third parse)) 's)))

 (define (parse->lf parse)
  ;; This has a Montagovian flavor.
  ;; This assumes throughout that
  ;;   lexical ambiguity does not lead to semantic ambiguity and
  ;;   prepositions and complementizers don't contribute semantic content.
  ;; QR ambiguity intentionally omitted throughout as it is handled elsewhere.
  ;; There should be coordination raising ambiguity just like QR.
  ;; needs work: Should generalize throughout to an arbitrary number of
  ;;             complements where any complement can be an NP, P VP, or P S.
  (let ((index -1))
   (define (gensym)
    (set! index (+ index 1))
    (string->symbol (string-append "x" (number->string index))))
   (let loop ((parse parse))
    (if (and (= (length parse) 4) (eq? (first (third parse)) 'coord))
	(let ((coord (second (third parse))))
	 (case (first (second parse))
	  ((nbar)
	   (let ((nbar1 (loop (second parse))) (nbar2 (loop (fourth parse))))
	    (lambda (object) `(,coord ,(nbar1 object) ,(nbar2 object)))))
	  ((np) (let ((np1 (loop (second parse))) (np2 (loop (fourth parse))))
		 (lambda (n) `(,coord ,(np1 n) ,(np2 n)))))
	  ((pp) (loop (list (first parse)
			    (second (second parse))
			    (list (first (third (second parse)))
				  (third (second parse))
				  (third parse)
				  (third (fourth parse))))))
	  ((vp) (let ((vp1 (loop (second parse))) (vp2 (loop (fourth parse))))
		 (lambda (np) `(,coord ,(vp1 np) ,(vp2 np)))))
	  ((s) `(,coord ,(loop (second parse)) ,(loop (fourth parse))))
	  ((r) (loop (list (first parse)
			   (second (second parse))
			   (list (first (third (second parse)))
				 (third (second parse))
				 (third parse)
				 (third (fourth parse))))))
	  (else (fuck-up))))
	(case (first parse)
	 ((nbar)
	  (cond
	   ((eq? (first (second parse)) 'n)
	    (let ((n (second (second parse)))
		  (complements (map loop (rest (rest parse)))))
	     ;; needs work: to move before computing complements
	     (unless (or (and (memq n '(player
					row
					column
					diagonal
					cache
					square
					piece
					move))
			      (= (length complements) 0))
			 (and (memq n '(opponent cache square piece))
			      (= (length complements) 1)))
	      (fail))
	     (case (length complements)
	      ((0) (lambda (object1) `(,n ,object1)))
	      ((1) (lambda (object1)
		    ;; limits to QR
		    ((first complements)
		     (lambda (object2) `(,n ,object1 ,object2)))))
	      ((2) (lambda (object1)
		    ;; limits to QR
		    ((first complements)
		     (lambda (object2)
		      ((second complements)
		       (lambda (object3) `(,n ,object1 ,object2 ,object3)))))))
	      (else (fuck-up)))))
	   ((and (eq? (first (second parse)) 'a) (eq? (first (third parse)) 'n))
	    (let ((a-n (string->symbol
			(string-append
			 (symbol->string (second (second parse)))
			 "-"
			 (symbol->string (second (third parse))))))
		  (complements (map loop (rest (rest (rest parse))))))
	     ;; needs work: to move before computing complements
	     (unless (or (and (memq a-n '(board-square cache-square))
			      (= (length complements) 0))
			 (and (memq a-n '(distant-row close-row cache-square))
			      (= (length complements) 1))
			 (and (memq a-n '(forward-adjacent-square
					  forward-diagonal-square))
			      (= (length complements) 2)))
	      (fail))
	     (case (length complements)
	      ((0) (lambda (object1) `(,a-n ,object1)))
	      ((1) (lambda (object1)
		    ;; limits to QR
		    ((first complements)
		     (lambda (object2) `(,a-n ,object1 ,object2)))))
	      ((2) (lambda (object1)
		    ;; limits to QR
		    ((first complements)
		     (lambda (object2)
		      ((second complements)
		       (lambda (object3)
			`(,a-n ,object1 ,object2 ,object3)))))))
	      (else (fuck-up)))))
	   ((eq? (first (second parse)) 'a)
	    (let ((a (second (second parse))) (nbar (loop (third parse))))
	     (unless (eq? a 'empty) (fail))
	     ;; limits to QR
	     (lambda (object) `(and ,(nbar object) (,a ,object)))))
	   (else (let ((nbar (loop (second parse))) (r (loop (third parse))))
		  (lambda (object)
		   ;; limits to QR
		   (r (lambda (n) `(and ,(nbar object) ,(n object)))))))))
	 ((np)
	  (case (second (second parse))
	   ((a)
	    ;; This assumes that you can use "a" only to denote defining
	    ;; occurrences and only in the NP "a player" with no relative
	    ;; clauses, no complements, and no adjectives.
	    (cond ((and (= (length (third parse)) 2)
			(= (length (second (third parse))) 3)
			(eq? (first (second (third parse))) 'n)
			(eq? (second (second (third parse))) 'player))
		   (lambda (n) (n 'p)))
		  (else (fail))))
	   ((some every no the)
	    (let ((nbar (loop (third parse))) (object (gensym)))
	     (lambda (n)
	      (if (eq? (second (second parse)) 'no)
		  ;; "no" can't be a target
		  `(,(second (second parse))
		    ,object ,(nbar object) ,(n object))
		  (if (head-a? (third parse))
		      `(,(second (second parse))
			,object
			,(nbar object)
			,(n object)
			,(head-n (third parse))
			,(head-a (third parse)))
		      `(,(second (second parse))
			,object
			,(nbar object)
			,(n object)
			,(head-n (third parse))))))))
	   ((that)
	    ;; This assumes that you can only use "that" to denote anaporic
	    ;; reference and that there can be no relative clauses, no
	    ;; complements, and no non-head adjectives.
	    (cond
	     ((and (= (length (third parse)) 2)
		   (= (length (second (third parse))) 3)
		   (eq? (first (second (third parse))) 'n))
	      (lambda (n) (n `(anaphor ,(second (second (third parse)))))))
	     ((and (= (length (third parse)) 3)
		   (= (length (second (third parse))) 3)
		   (eq? (first (second (third parse))) 'a)
		   (= (length (third (third parse))) 3)
		   (eq? (first (third (third parse))) 'n))
	      (lambda (n)
	       (n `(anaphor ,(second (third (third parse)))
			    ,(second (second (third parse)))))))
	     (else (fail))))
	   (else (fuck-up))))
	 ((pp) (loop (third parse)))
	 ((vp)
	  (let ((v (second (second parse)))
		(complements (map loop (rest (rest parse)))))
	   ;; needs work: to move before computing complements
	   (unless (or (and (= (length complements) 1)
			    (or (p-vp? (third parse)) (p-s? (third parse))))
		       (and (memq v '(wins)) (= (length complements) 0))
		       (and (memq v '(has)) (= (length complements) 1))
		       (and (memq v '(moving)) (= (length complements) 3)))
	    (fail))
	   (case (length complements)
	    ((0) (lambda (np) (np (lambda (object1) `(,v ,object1)))))
	    ((1) (lambda (np)
		  (np (lambda (object1)
		       (cond ((np? (third parse))
			      ((first complements)
			       (lambda (object2)
				`(,v ,object1 ,object2))))
			     ((p-vp? (third parse))
			      `(define (,v ,object1) ,((first complements) np)))
			     ((p-s? (third parse))
			      `(define (,v ,object1) ,(first complements)))
			     (else (fuck-up)))))))
	    ((2) (lambda (np)
		  (np (lambda (object1)
		       ((first complements)
			(lambda (object2)
			 ((second complements)
			  (lambda (object3)
			   `(,v ,object1 ,object2 ,object3)))))))))
	    ((3) (lambda (np)
		  (np
		   (lambda (object1)
		    ((first complements)
		     (lambda (object2)
		      ((second complements)
		       (lambda (object3)
			((third complements)
			 (lambda (object4)
			  `(,v ,object1 ,object2 ,object3 ,object4)))))))))))
	    (else (fuck-up)))))
	 ((s) ((loop (third parse)) (loop (second parse))))
	 ((r) (loop (third parse)))
	 (else (fuck-up)))))))

 (define (an-anaphora-resolution lf)
  (let ((targets
	 (remove-duplicates
	  (let loop ((lf lf))
	   (append
	    (if (or (memq lf '(p))
		    ;; "no" can't be a target
		    (and (list? lf) (memq (first lf) '(some every the))))
		(list lf)
		'())
	    (if (list? lf) (map-reduce append '() loop lf) '()))))))
   (let loop ((lf lf))
    (if (list? lf)
	(if (eq? (first lf) 'anaphor)
	    (let ((target
		   (a-member-of
		    (remove-if-not
		     (lambda (target)
		      (or (and (= (length lf) 2)
			       (eq? (second lf) 'player)
			       (eq? target 'p))
			  (and (= (length lf) 2)
			       (list? target)
			       (= (length target) 5)
			       (eq? (second lf) (fifth target)))
			  (and (= (length lf) 3)
			       (list? target)
			       (= (length target) 6)
			       (eq? (second lf) (fifth target))
			       (eq? (third lf) (sixth target)))))
		     targets))))
	     (if (symbol? target) target (second target)))
	    (map loop lf))
	lf))))

 (define (declarative-sentence lf)
  (if (and (list? lf) (not (eq? (first lf) 'define)))
      `(define (initial-state) ,lf)
      lf))

 (define (variables-in lf)
  (remove-duplicates
   (let loop ((lf lf))
    ;; "no" can't be raised
    (append (if (and (list? lf) (memq (first lf) '(some every the)))
		(list (second lf))
		'())
	    (if (list? lf) (map-reduce append '() loop lf) '())))))

 (define (quantifier-of x lf)
  (first
   (let loop ((lf lf))
    (append (if (and (list? lf)
		     ;; "no" can't be raised
		     (memq (first lf) '(some every the))
		     (eq? (second lf) x))
		(list lf)
		'())
	    (if (list? lf) (map-reduce append '() loop lf) '())))))

 (define (remove-quantifier-of x lf)
  (let loop ((lf lf))
   (if (list? lf)
       ;; "no" can't be raised
       (if (and (memq (first lf) '(some every the)) (eq? (second lf) x))
	   (fourth lf)
	   (cons (first lf) (map loop (rest lf))))
       lf)))

 (define (raise-quantifier x lf)
  (let ((q (quantifier-of x lf)))
   (list (first q)
	 (second q)
	 (third q)
	 (remove-quantifier-of x lf))))

 (define (well-formed-term? lf xs) (memq lf xs))

 (define (well-formed-formula? lf xs)
  (or
   (and (list? lf)
	(= (length lf) 3)
	(memq (first lf) '(then and))
	(well-formed-formula? (second lf) xs)
	(well-formed-formula? (third lf) xs))
   (and (list? lf)
	(= (length lf) 4)
	(memq (first lf) '(some every no the))
	(symbol? (second lf))
	(well-formed-formula? (third lf) (cons (second lf) xs))
	(well-formed-formula? (fourth lf) (cons (second lf) xs)))
   (and
    (list? lf)
    (or (and (= (length lf) 2)
	     (memq (first lf)
		   '(player
		     row
		     column
		     diagonal
		     cache
		     square
		     piece
		     move
		     board-square
		     cache-square
		     empty
		     wins)))
	(and (= (length lf) 3)
	     (memq (first lf)
		   '(opponent
		     cache
		     square
		     piece
		     distant-row
		     close-row
		     cache-square
		     has)))
	(and (= (length lf) 4)
	     (memq (first lf)
		   '(forward-adjacent-square forward-diagonal-square)))
	(and (= (length lf) 5)
	     (memq (first lf) '(moving))))
    (every (lambda (lf) (well-formed-term? lf xs)) (rest lf)))))

 (define (well-formed-definition? lf)
  (and (list? lf)
       (= (length lf) 3)
       (eq? (first lf) 'define)
       (or (equal? (second lf) '(initial-state))
	   (equal? (second lf) '(wins p))
	   (equal? (second lf) '(draws p))
	   (equal? (second lf) '(moves p)))
       (well-formed-formula? (third lf) (rest (second lf)))))

 (define (free-in? x lf)
  (if (list? lf)
      (if (memq (first lf) '(some every no the))
	  (and (not (eq? x (second lf)))
	       (or (free-in? x (third lf)) (free-in? x (fourth lf))))
	  (some (lambda (lf) (free-in? x lf)) (rest lf)))
      (eq? x lf)))

 (define (before? x1 x2 lf) (free-in? x1 (third (quantifier-of x2 lf))))

 (define (a-split-of l)
  (let loop ((x '()) (y l))
   (if (null? y)
       (list x y)
       (amb (list x y) (loop (append x (list (first y))) (rest y))))))

 (define (an-ordered-permutation-of < l)
  (if (null? l)
      l
      (let ((split (a-split-of (an-ordered-permutation-of < (rest l)))))
       (when (or (some (lambda (x) (< (first l) x)) (first split))
		 (some (lambda (x) (< x (first l))) (second split)))
	(fail))
       (append (first split) (cons (first l) (second split))))))

 (define (a-quantifier-scoping lf)
  (let* ((definiens (second lf))
	 (lf (third lf))
	 (xs (variables-in lf))
	 (before?
	  (let ((lf (let loop ((xs xs) (lf lf))
		     (if (null? xs)
			 lf
			 (loop (rest xs) (raise-quantifier (first xs) lf))))))
	   (lambda (x1 x2) (before? x1 x2 lf))))
	 (lf `(define ,definiens
	       ,(let loop ((xs (reverse (an-ordered-permutation-of before? xs)))
			   (lf lf))
		 (if (null? xs)
		     lf
		     (loop (rest xs) (raise-quantifier (first xs) lf)))))))
   ;; needs work: We need to prevent coordination of defines before changing
   ;;             this fail to fuck-up.
   (unless (well-formed-definition? lf) (fail))
   lf))

 (define (board-ref state board-square)
  (force-nondeterministic-promise
   (matrix-ref (state-board state)
	       (board-square-row board-square)
	       (board-square-column board-square))))

 (define (cache-ref state cache-square)
  (force-nondeterministic-promise
   (vector-ref ((case (cache-square-player cache-square)
		 ((x) state-cache-for-x)
		 ((o) state-cache-for-o)
		 (else (fuck-up)))
		state)
	       (cache-square-i cache-square))))

 (define (vector-replace v i x)
  (list->vector (list-replace (vector->list v) i x)))

 (define (matrix-replace m i j x)
  (vector-replace m i (vector-replace (vector-ref m i) j x)))

 (define (board-replace state board-square player)
  (matrix-replace (state-board state)
		  (board-square-row board-square)
		  (board-square-column board-square)
		  player))

 (define (cache-replace state cache-square player)
  (vector-replace ((case (cache-square-player cache-square)
		    ((x) state-cache-for-x)
		    ((o) state-cache-for-o)
		    (else (fuck-up)))
		   state)
		  (cache-square-i cache-square)
		  player))

 (define (turn state)
  (make-state (state-board state)
	      (state-cache-for-x state)
	      (state-cache-for-o state)
	      (case (state-player state)
	       ((x) 'o)
	       ((o) 'x)
	       (else (fuck-up)))))

 (define (interpret lf kind lfs state)
  ;; We can't give type errors for nouns. We can but don't give type errors for
  ;; adjectives and verbs.
  (let ((things
	 (append (list (make-player 'x)
		       (make-player 'o)
		       (make-piece 'x)
		       (make-piece 'o)
		       (make-board-square 0 0)
		       (make-board-square 0 1)
		       (make-board-square 0 2)
		       (make-board-square 1 0)
		       (make-board-square 1 1)
		       (make-board-square 1 2)
		       (make-board-square 2 0)
		       (make-board-square 2 1)
		       (make-board-square 2 2)
		       (make-row 0)
		       (make-row 1)
		       (make-row 2)
		       (make-column 0)
		       (make-column 1)
		       (make-column 2)
		       (make-diagonal 1)
		       (make-diagonal -1)
		       (make-cache-square 'x 0)
		       (make-cache-square 'x 1)
		       (make-cache-square 'x 2)
		       (make-cache-square 'x 3)
		       (make-cache-square 'x 4)
		       (make-cache-square 'o 0)
		       (make-cache-square 'o 1)
		       (make-cache-square 'o 2)
		       (make-cache-square 'o 3)
		       (make-cache-square 'o 4)
		       (make-cache 'x)
		       (make-cache 'o))
		 ;; For now, we just reify the presence or absence of moves, not
		 ;; the moves themselves.
		 (if (and (eq? kind 'predicate)
			  (some
			   (lambda (lf)
			    (and (equal? (second lf) '(moves p))
				 (not
				  (null? (interpret
					  (third lf) 'function lfs state)))))
			   lfs))
		     (list (make-move))
		     '()))))
   (define (predicate lf bindings state)
    (define (lookup t)
     (let ((binding
	    (find-if (lambda (binding) (eq? t (binding-variable binding)))
		     bindings)))
      (unless binding (fuck-up))
      (binding-thing binding)))
    (case (first lf)
     ((then) (fail))
     ((and)
      (and (predicate (second lf) bindings state)
	   (predicate (third lf) bindings state)))
     ((some)
      (some (lambda (thing)
	     (and (predicate (third lf)
			     (cons (make-binding (second lf) thing) bindings)
			     state)
		  (predicate (fourth lf)
			     (cons (make-binding (second lf) thing) bindings)
			     state)))
	    things))
     ((every)
      (every
       (lambda (thing)
	(or (not (predicate (third lf)
			    (cons (make-binding (second lf) thing) bindings)
			    state))
	    (predicate (fourth lf)
		       (cons (make-binding (second lf) thing) bindings)
		       state)))
       things))
     ((no)
      (not
       (some (lambda (thing)
	      (and (predicate (third lf)
			      (cons (make-binding (second lf) thing) bindings)
			      state)
		   (predicate (fourth lf)
			      (cons (make-binding (second lf) thing) bindings)
			      state)))
	     things)))
     ((the)
      (unless (one (lambda (thing)
		    (predicate (third lf)
			       (cons (make-binding (second lf) thing) bindings)
			       state))
		   things)
       (fail))
      (predicate
       (fourth lf)
       (cons (make-binding
	      (second lf)
	      (find-if (lambda (thing)
			(predicate (third lf)
				   (cons (make-binding (second lf) thing)
					 bindings)
				   state))
		       things))
	     bindings)
       state))
     ;; 1
     ((player) (player? (lookup (second lf))))
     ((row) (row? (lookup (second lf))))
     ((column) (column? (lookup (second lf))))
     ((diagonal) (diagonal? (lookup (second lf))))
     ((board-square) (board-square? (lookup (second lf))))
     ((empty)
      ;; Could generalize to empty rows, columns, diagonals, cache (for a
      ;; player), and board.
      (or (and (board-square? (lookup (second lf)))
	       (eq? (board-ref state (lookup (second lf))) #f))
	  (and (cache-square? (lookup (second lf)))
	       (eq? (cache-ref state (lookup (second lf))) #f))))
     ;; needs work: This screws up if it is used in the second argument to
     ;;             "then".
     ((move) (move? (lookup (second lf))))
     ((wins)
      (and (player? (lookup (second lf)))
	   (win? lfs
		 (make-state (state-board state)
			     (state-cache-for-x state)
			     (state-cache-for-o state)
			     (case (player-player (lookup (second lf)))
			      ((x) 'o)
			      ((o) 'x)
			      (else (fuck-up)))))))
     ;; 1 or 2
     ((cache)
      (case (length lf)
       ((2) (cache? (lookup (second lf))))
       ((3) (and (cache? (lookup (second lf)))
		 (player? (lookup (third lf)))
		 (eq? (cache-player (lookup (second lf)))
		      (player-player (lookup (third lf))))))
       (else (fuck-up))))
     ((square)
      (case (length lf)
       ((2)
	(or (board-square? (lookup (second lf)))
	    (cache-square? (lookup (second lf)))))
       ((3)
	(or
	 (and (board-square? (lookup (second lf)))
	      (or (and (row? (lookup (third lf)))
		       (= (board-square-row (lookup (second lf)))
			  (row-row (lookup (third lf)))))
		  (and (column? (lookup (third lf)))
		       (= (board-square-column (lookup (second lf)))
			  (column-column (lookup (third lf)))))
		  (and (diagonal? (lookup (third lf)))
		       (or (and (= (diagonal-slope (lookup (third lf))) 1)
				(= (board-square-row (lookup (second lf)))
				   (board-square-column (lookup (second lf)))))
			   (and (= (diagonal-slope (lookup (third lf))) -1)
				(= (board-square-row (lookup (second lf)))
				   (- 2 (board-square-column
					 (lookup (second lf))))))))))
	 (and (cache-square? (lookup (second lf)))
	      (cache? (lookup (third lf)))
	      (eq? (cache-square-player (lookup (second lf)))
		   (cache-player (lookup (third lf)))))))
       (else (fuck-up))))
     ((piece)
      (case (length lf)
       ((2) (piece? (lookup (second lf))))
       ((3) (and (piece? (lookup (second lf)))
		 (player? (lookup (third lf)))
		 (eq? (piece-player (lookup (second lf)))
		      (player-player (lookup (third lf))))))
       (else (fuck-up))))
     ((cache-square)
      (case (length lf)
       ((2) (cache-square? (lookup (second lf))))
       ((3) (and (cache-square? (lookup (second lf)))
		 (player? (lookup (third lf)))
		 (eq? (cache-square-player (lookup (second lf)))
		      (player-player (lookup (third lf))))))
       (else (fuck-up))))
     ;; 2
     ((opponent)
      (and (player? (lookup (second lf)))
	   (player? (lookup (third lf)))
	   (not (eq? (player-player (lookup (second lf)))
		     (player-player (lookup (third lf)))))))
     ((distant-row)
      (and (row? (lookup (second lf)))
	   (player? (lookup (third lf)))
	   (or (and (eq? (player-player (lookup (third lf))) 'x)
		    (= (row-row (lookup (second lf))) 2))
	       (and (eq? (player-player (lookup (third lf))) 'o)
		    (= (row-row (lookup (second lf))) 0)))))
     ((close-row)
      (and (row? (lookup (second lf)))
	   (player? (lookup (third lf)))
	   (or (and (eq? (player-player (lookup (third lf))) 'x)
		    (= (row-row (lookup (second lf))) 0))
	       (and (eq? (player-player (lookup (third lf))) 'o)
		    (= (row-row (lookup (second lf))) 2)))))
     ;; Could generalize to rows, columns, diagonals, cache (for a player), and
     ;; board.
     ((has)
      (or (and (board-square? (lookup (second lf)))
	       (piece? (lookup (third lf)))
	       (eq? (board-ref state (lookup (second lf)))
		    (piece-player (lookup (third lf)))))
	  (and (cache-square? (lookup (second lf)))
	       (piece? (lookup (third lf)))
	       (eq? (cache-ref state (lookup (second lf)))
		    (piece-player (lookup (third lf)))))
	  (and (player? (lookup (second lf)))
	       (move? (lookup (third lf)))
	       (eq? (player-player (lookup (second lf)))
		    (state-player state)))))
     ;; 3
     ((forward-adjacent-square)
      (and (board-square? (lookup (second lf)))
	   (player? (lookup (third lf)))
	   (board-square? (lookup (fourth lf)))
	   (= (board-square-column (lookup (second lf)))
	      (board-square-column (lookup (fourth lf))))
	   (= (board-square-row (lookup (second lf)))
	      (+ (case (player-player (lookup (third lf)))
		  ((x) 1)
		  ((o) -1)
		  (else (fuck-up)))
		 (board-square-row (lookup (fourth lf)))))))
     ((forward-diagonal-square)
      (and (board-square? (lookup (second lf)))
	   (player? (lookup (third lf)))
	   (board-square? (lookup (fourth lf)))
	   (or (= (board-square-column (lookup (second lf)))
		  (+ (board-square-column (lookup (fourth lf))) 1))
	       (= (board-square-column (lookup (second lf)))
		  (- (board-square-column (lookup (fourth lf))) 1)))
	   (= (board-square-row (lookup (second lf)))
	      (+ (case (player-player (lookup (third lf)))
		  ((x) 1)
		  ((o) -1)
		  (else (fuck-up)))
		 (board-square-row (lookup (fourth lf)))))))
     ;; 4
     ((moving) (fail))
     (else (fuck-up))))
   (define (function lf bindings state)
    (define (lookup t)
     (let ((binding
	    (find-if (lambda (binding) (eq? t (binding-variable binding)))
		     bindings)))
      (unless binding (fuck-up))
      (binding-thing binding)))
    (case (first lf)
     ((then)
      (map-reduce append
		  '()
		  (lambda (state) (function (third lf) bindings state))
		  (function (second lf) bindings state)))
     ((and) (fail))
     ((some)
      (map-reduce
       append
       '()
       (lambda (thing)
	(if (predicate (third lf)
		       (cons (make-binding (second lf) thing) bindings)
		       state)
	    (function (fourth lf)
		      (cons (make-binding (second lf) thing) bindings)
		      state)
	    '()))
       things))
     ((every) (fail))
     ((no) (fail))
     ((the)
      (unless (one (lambda (thing)
		    (predicate (third lf)
			       (cons (make-binding (second lf) thing) bindings)
			       state))
		   things)
       (fail))
      (function
       (fourth lf)
       (cons (make-binding
	      (second lf)
	      (find-if (lambda (thing)
			(predicate (third lf)
				   (cons (make-binding (second lf) thing)
					 bindings)
				   state))
		       things))
	     bindings)
       state))
     ;; 1
     ((player) (fail))
     ((row) (fail))
     ((column) (fail))
     ((diagonal) (fail))
     ((board-square) (fail))
     ((empty) (fail))
     ((move) (fail))
     ((wins) (fail))
     ;; 1 or 2
     ((cache) (fail))
     ((square) (fail))
     ((piece) (fail))
     ((cache-square) (fail))
     ;; 2
     ((opponent) (fail))
     ((distant-row) (fail))
     ((close-row) (fail))
     ((has) (fail))
     ;; 3
     ((forward-adjacent-square) (fail))
     ((forward-diagonal-square) (fail))
     ;; 4
     ((moving)
      (if (and (or (and (board-square? (lookup (fourth lf)))
			(eq? (board-ref state (lookup (fourth lf)))
			     (piece-player (lookup (third lf)))))
		   (and (cache-square? (lookup (fourth lf)))
			(eq? (cache-ref state (lookup (fourth lf)))
			     (piece-player (lookup (third lf))))))
	       (or (and (board-square? (lookup (fifth lf)))
			(eq? (board-ref state (lookup (fifth lf))) #f))
		   (and (cache-square? (lookup (fifth lf)))
			(eq? (cache-ref state (lookup (fifth lf))) #f))))
	  (let ((state
		 (cond
		  ((board-square? (lookup (fourth lf)))
		   (make-state (board-replace state (lookup (fourth lf)) #f)
			       (state-cache-for-x state)
			       (state-cache-for-o state)
			       (state-player state)))
		  ((cache-square? (lookup (fourth lf)))
		   (case (cache-square-player (lookup (fourth lf)))
		    ((x)
		     (make-state (state-board state)
				 (cache-replace state (lookup (fourth lf)) #f)
				 (state-cache-for-o state)
				 (state-player state)))
		    ((o)
		     (make-state (state-board state)
				 (state-cache-for-x state)
				 (cache-replace state (lookup (fourth lf)) #f)
				 (state-player state)))
		    (else (fuck-up))))
		  (else (fuck-up)))))
	   (list (cond ((board-square? (lookup (fifth lf)))
			(make-state (board-replace
				     state
				     (lookup (fifth lf))
				     (piece-player (lookup (third lf))))
				    (state-cache-for-x state)
				    (state-cache-for-o state)
				    (state-player state)))
		       ((cache-square? (lookup (fifth lf)))
			(case (cache-square-player (lookup (fifth lf)))
			 ((x) (make-state (state-board state)
					  (cache-replace
					   state
					   (lookup (fifth lf))
					   (piece-player (lookup (third lf))))
					  (state-cache-for-o state)
					  (state-player state)))
			 ((o) (make-state (state-board state)
					  (state-cache-for-x state)
					  (cache-replace
					   state
					   (lookup (fifth lf))
					   (piece-player (lookup (third lf))))
					  (state-player state)))
			 (else (fuck-up))))
		       (else (fuck-up)))))
	  '()))
     (else (fuck-up))))
   (define (assertion lf bindings state)
    (define (lookup t)
     (let ((binding
	    (find-if (lambda (binding) (eq? t (binding-variable binding)))
		     bindings)))
      (unless binding (fuck-up))
      (binding-thing binding)))
    (define (assert p) (unless p (fail)))
    (case (first lf)
     ((then) (fail))
     ((and)
      (assertion (second lf) bindings state)
      (assertion (third lf) bindings state))
     ((some)
      (let ((thing (a-member-of things)))
       (assertion
	(third lf) (cons (make-binding (second lf) thing) bindings) state)
       (assertion
	(fourth lf) (cons (make-binding (second lf) thing) bindings) state)))
     ((every)
      (for-each
       (lambda (thing)
	(when (predicate (third lf)
			 (cons (make-binding (second lf) thing) bindings)
			 state)
	 (assertion
	  (fourth lf) (cons (make-binding(second lf) thing) bindings) state)))
       things))
     ((no) (fail))
     ((the)
      (unless (one (lambda (thing)
		    (predicate (third lf)
			       (cons (make-binding (second lf) thing) bindings)
			       state))
		   things)
       (fail))
      (assertion
       (fourth lf)
       (cons (make-binding
	      (second lf)
	      (find-if (lambda (thing)
			(predicate (third lf)
				   (cons (make-binding (second lf) thing)
					 bindings)
				   state))
		       things))
	     bindings)
       state))
     ;; 1
     ((player) (assert (player? (lookup (second lf)))))
     ((row) (assert (row? (lookup (second lf)))))
     ((column) (assert (column? (lookup (second lf)))))
     ((diagonal) (assert (diagonal? (lookup (second lf)))))
     ((board-square) (assert (board-square? (lookup (second lf)))))
     ((empty)
      ;; Could generalize to empty rows, columns, diagonals, cache (for a
      ;; player), and board.
      (cond ((board-square? (lookup (second lf)))
	     (assert (eq? (board-ref state (lookup (second lf))) #f)))
	    ((cache-square? (lookup (second lf)))
	     (assert (eq? (cache-ref state (lookup (second lf))) #f)))
	    (else (fail))))
     ((move) (fail))
     ((wins) (fail))
     ;; 1 or 2
     ((cache)
      (assert (case (length lf)
	       ((2) (cache? (lookup (second lf))))
	       ((3) (and (cache? (lookup (second lf)))
			 (player? (lookup (third lf)))
			 (eq? (cache-player (lookup (second lf)))
			      (player-player (lookup (third lf))))))
	       (else (fuck-up)))))
     ((square)
      (assert
       (case (length lf)
	((2)
	 (or (board-square? (lookup (second lf)))
	     (cache-square? (lookup (second lf)))))
	((3)
	 (or (and
	      (board-square? (lookup (second lf)))
	      (or (and (row? (lookup (third lf)))
		       (= (board-square-row (lookup (second lf)))
			  (row-row (lookup (third lf)))))
		  (and (column? (lookup (third lf)))
		       (= (board-square-column (lookup (second lf)))
			  (column-column (lookup (third lf)))))
		  (and (diagonal? (lookup (third lf)))
		       (or (and (= (diagonal-slope (lookup (third lf))) 1)
				(= (board-square-row (lookup (second lf)))
				   (board-square-column (lookup (second lf)))))
			   (and (= (diagonal-slope (lookup (third lf))) -1)
				(= (board-square-row (lookup (second lf)))
				   (- 2 (board-square-column
					 (lookup (second lf))))))))))
	     (and (cache-square? (lookup (second lf)))
		  (cache? (lookup (third lf)))
		  (eq? (cache-square-player (lookup (second lf)))
		       (cache-player (lookup (third lf)))))))
	(else (fuck-up)))))
     ((piece)
      (assert (case (length lf)
	       ((2) (piece? (lookup (second lf))))
	       ((3) (and (piece? (lookup (second lf)))
			 (player? (lookup (third lf)))
			 (eq? (piece-player (lookup (second lf)))
			      (player-player (lookup (third lf))))))
	       (else (fuck-up)))))
     ((cache-square)
      (assert (case (length lf)
	       ((2) (cache-square? (lookup (second lf))))
	       ((3) (and (cache-square? (lookup (second lf)))
			 (player? (lookup (third lf)))
			 (eq? (cache-square-player (lookup (second lf)))
			      (player-player (lookup (third lf))))))
	       (else (fuck-up)))))
     ;; 2
     ((opponent)
      (assert (and (player? (lookup (second lf)))
		   (player? (lookup (third lf)))
		   (not (eq? (player-player (lookup (second lf)))
			     (player-player (lookup (third lf))))))))
     ((distant-row)
      (assert (and (row? (lookup (second lf)))
		   (player? (lookup (third lf)))
		   (or (and (eq? (player-player (lookup (third lf))) 'x)
			    (= (row-row (lookup (second lf))) 2))
		       (and (eq? (player-player (lookup (third lf))) 'o)
			    (= (row-row (lookup (second lf))) 0))))))
     ((close-row)
      (assert (and (row? (lookup (second lf)))
		   (player? (lookup (third lf)))
		   (or (and (eq? (player-player (lookup (third lf))) 'x)
			    (= (row-row (lookup (second lf))) 0))
		       (and (eq? (player-player (lookup (third lf))) 'o)
			    (= (row-row (lookup (second lf))) 2))))))
     ;; Could generalize to rows, columns, diagonals, cache (for a player), and
     ;; board.
     ((has)
      (cond ((and (board-square? (lookup (second lf)))
		  (piece? (lookup (third lf))))
	     (assert (eq? (board-ref state (lookup (second lf)))
			  (piece-player (lookup (third lf))))))
	    ((and (cache-square? (lookup (second lf)))
		  (piece? (lookup (third lf))))
	     (assert (eq? (cache-ref state (lookup (second lf)))
			  (piece-player (lookup (third lf))))))
	    (else (fail))))
     ;; 3
     ((forward-adjacent-square)
      (assert (and (board-square? (lookup (second lf)))
		   (player? (lookup (third lf)))
		   (board-square? (lookup (fourth lf)))
		   (= (board-square-column (lookup (second lf)))
		      (board-square-column (lookup (fourth lf))))
		   (= (board-square-row (lookup (second lf)))
		      (+ (case (player-player (lookup (third lf)))
			  ((x) 1)
			  ((o) -1)
			  (else (fuck-up)))
			 (board-square-row (lookup (fourth lf))))))))
     ((forward-diagonal-square)
      (assert (and (board-square? (lookup (second lf)))
		   (player? (lookup (third lf)))
		   (board-square? (lookup (fourth lf)))
		   (or (= (board-square-column (lookup (second lf)))
			  (+ (board-square-column (lookup (fourth lf))) 1))
		       (= (board-square-column (lookup (second lf)))
			  (- (board-square-column (lookup (fourth lf))) 1)))
		   (= (board-square-row (lookup (second lf)))
		      (+ (case (player-player (lookup (third lf)))
			  ((x) 1)
			  ((o) -1)
			  (else (fuck-up)))
			 (board-square-row (lookup (fourth lf))))))))
     ;; 4
     ((moving) (fail))
     (else (fuck-up))))
   ((case kind
     ((predicate) predicate)
     ((function) function)
     ((assertion) assertion)
     (else (fuck-up)))
    lf (list (make-binding 'p (make-player (state-player state)))) state)))

 (define (list->state l)
  (make-state (vector (vector (list-ref l 0) (list-ref l 1) (list-ref l 2))
		      (vector (list-ref l 3) (list-ref l 4) (list-ref l 5))
		      (vector (list-ref l 6) (list-ref l 7) (list-ref l 8)))
	      (vector (list-ref l 9)
		      (list-ref l 10)
		      (list-ref l 11)
		      (list-ref l 12)
		      (list-ref l 13))
	      (vector (list-ref l 14)
		      (list-ref l 15)
		      (list-ref l 16)
		      (list-ref l 17)
		      (list-ref l 18))
	      'x))

 (define pretty-print write)

 (define-syntax for-effects
  (syntax-rules () ((for-effects e ...) (begin (domain (begin e ... #f)) #f))))

 (define (test-lexicon sentences)
  (for-each (lambda (sentence)
	     (for-each (lambda (word)
			(unless (some (lambda (entry) (eq? (second entry) word))
				      *lexicon*)
			 (write word)
			 (newline)))
		       sentence))
	    sentences))

 (define (simplify parse)
  (if (memq (first parse) '(d n a p v coord c))
      (list (first parse) (second parse))
      (cons (first parse) (map simplify (rest parse)))))

 (define (test-grammar sentences)
  (for-each (lambda (sentence)
	     (write sentence)
	     (newline)
	     (for-effects (pretty-print (simplify (a-parse sentence)))
			  (newline))
	     (newline))
	    sentences))

 (define (test-parse->lf sentences)
  (for-each (lambda (sentence)
	     (write sentence)
	     (newline)
	     (for-effects (pretty-print (parse->lf (a-parse sentence)))
			  (newline))
	     (newline))
	    sentences))

 (define (test-semantics sentences)
  (for-each
   (lambda (sentence)
    (write sentence)
    (newline)
    (for-effects
     (pretty-print (a-quantifier-scoping
		    (declarative-sentence
		     (an-anaphora-resolution (parse->lf (a-parse sentence))))))
     (newline))
    (newline))
   sentences))

 (define (sentence->rule sentence)
  (a-quantifier-scoping
   (declarative-sentence
    (an-anaphora-resolution (parse->lf (a-parse sentence))))))

 (define (sentences->rules sentences) (map sentence->rule sentences))

 (define (initial-state sentences)
  (last
   (domain
    (let ((rules (sentences->rules sentences)))
     (maximal
      (lambda (xs)
       (let ((state (list->state xs)))
	(for-each (lambda (lf)
		   (when (equal? (second lf) '(initial-state))
		    (interpret (third lf) 'assertion rules state)))
		  rules)
	(list->state (map force-nondeterministic-promise xs))))
      (map-n (lambda (i) (delayed-a-member-of '(#f x o))) 19))))))

 (define (initial-state? sentences state)
  (possibly?
   (domain
    (let ((rules (sentences->rules sentences)))
     (some (lambda (lf)
	    (and (equal? (second lf) '(initial-state))
		 (interpret (third lf) 'predicate rules (turn state))))
	   rules)))))

 (define (win? sentences state)
  ;; Win is applied after a move.
  (possibly?
   (domain
    (let ((rules (sentences->rules sentences)))
     (some (lambda (lf)
	    (and (equal? (second lf) '(wins p))
		 (interpret (third lf) 'predicate rules (turn state))))
	   rules)))))

 (define (draw? sentences state)
  ;; Draw is applied before a move.
  (possibly?
   (domain
    (let ((rules (sentences->rules sentences)))
     (some (lambda (lf)
	    (and (equal? (second lf) '(draws p))
		 (interpret (third lf) 'predicate rules state)))
	   rules)))))

 (define (legal-moves sentences state)
  (remove-duplicatesp
   (lambda (state1 state2) (equal? (state-board state1) (state-board state2)))
   (fold
    append
    '()
    (domain
     (let ((rules (sentences->rules sentences)))
      (map-reduce append
		  '()
		  (lambda (lf)
		   (if (equal? (second lf) '(moves p))
		       (map turn (interpret (third lf) 'function rules state))
		       '()))
		  rules))))))

 (define (random-game sentences)
  (let loop ((states (list (initial-state sentences))))
   (if (or (win? sentences (first states)) (draw? sentences (first states)))
       (reverse states)
       ;; needs work: to make random
       (loop (cons (first (legal-moves sentences (first states))) states)))))

 (define (valid? sentences games)
  (every (lambda (game)
	  (and (initial-state? sentences (first game))
	       (or (win? sentences (last game)) (draw? sentences (last game)))
	       (every (lambda (state next-state)
		       (member next-state (legal-moves sentences state)))
		      (but-last game)
		      (rest game))))
	 games))

 (define *tic-tac-toe*
  '((every cache square for every player has some piece of that player)
    (a player moves by moving some piece of that player from some cache square
       for that player to some empty board square)
    (a player wins when every square in some row has some piece of that player)
    (a player wins when every square in some column has some piece of that
       player)
    (a player wins when every square in some diagonal has some piece of that
       player)
    (a player draws when no player wins and that player has no move)))

 (define *hexapawn*
  '((every square in the close row for every player has some piece of that
	   player)
    (a player moves by moving some piece of that player from some square to some
       empty forward-adjacent square for that player of that square)
    (a player moves by moving some piece of the opponent of that player from
       some forward-diagonal square for that player of some square to some
       cache square for that opponent then moving the piece of that player from
       that square to that forward-diagonal square)
    (a player wins when some square in the distant row for that player has some
       piece of that player)
    (a player draws when no player wins and that player has no move))))
