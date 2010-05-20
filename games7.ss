#!r6rs

(library
 (games7)
 (export make-state parse-type pretty-type parse-expression pretty-expression
	 pretty-value pretty-environment
	 type free-variables equal-type? equal-value?
	 *s* *n* *np* *d*
	 *pp/of/np* *pp/for/np* *pp/in/np* *pp/from/np* *pp/to/np*
	 *p/in-np* *p/for-np* *p/of-np* *p/from-np* *p/to-np*
	 *n-pp/of/np* *n-pp/for/np* *n-pp/in/np*
	 *a* *a-pp/for/np* *a-pp/for/np-pp/of/np*
	 *vp* *pp/by/vp* *p-vp* *pp/when/s* *p-s* *v* *v-pp/by/vp*
	 *v-pp/when/s* *v-np* *v-np-pp/from/np-pp/to/np* *coord-vp* *coord-s*
	 *lexicon* board-ref cache-ref vector-replace matrix-replace
	 board-replace cache-replace turn evaluate
	 call a-type a-lambda-expression-of-type a-value-of-type
	 a-phrase-of-type a-phrase-of-value a-bottom-up-parse parse-length
	 a-top-down-parse things a-typed-apply possibly-true?
	 *tic-tac-toe* *hexapawn*)
 (import (rnrs) (QobiScheme) (nondeterministic-scheme))

 (define-record-type typed-meaning (fields type meaning))

 (define-record-type stack-entry (fields type parse))

 (define-record-type result (fields parse words))

 (define-record-type state (fields board cache-for-x cache-for-o player))

 (define-record-type player (fields player))

 (define-record-type piece (fields player))

 (define-record-type board-square (fields row column))

 (define-record-type row (fields row))

 (define-record-type column (fields column))

 (define-record-type diagonal (fields slope))

 (define-record-type cache-square (fields player i))

 (define-record-type cache (fields player))

 (define-record-type move (fields))

 (define-record-type leftward-arrow-type (fields result argument))

 (define-record-type rightward-arrow-type (fields argument result))

 (define-record-type variable-access-expression (fields variable type))

 (define-record-type lambda-expression
  (fields variable expression variables types type))

 (define-record-type application (fields callee argument type))

 (define-record-type and-expression (fields expressions))

 (define-record-type or-expression (fields expressions))

 (define-record-type a-expression (fields expression1 expression2))

 (define-record-type some-expression (fields expression1 expression2))

 (define-record-type every-expression (fields expression1 expression2))

 (define-record-type that-expression (fields expression1 expression2))

 (define-record-type no-expression (fields expression1 expression2))

 (define-record-type the-expression (fields expression1 expression2))

 (define-record-type player?-expression (fields expression))

 (define-record-type row?-expression (fields expression))

 (define-record-type column?-expression (fields expression))

 (define-record-type diagonal?-expression (fields expression))

 (define-record-type move?-expression (fields expression))

 (define-record-type opponent?-expression (fields expression1 expression2))

 (define-record-type cache?-expression (fields expression1 expression2))

 (define-record-type square?-expression (fields expression1 expression2))

 (define-record-type piece?-expression (fields expression1 expression2))

 (define-record-type distant?-expression (fields expression1 expression2))

 (define-record-type close?-expression (fields expression1 expression2))

 (define-record-type forward-adjacent?-expression
  (fields expression1 expression2 expression3))

 (define-record-type forward-diagonal?-expression
  (fields expression1 expression2 expression3))

 (define-record-type empty?-expression (fields expression))

 (define-record-type has?-expression (fields expression1 expression2))

 (define-record-type binding (fields variable value))

 (define-record-type closure (fields environment expression))

 (define (parse-type type)
  (cond ((eq? type 'boolean) 'boolean)
	((eq? type 'thing) 'thing)
	((eq? type 'pp/of/np) 'pp/of/np)
	((eq? type 'pp/for/np) 'pp/for/np)
	((eq? type 'pp/in/np) 'pp/in/np)
	((eq? type 'pp/from/np) 'pp/from/np)
	((eq? type 'pp/to/np) 'pp/to/np)
	((eq? type 'pp/by/vp) 'pp/by/vp)
	((eq? type 'pp/when/s) 'pp/when/s)
	((and (list? type) (= (length type) 3) (eq? (first type) '<-))
	 (make-leftward-arrow-type
	  (parse-type (second type)) (parse-type (third type))))
	((and (list? type) (= (length type) 3) (eq? (first type) '->))
	 (make-rightward-arrow-type
	  (parse-type (second type)) (parse-type (third type))))
	(else (error #f "Bad type"))))

 (define (pretty-type type)
  (cond ((equal-type? type 'boolean) 'boolean)
	((equal-type? type 'thing) 'thing)
	((equal-type? type 'pp/of/np) 'pp/of/np)
	((equal-type? type 'pp/for/np) 'pp/for/np)
	((equal-type? type 'pp/in/np) 'pp/in/np)
	((equal-type? type 'pp/from/np) 'pp/from/np)
	((equal-type? type 'pp/to/np) 'pp/to/np)
	((equal-type? type 'pp/by/vp) 'pp/by/vp)
	((equal-type? type 'pp/when/s) 'pp/when/s)
	((leftward-arrow-type? type)
	 `(<- ,(pretty-type (leftward-arrow-type-result type))
	      ,(pretty-type (leftward-arrow-type-argument type))))
	((rightward-arrow-type? type)
	 `(-> ,(pretty-type (rightward-arrow-type-argument type))
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
     (unless (or (leftward-arrow-type? type) (rightward-arrow-type? type))
      (error #f "lambda expression not of function type"))
     (let* ((variable (first (second expression)))
	    (expression (loop (third expression)
			      (if (leftward-arrow-type? type)
				  (leftward-arrow-type-result type)
				  (rightward-arrow-type-result type))
			      (cons (first (second expression)) variables)
			      (cons (if (leftward-arrow-type? type)
					(leftward-arrow-type-argument type)
					(rightward-arrow-type-argument type))
				    types)))
	    (free-variables (removeq variable (free-variables expression))))
      (make-lambda-expression
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
	  (= (length expression) 3)
	  (eq? (first expression) 'a))
     (unless (equal-type? type 'boolean)
      (error #f "a expression not of type boolean"))
     (make-a-expression (loop (second expression)
			      (make-rightward-arrow-type 'thing 'boolean)
			      variables
			      types)
			(loop (third expression)
			      (make-rightward-arrow-type 'thing 'boolean)
			      variables
			      types)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'some))
     (unless (equal-type? type 'boolean)
      (error #f "some expression not of type boolean"))
     (make-some-expression (loop (second expression)
				 (make-rightward-arrow-type 'thing 'boolean)
				 variables
				 types)
			   (loop (third expression)
				 (make-rightward-arrow-type 'thing 'boolean)
				 variables
				 types)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'every))
     (unless (equal-type? type 'boolean)
      (error #f "every expression not of type boolean"))
     (make-every-expression (loop (second expression)
				  (make-rightward-arrow-type 'thing 'boolean)
				  variables
				  types)
			    (loop (third expression)
				  (make-rightward-arrow-type 'thing 'boolean)
				  variables
				  types)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'that))
     (unless (equal-type? type 'boolean)
      (error #f "that expression not of type boolean"))
     (make-that-expression (loop (second expression)
				 (make-rightward-arrow-type 'thing 'boolean)
				 variables
				 types)
			   (loop (third expression)
				 (make-rightward-arrow-type 'thing 'boolean)
				 variables
				 types)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'no))
     (unless (equal-type? type 'boolean)
      (error #f "no expression not of type boolean"))
     (make-no-expression (loop (second expression)
			       (make-rightward-arrow-type 'thing 'boolean)
			       variables
			       types)
			 (loop (third expression)
			       (make-rightward-arrow-type 'thing 'boolean)
			       variables
			       types)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'the))
     (unless (equal-type? type 'boolean)
      (error #f "the expression not of type boolean"))
     (make-the-expression (loop (second expression)
				(make-rightward-arrow-type 'thing 'boolean)
				variables
				types)
			  (loop (third expression)
				(make-rightward-arrow-type 'thing 'boolean)
				variables
				types)))
    ((and (list? expression)
	  (= (length expression) 2)
	  (eq? (first expression) 'player?))
     (unless (equal-type? type 'boolean)
      (error #f "player? expression not of type boolean"))
     (make-player?-expression
      (loop (second expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 2)
	  (eq? (first expression) 'row?))
     (unless (equal-type? type 'boolean)
      (error #f "row? expression not of type boolean"))
     (make-row?-expression (loop (second expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 2)
	  (eq? (first expression) 'column?))
     (unless (equal-type? type 'boolean)
      (error #f "column? expression not of type boolean"))
     (make-column?-expression
      (loop (second expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 2)
	  (eq? (first expression) 'diagonal?))
     (unless (equal-type? type 'boolean)
      (error #f "diagonal? expression not of type boolean"))
     (make-diagonal?-expression
      (loop (second expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 2)
	  (eq? (first expression) 'move?))
     (unless (equal-type? type 'boolean)
      (error #f "move? expression not of type boolean"))
     (make-move?-expression (loop (second expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'opponent?))
     (unless (equal-type? type 'boolean)
      (error #f "opponent? expression not of type boolean"))
     (make-opponent?-expression
      (loop (second expression) 'thing variables types)
      (loop (third expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'cache?))
     (unless (equal-type? type 'boolean)
      (error #f "cache? expression not of type boolean"))
     (make-cache?-expression (loop (second expression) 'thing variables types)
			     (loop (third expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'square?))
     (unless (equal-type? type 'boolean)
      (error #f "square? expression not of type boolean"))
     (make-square?-expression (loop (second expression) 'thing variables types)
			      (loop (third expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'piece?))
     (unless (equal-type? type 'boolean)
      (error #f "piece? expression not of type boolean"))
     (make-piece?-expression (loop (second expression) 'thing variables types)
			     (loop (third expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'distant?))
     (unless (equal-type? type 'boolean)
      (error #f "distant? expression not of type boolean"))
     (make-distant?-expression
      (loop (second expression) 'thing variables types)
      (loop (third expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'close?))
     (unless (equal-type? type 'boolean)
      (error #f "close? expression not of type boolean"))
     (make-close?-expression (loop (second expression) 'thing variables types)
			     (loop (third expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 4)
	  (eq? (first expression) 'forward-adjacent?))
     (unless (equal-type? type 'boolean)
      (error #f "forward-adjacent? expression not of type boolean"))
     (make-forward-adjacent?-expression
      (loop (second expression) 'thing variables types)
      (loop (third expression) 'thing variables types)
      (loop (fourth expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 4)
	  (eq? (first expression) 'forward-diagonal?))
     (unless (equal-type? type 'boolean)
      (error #f "forward-diagonal? expression not of type boolean"))
     (make-forward-diagonal?-expression
      (loop (second expression) 'thing variables types)
      (loop (third expression) 'thing variables types)
      (loop (fourth expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 2)
	  (eq? (first expression) 'empty?))
     (unless (equal-type? type 'boolean)
      (error #f "empty? expression not of type boolean"))
     (make-empty?-expression (loop (second expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'has?))
     (unless (equal-type? type 'boolean)
      (error #f "has? expression not of type boolean"))
     (make-has?-expression (loop (second expression) 'thing variables types)
			   (loop (third expression) 'thing variables types)))
    ((and (list? expression) (= (length expression) 3))
     ;; needs work: should do type inference
     (let ((callee-type (parse-type (third expression))))
      (unless (or (and (leftward-arrow-type? callee-type)
		       (equal-type? (leftward-arrow-type-result callee-type)
				    type))
		  (and (rightward-arrow-type? callee-type)
		       (equal-type? (rightward-arrow-type-result callee-type)
				    type)))
       (error #f "Type error"))
      (make-application (loop (first expression) callee-type variables types)
			(loop (second expression)
			      ((if (leftward-arrow-type? callee-type)
				   leftward-arrow-type-argument
				   rightward-arrow-type-argument)
			       callee-type)
			      variables
			      types)
			type)))
    (else (error #f "Bad expression")))))

 (define (pretty-expression expression)
  (cond
   ((variable-access-expression? expression)
    (variable-access-expression-variable expression))
   ((lambda-expression? expression)
    `(lambda (,(lambda-expression-variable expression))
      ,(pretty-expression (lambda-expression-expression expression))))
   ((and-expression? expression)
    `(and ,@(map pretty-expression (and-expression-expressions expression))))
   ((or-expression? expression)
    `(or ,@(map pretty-expression (or-expression-expressions expression))))
   ((a-expression? expression)
    `(a ,(pretty-expression (a-expression-expression1 expression))
	,(pretty-expression (a-expression-expression2 expression))))
   ((some-expression? expression)
    `(some ,(pretty-expression (some-expression-expression1 expression))
	   ,(pretty-expression (some-expression-expression2 expression))))
   ((every-expression? expression)
    `(every ,(pretty-expression (every-expression-expression1 expression))
	    ,(pretty-expression (every-expression-expression2 expression))))
   ((that-expression? expression)
    `(that ,(pretty-expression (that-expression-expression1 expression))
	   ,(pretty-expression (that-expression-expression2 expression))))
   ((no-expression? expression)
    `(no ,(pretty-expression (no-expression-expression1 expression))
	 ,(pretty-expression (no-expression-expression2 expression))))
   ((the-expression? expression)
    `(the ,(pretty-expression (the-expression-expression1 expression))
	  ,(pretty-expression (the-expression-expression2 expression))))
   ((player?-expression? expression)
    `(player? ,(pretty-expression (player?-expression-expression expression))))
   ((row?-expression? expression)
    `(row? ,(pretty-expression (row?-expression-expression expression))))
   ((column?-expression? expression)
    `(column? ,(pretty-expression (column?-expression-expression expression))))
   ((diagonal?-expression? expression)
    `(diagonal?
      ,(pretty-expression (diagonal?-expression-expression expression))))
   ((move?-expression? expression)
    `(move? ,(pretty-expression (move?-expression-expression expression))))
   ((opponent?-expression? expression)
    `(opponent?
      ,(pretty-expression (opponent?-expression-expression1 expression))
      ,(pretty-expression (opponent?-expression-expression2 expression))))
   ((cache?-expression? expression)
    `(cache? ,(pretty-expression (cache?-expression-expression1 expression))
	     ,(pretty-expression (cache?-expression-expression2 expression))))
   ((square?-expression? expression)
    `(square? ,(pretty-expression (square?-expression-expression1 expression))
	      ,(pretty-expression (square?-expression-expression2 expression))))
   ((piece?-expression? expression)
    `(piece? ,(pretty-expression (piece?-expression-expression1 expression))
	     ,(pretty-expression (piece?-expression-expression2 expression))))
   ((distant?-expression? expression)
    `(distant?
      ,(pretty-expression (distant?-expression-expression1 expression))
      ,(pretty-expression (distant?-expression-expression2 expression))))
   ((close?-expression? expression)
    `(close? ,(pretty-expression (close?-expression-expression1 expression))
	     ,(pretty-expression (close?-expression-expression2 expression))))
   ((forward-adjacent?-expression? expression)
    `(forward-adjacent?
      ,(pretty-expression (forward-adjacent?-expression-expression1 expression))
      ,(pretty-expression (forward-adjacent?-expression-expression2 expression))
      ,(pretty-expression
	(forward-adjacent?-expression-expression3 expression))))
   ((forward-diagonal?-expression? expression)
    `(forward-diagonal?
      ,(pretty-expression (forward-diagonal?-expression-expression1 expression))
      ,(pretty-expression (forward-diagonal?-expression-expression2 expression))
      ,(pretty-expression
	(forward-diagonal?-expression-expression3 expression))))
   ((empty?-expression? expression)
    `(empty? ,(pretty-expression (empty?-expression-expression expression))))
   ((has?-expression? expression)
    `(has? ,(pretty-expression (has?-expression-expression1 expression))
	   ,(pretty-expression (has?-expression-expression2 expression))))
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
	((and-expression? expression) 'boolean)
	((or-expression? expression) 'boolean)
	((a-expression? expression) 'boolean)
	((some-expression? expression) 'boolean)
	((every-expression? expression) 'boolean)
	((that-expression? expression) 'boolean)
	((no-expression? expression) 'boolean)
	((the-expression? expression) 'boolean)
	((player?-expression? expression) 'boolean)
	((row?-expression? expression) 'boolean)
	((column?-expression? expression) 'boolean)
	((diagonal?-expression? expression) 'boolean)
	((move?-expression? expression) 'boolean)
	((opponent?-expression? expression) 'boolean)
	((cache?-expression? expression) 'boolean)
	((square?-expression? expression) 'boolean)
	((piece?-expression? expression) 'boolean)
	((distant?-expression? expression) 'boolean)
	((close?-expression? expression) 'boolean)
	((forward-adjacent?-expression? expression) 'boolean)
	((forward-diagonal?-expression? expression) 'boolean)
	((empty?-expression? expression) 'boolean)
	((has?-expression? expression) 'boolean)
	((application? expression) (application-type expression))
	(else (fuck-up))))

 (define (free-variables expression)
  (cond
   ((variable-access-expression? expression)
    (list (variable-access-expression-variable expression)))
   ((lambda-expression? expression) (lambda-expression-variables expression))
   ((and-expression? expression)
    (map-reduce
     unionq '() free-variables (and-expression-expressions expression)))
   ((or-expression? expression)
    (map-reduce
     unionq '() free-variables (or-expression-expressions expression)))
   ((a-expression? expression)
    (unionq (free-variables (a-expression-expression1 expression))
	    (free-variables (a-expression-expression2 expression))))
   ((some-expression? expression)
    (unionq (free-variables (some-expression-expression1 expression))
	    (free-variables (some-expression-expression2 expression))))
   ((every-expression? expression)
    (unionq (free-variables (every-expression-expression1 expression))
	    (free-variables (every-expression-expression2 expression))))
   ((that-expression? expression)
    (unionq (free-variables (that-expression-expression1 expression))
	    (free-variables (that-expression-expression2 expression))))
   ((no-expression? expression)
    (unionq (free-variables (no-expression-expression1 expression))
	    (free-variables (no-expression-expression2 expression))))
   ((the-expression? expression)
    (unionq (free-variables (the-expression-expression1 expression))
	    (free-variables (the-expression-expression2 expression))))
   ((player?-expression? expression)
    (free-variables (player?-expression-expression expression)))
   ((row?-expression? expression)
    (free-variables (row?-expression-expression expression)))
   ((column?-expression? expression)
    (free-variables (column?-expression-expression expression)))
   ((diagonal?-expression? expression)
    (free-variables (diagonal?-expression-expression expression)))
   ((move?-expression? expression)
    (free-variables (move?-expression-expression expression)))
   ((opponent?-expression? expression)
    (unionq (free-variables (opponent?-expression-expression1 expression))
	    (free-variables (opponent?-expression-expression2 expression))))
   ((cache?-expression? expression)
    (unionq (free-variables (cache?-expression-expression1 expression))
	    (free-variables (cache?-expression-expression2 expression))))
   ((square?-expression? expression)
    (unionq (free-variables (square?-expression-expression1 expression))
	    (free-variables (square?-expression-expression2 expression))))
   ((piece?-expression? expression)
    (unionq (free-variables (piece?-expression-expression1 expression))
	    (free-variables (piece?-expression-expression2 expression))))
   ((distant?-expression? expression)
    (unionq (free-variables (distant?-expression-expression1 expression))
	    (free-variables (distant?-expression-expression2 expression))))
   ((close?-expression? expression)
    (unionq (free-variables (close?-expression-expression1 expression))
	    (free-variables (close?-expression-expression2 expression))))
   ((forward-adjacent?-expression? expression)
    (unionq
     (free-variables (forward-adjacent?-expression-expression1 expression))
     (unionq
      (free-variables (forward-adjacent?-expression-expression2 expression))
      (free-variables (forward-adjacent?-expression-expression3 expression)))))
   ((forward-diagonal?-expression? expression)
    (unionq
     (free-variables (forward-diagonal?-expression-expression1 expression))
     (unionq
      (free-variables (forward-diagonal?-expression-expression2 expression))
      (free-variables (forward-diagonal?-expression-expression3 expression)))))
   ((empty?-expression? expression)
    (free-variables (empty?-expression-expression expression)))
   ((has?-expression? expression)
    (unionq (free-variables (has?-expression-expression1 expression))
	    (free-variables (has?-expression-expression2 expression))))
   ((application? expression)
    (unionq (free-variables (application-callee expression))
	    (free-variables (application-argument expression))))
   (else (fuck-up))))

 (define (equal-type? type1 type2)
  ;; needs work: pp/{of,for,in,from,to}/np, pp/by/vp, and pp/when/s
  (or (eq? type1 type2)
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
   (unless (and (lambda-expression? expression)
		(null? (lambda-expression-variables expression)))
    (fuck-up))
   (make-typed-meaning type expression)))

 (define *s* 'boolean)

 (define *n* '(-> thing boolean))

 (define *np* `(-> ,*n* boolean))

 (define *d* `(-> ,*n* ,*np*))

 (define *pp/of/np* 'pp/of/np)

 (define *pp/for/np* 'pp/for/np)

 (define *pp/in/np* 'pp/in/np)

 (define *pp/from/np* 'pp/from/np)

 (define *pp/to/np* 'pp/to/np)

 (define *p/in-np* `(-> ,*np* ,*pp/in/np*))

 (define *p/for-np* `(-> ,*np* ,*pp/for/np*))

 (define *p/of-np* `(-> ,*np* ,*pp/of/np*))

 (define *p/from-np* `(-> ,*np* ,*pp/from/np*))

 (define *p/to-np* `(-> ,*np* ,*pp/to/np*))

 (define *n-pp/of/np* `(-> ,*pp/of/np* ,*n*))

 (define *n-pp/for/np* `(-> ,*pp/for/np* ,*n*))

 (define *n-pp/in/np* `(-> ,*pp/in/np* ,*n*))

 (define *a* `(-> ,*n* ,*n*))

 (define *a-pp/for/np* `(-> ,*n* (-> ,*pp/for/np* ,*n*)))

 (define *a-pp/for/np-pp/of/np*
  `(-> ,*n* (-> ,*pp/for/np* (-> ,*pp/of/np* ,*n*))))

 (define *vp* `(<- ,*s* ,*np*))

 (define *pp/by/vp* 'pp/by/vp)

 (define *p-vp* `(-> ,*vp* ,*pp/by/vp*))

 (define *pp/when/s* 'pp/when/s)

 (define *p-s* `(-> ,*s* ,*pp/when/s*))

 (define *v* *vp*)

 (define *v-pp/by/vp* `(-> ,*pp/by/vp* ,*vp*))

 (define *v-pp/when/s* `(-> ,*pp/when/s* ,*vp*))

 (define *v-np* `(-> ,*np* ,*vp*))

 (define *v-np-pp/from/np-pp/to/np*
  `(-> ,*np* (-> ,*pp/from/np* (-> ,*pp/to/np* ,*vp*))))

 (define *coord-vp* `(<- (-> ,*vp* ,*vp*) ,*vp*))

 (define *coord-s* `(<- (-> ,*s* ,*s*) ,*s*))

 ;; needs work: subcategorization of adjectives based on class of noun
 ;;             complement
 ;; needs work: subcategorization of nouns, adjectives, and verbs based on
 ;;             class of head noun of np complement of pp complement
 ;; needs work: subcategorization of prepositions and verbs based on class of
 ;;             head noun of np complement
 ;; needs work: eliminated relative clauses for now since the current rules
 ;;             don't use them
 ;; needs work: eliminated restricted associativity of coordination and instead
 ;;             have type-restricted coordination; can't coordinate nouns, NPs,
 ;;             determiners, prepositions, PPs, adjectives, or verbs
 ;; needs work: ambiguity between ((a n) pp) and (a (n pp))
 ;; needs work: coordination ambiguity due to lack of declarative sentence
 ;;             constraint
 (define *lexicon*
  (remove-if-not
   (lambda (x) x)
   (list
    ;; needs work: should abstract lexical entries
    (and #f
	 (cons 'a
	       (create-typed-meaning
		*d* '(lambda (noun1) (lambda (noun2) (a noun1 noun2))))))
    (cons 'some
	  (create-typed-meaning
	   *d* '(lambda (noun1) (lambda (noun2) (some noun1 noun2)))))
    (cons 'every
	  (create-typed-meaning
	   *d* '(lambda (noun1) (lambda (noun2) (every noun1 noun2)))))
    (and #f
	 (cons 'that
	       (create-typed-meaning
		*d* '(lambda (noun1) (lambda (noun2) (that noun1 noun2))))))
    (cons 'no
	  (create-typed-meaning
	   *d* '(lambda (noun1) (lambda (noun2) (no noun1 noun2)))))
    (cons 'the
	  (create-typed-meaning
	   *d* '(lambda (noun1) (lambda (noun2) (the noun1 noun2)))))
    ;;
    (cons 'player (create-typed-meaning *n* '(lambda (thing) (player? thing))))
    (cons 'opponent
	  (create-typed-meaning
	   *n*
	   '(lambda (thing1)
	     (some (lambda (thing2) (player? thing2))
		   (lambda (thing2) (opponent? thing1 thing2))))))
    (cons 'opponent
	  (create-typed-meaning
	   *n-pp/of/np*			;player
	   '(lambda (np)
	     (lambda (thing1)
	      (np (lambda (thing2) (opponent? thing1 thing2))
		  (-> (-> thing boolean) boolean))))))
    (cons 'row (create-typed-meaning *n* '(lambda (thing) (row? thing))))
    (cons 'column (create-typed-meaning *n* '(lambda (thing) (column? thing))))
    (cons
     'diagonal (create-typed-meaning *n* '(lambda (thing) (diagonal? thing))))
    (cons 'cache
	  (create-typed-meaning
	   *n*
	   '(lambda (thing1)
	     (some (lambda (thing2) (player? thing2))
		   (lambda (thing2) (cache? thing1 thing2))))))
    (cons 'cache
	  (create-typed-meaning
	   *n-pp/for/np*		;player
	   '(lambda (np)
	     (lambda (thing1)
	      (np (lambda (thing2) (cache? thing1 thing2))
		  (-> (-> thing boolean) boolean))))))
    (cons 'square
	  (create-typed-meaning
	   *n*
	   '(lambda (thing1)
	     (some (lambda (thing2)
		    (or (row? thing2)
			(column? thing2)
			(diagonal? thing2)
			(some (lambda (thing3) (player? thing3))
			      (lambda (thing3) (cache? thing2 thing3)))))
		   (lambda (thing2) (square? thing1 thing2))))))
    (cons 'square
	  (create-typed-meaning
	   *n-pp/of/np*			;line
	   '(lambda (np)
	     (lambda (thing1)
	      (np (lambda (thing2) (square? thing1 thing2))
		  (-> (-> thing boolean) boolean))))))
    (cons 'square
	  (create-typed-meaning
	   *n-pp/in/np*			;line
	   '(lambda (np)
	     (lambda (thing1)
	      (np (lambda (thing2) (square? thing1 thing2))
		  (-> (-> thing boolean) boolean))))))
    (cons 'piece
	  (create-typed-meaning
	   *n*
	   '(lambda (thing1)
	     (some (lambda (thing2) (player? thing2))
		   (lambda (thing2) (piece? thing1 thing2))))))
    (cons 'piece
	  (create-typed-meaning
	   *n-pp/of/np*			;player
	   '(lambda (np)
	     (lambda (thing1)
	      (np (lambda (thing2) (piece? thing1 thing2))
		  (-> (-> thing boolean) boolean))))))
    (cons 'move (create-typed-meaning *n* '(lambda (thing) (move? thing))))
    ;;
    ;; needs work: In all of the following, need to deal with the lexical
    ;;             ambiguity of scoping of the "and" that implements adjectival
    ;;             modification relative the the quantifiers of the (implicit)
    ;;             complements of the adjecive.
    (cons 'distant
	  (create-typed-meaning
	   *a*				;row
	   '(lambda (noun)
	     (lambda (thing1)
	      (and (noun thing1 (-> thing boolean))
		   (some (lambda (thing2) (player? thing2))
			 (lambda (thing2) (distant? thing1 thing2))))))))
    (cons 'distant
	  (create-typed-meaning
	   *a-pp/for/np*		;row player
	   '(lambda (noun)
	     (lambda (np)
	      (lambda (thing1)
	       (and (noun thing1 (-> thing boolean))
		    (np (lambda (thing2) (distant? thing1 thing2))
			(-> (-> thing boolean) boolean))))))))
    (cons 'close
	  (create-typed-meaning
	   *a*				;row
	   '(lambda (noun)
	     (lambda (thing1)
	      (and (noun thing1 (-> thing boolean))
		   (some (lambda (thing2) (player? thing2))
			 (lambda (thing2) (close? thing1 thing2))))))))
    (cons 'close
	  (create-typed-meaning
	   *a-pp/for/np*		;row player
	   '(lambda (noun)
	     (lambda (np)
	      (lambda (thing1)
	       (and (noun thing1 (-> thing boolean))
		    (np (lambda (thing2) (close? thing1 thing2))
			(-> (-> thing boolean) boolean))))))))
    ;; lexicalization
    (cons
     'forward-adjacent
     (create-typed-meaning
      *a*				;square
      '(lambda (noun)
	(lambda (thing1)
	 (and
	  (noun thing1 (-> thing boolean))
	  (some (lambda (thing2) (player? thing2))
		(lambda (thing2)
		 (some
		  (lambda (thing3)
		   (or (row? thing3) (column? thing3) (diagonal? thing3)))
		  (lambda (thing3)
		   (some (lambda (thing4) (square? thing4 thing3))
			 (lambda (thing4)
			  (forward-adjacent? thing1 thing2 thing4))))))))))))
    (cons 'forward-adjacent
	  (create-typed-meaning
	   *a-pp/for/np-pp/of/np*	;square player square
	   '(lambda (noun)
	     (lambda (np1)
	      (lambda (np2)
	       (lambda (thing1)
		(and (noun thing1 (-> thing boolean))
		     (np1 (lambda (thing2)
			   (np2 (lambda (thing3)
				 (forward-adjacent? thing1 thing2 thing3))
				(-> (-> thing boolean) boolean)))
			  (-> (-> thing boolean) boolean)))))))))
    (cons 'forward-adjacent
	  (create-typed-meaning
	   *a-pp/for/np-pp/of/np*	;square player square
	   '(lambda (noun)
	     (lambda (np1)
	      (lambda (np2)
	       (lambda (thing1)
		(and (noun thing1 (-> thing boolean))
		     (np2 (lambda (thing3)
			   (np1 (lambda (thing2)
				 (forward-adjacent? thing1 thing2 thing3))
				(-> (-> thing boolean) boolean)))
			  (-> (-> thing boolean) boolean)))))))))
    ;; lexicalization
    (cons
     'forward-diagonal
     (create-typed-meaning
      *a*				;square
      '(lambda (noun)
	(lambda (thing1)
	 (and
	  (noun thing1 (-> thing boolean))
	  (some (lambda (thing2) (player? thing2))
		(lambda (thing2)
		 (some
		  (lambda (thing3)
		   (or (row? thing3) (column? thing3) (diagonal? thing3)))
		  (lambda (thing3)
		   (some (lambda (thing4) (square? thing4 thing3))
			 (lambda (thing4)
			  (forward-diagonal? thing1 thing2 thing4))))))))))))
    (cons 'forward-diagonal
	  (create-typed-meaning
	   *a-pp/for/np-pp/of/np*	;square player square
	   '(lambda (noun)
	     (lambda (np1)
	      (lambda (np2)
	       (lambda (thing1)
		(and (noun thing1 (-> thing boolean))
		     (np1 (lambda (thing2)
			   (np2 (lambda (thing3)
				 (forward-diagonal? thing1 thing2 thing3))
				(-> (-> thing boolean) boolean)))
			  (-> (-> thing boolean) boolean)))))))))
    (cons 'forward-diagonal
	  (create-typed-meaning
	   *a-pp/for/np-pp/of/np*	;square player square
	   '(lambda (noun)
	     (lambda (np1)
	      (lambda (np2)
	       (lambda (thing1)
		(and (noun thing1 (-> thing boolean))
		     (np2 (lambda (thing3)
			   (np1 (lambda (thing2)
				 (forward-diagonal? thing1 thing2 thing3))
				(-> (-> thing boolean) boolean)))
			  (-> (-> thing boolean) boolean)))))))))
    (cons 'board
	  (create-typed-meaning
	   *a*				;square
	   '(lambda (noun)
	     (lambda (thing1)
	      (and
	       (noun thing1 (-> thing boolean))
	       (some (lambda (thing2)
		      (or (row? thing2) (column? thing2) (diagonal? thing2)))
		     (lambda (thing2) (square? thing1 thing2))))))))
    (cons 'cache
	  (create-typed-meaning
	   *a*				;square
	   '(lambda (noun)
	     (lambda (thing1)
	      (and
	       (noun thing1 (-> thing boolean))
	       (some (lambda (thing2) (player? thing2))
		     (lambda (thing2)
		      (some (lambda (thing3) (cache? thing3 thing2))
			    (lambda (thing3) (square? thing1 thing3))))))))))
    (cons 'cache
	  (create-typed-meaning
	   *a-pp/for/np*		;square player
	   '(lambda (noun)
	     (lambda (np)
	      (lambda (thing1)
	       (and (noun thing1 (-> thing boolean))
		    (np (lambda (thing2)
			 (some (lambda (thing3) (cache? thing3 thing2))
			       (lambda (thing3) (square? thing1 thing3))))
			(-> (-> thing boolean) boolean))))))))
    (cons 'empty
	  (create-typed-meaning
	   *a*				;line|square
	   '(lambda (noun)
	     (lambda (thing)
	      (and (noun thing (-> thing boolean)) (empty? thing))))))
    ;;
    ;; line
    (cons 'in (create-typed-meaning *p/in-np* '(lambda (np) np)))
    ;; player
    (cons 'for (create-typed-meaning *p/for-np* '(lambda (np) np)))
    ;; player|square
    (cons 'of (create-typed-meaning *p/of-np* '(lambda (np) np)))
    ;; square
    (cons 'from (create-typed-meaning *p/from-np* '(lambda (np) np)))
    ;; square
    (cons 'to (create-typed-meaning *p/to-np* '(lambda (np) np)))
    ;; needs work: should only allow moving
    (cons 'by (create-typed-meaning *p-vp* '(lambda (vp) vp)))
    ;; needs work: should only allow wins/1, draws/1, and has
    (cons 'when (create-typed-meaning *p-s* '(lambda (s) s)))
    ;;
    (and #f (cons 'wins (create-typed-meaning *v* 'needs-work)))
    (and #f (cons 'wins (create-typed-meaning *v-pp/when/s* 'needs-work)))
    (and #f (cons 'draws (create-typed-meaning *v-pp/when/s* 'needs-work)))
    (cons
     'has
     (create-typed-meaning *v-np*	;piece|move
			   '(lambda (np2)
			     (lambda (np1)
			      (np2 (lambda (thing2)
				    (np1 (lambda (thing1) (has? thing1 thing2))
					 (-> (-> thing boolean) boolean)))
				   (-> (-> thing boolean) boolean))))))
    (cons
     'has
     (create-typed-meaning *v-np*	;piece|move
			   '(lambda (np2)
			     (lambda (np1)
			      (np1 (lambda (thing1)
				    (np2 (lambda (thing2) (has? thing1 thing2))
					 (-> (-> thing boolean) boolean)))
				   (-> (-> thing boolean) boolean))))))
    (and #f (cons 'moves (create-typed-meaning *v-pp/by/vp* 'needs-work)))
    (and #f
	 (cons 'moving
	       (create-typed-meaning
		*v-np-pp/from/np-pp/to/np* ;piece square square
		'needs-work)))
    ;;
    (and #f (cons 'then (create-typed-meaning *coord-vp* 'needs-work)))
    (cons 'and
	  (create-typed-meaning *coord-s*
				'(lambda (s1) (lambda (s2) (and s1 s2))))))))

 (define (board-ref state board-square)
  (matrix-ref (state-board state)
	      (board-square-row board-square)
	      (board-square-column board-square)))

 (define (cache-ref state cache-square)
  (vector-ref ((case (cache-square-player cache-square)
		((x) state-cache-for-x)
		((o) state-cache-for-o)
		(else (fuck-up)))
	       state)
	      (cache-square-i cache-square)))

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

 (define (evaluate expression environment things state)
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
   ((and-expression? expression)
    (every (lambda (expression) (evaluate expression environment things state))
	   (and-expression-expressions expression)))
   ((or-expression? expression)
    (some (lambda (expression) (evaluate expression environment things state))
	  (or-expression-expressions expression)))
   ((a-expression? expression)
    (let ((value1 (evaluate (a-expression-expression1 expression)
			    environment
			    things
			    state))
	  (value2 (evaluate (a-expression-expression2 expression)
			    environment
			    things
			    state)))
     'needs-work))
   ((some-expression? expression)
    (let ((value1 (evaluate (some-expression-expression1 expression)
			    environment
			    things
			    state))
	  (value2 (evaluate (some-expression-expression2 expression)
			    environment
			    things
			    state)))
     (some
      (lambda (thing)
       (and (call value1 thing things state) (call value2 thing things state)))
      things)))
   ((every-expression? expression)
    (let ((value1 (evaluate (every-expression-expression1 expression)
			    environment
			    things
			    state))
	  (value2 (evaluate (every-expression-expression2 expression)
			    environment
			    things
			    state)))
     (every (lambda (thing)
	     (or (not (call value1 thing things state))
		 (call value2 thing things state)))
	    things)))
   ((that-expression? expression)
    (let* ((value1 (evaluate (that-expression-expression1 expression)
			     environment
			     things
			     state))
	   (value2 (evaluate (that-expression-expression2 expression)
			     environment
			     things
			     state))
	   (value3 (binding-value (a-member-of environment))))
     (unless (call value1 value3 things state) (fail))
     (call value2 value3 things state)))
   ((no-expression? expression)
    (let ((value1 (evaluate (no-expression-expression1 expression)
			    environment
			    things
			    state))
	  (value2 (evaluate (no-expression-expression2 expression)
			    environment
			    things
			    state)))
     (not (some (lambda (thing)
		 (and (call value1 thing things state)
		      (call value2 thing things state)))
		things))))
   ((the-expression? expression)
    (let ((value1 (evaluate (the-expression-expression1 expression)
			    environment
			    things
			    state))
	  (value2 (evaluate (the-expression-expression2 expression)
			    environment
			    things
			    state)))
     (if (one (lambda (thing) (call value1 thing things state)) things)
	 (call
	  value2
	  (find-if (lambda (thing) (call value1 thing things state)) things)
	  things
	  state)
	 (fail))))
   ((player?-expression? expression)
    (player? (evaluate (player?-expression-expression expression)
		       environment
		       things
		       state)))
   ((row?-expression? expression)
    (row? (evaluate (row?-expression-expression expression)
		    environment
		    things
		    state)))
   ((column?-expression? expression)
    (column? (evaluate (column?-expression-expression expression)
		       environment
		       things
		       state)))
   ((diagonal?-expression? expression)
    (diagonal? (evaluate (diagonal?-expression-expression expression)
			 environment
			 things
			 state)))
   ((move?-expression? expression)
    (move? (evaluate (move?-expression-expression expression)
		     environment
		     things
		     state)))
   ((opponent?-expression? expression)
    (let ((value1 (evaluate (opponent?-expression-expression1 expression)
			    environment
			    things
			    state))
	  (value2 (evaluate (opponent?-expression-expression2 expression)
			    environment
			    things
			    state)))
     (and (player? value1)
	  (player? value2)
	  (not (eq? (player-player value1) (player-player value2))))))
   ((cache?-expression? expression)
    (let ((value1 (evaluate (cache?-expression-expression1 expression)
			    environment
			    things
			    state))
	  (value2 (evaluate (cache?-expression-expression2 expression)
			    environment
			    things
			    state)))
     (and (cache? value1)
	  (player? value2)
	  (eq? (cache-player value1) (player-player value2)))))
   ((square?-expression? expression)
    (let ((value1 (evaluate (square?-expression-expression1 expression)
			    environment
			    things
			    state))
	  (value2 (evaluate (square?-expression-expression2 expression)
			    environment
			    things
			    state)))
     (or (and (board-square? value1)
	      (or (and (row? value2)
		       (= (board-square-row value1) (row-row value2)))
		  (and (column? value2)
		       (= (board-square-column value1) (column-column value2)))
		  (and (diagonal? value2)
		       (or (and (= (diagonal-slope value2) 1)
				(= (board-square-row value1)
				   (board-square-column value1)))
			   (and (= (diagonal-slope value2) -1)
				(= (board-square-row value1)
				   (- 2 (board-square-column value1))))))))
	 (and (cache-square? value1)
	      (cache? value2)
	      (eq? (cache-square-player value1) (cache-player value2))))))
   ((piece?-expression? expression)
    (let ((value1 (evaluate (piece?-expression-expression1 expression)
			    environment
			    things
			    state))
	  (value2 (evaluate (piece?-expression-expression2 expression)
			    environment
			    things
			    state)))
     (and (piece? value1)
	  (player? value2)
	  (eq? (piece-player value1) (player-player value2)))))
   ((distant?-expression? expression)
    (let ((value1 (evaluate (distant?-expression-expression1 expression)
			    environment
			    things
			    state))
	  (value2 (evaluate (distant?-expression-expression2 expression)
			    environment
			    things
			    state)))
     (and (row? value1)
	  (player? value2)
	  (or (and (eq? (player-player value2) 'x) (= (row-row value1) 2))
	      (and (eq? (player-player value2) 'o) (= (row-row value1) 0))))))
   ((close?-expression? expression)
    (let ((value1 (evaluate (close?-expression-expression1 expression)
			    environment
			    things
			    state))
	  (value2 (evaluate (close?-expression-expression2 expression)
			    environment
			    things
			    state)))
     (and (row? value1)
	  (player? value2)
	  (or (and (eq? (player-player value2) 'x) (= (row-row value1) 0))
	      (and (eq? (player-player value2) 'o) (= (row-row value1) 2))))))
   ((forward-adjacent?-expression? expression)
    (let ((value1
	   (evaluate (forward-adjacent?-expression-expression1 expression)
		     environment
		     things
		     state))
	  (value2
	   (evaluate (forward-adjacent?-expression-expression2 expression)
		     environment
		     things
		     state))
	  (value3
	   (evaluate (forward-adjacent?-expression-expression3 expression)
		     environment
		     things
		     state)))
     (and (board-square? value1)
	  (player? value2)
	  (board-square? value3)
	  (= (board-square-column value1) (board-square-column value3))
	  (= (board-square-row value1)
	     (+ (case (player-player value2)
		 ((x) 1)
		 ((o) -1)
		 (else (fuck-up)))
		(board-square-row value3))))))
   ((forward-diagonal?-expression? expression)
    (let ((value1
	   (evaluate (forward-diagonal?-expression-expression1 expression)
		     environment
		     things
		     state))
	  (value2
	   (evaluate (forward-diagonal?-expression-expression2 expression)
		     environment
		     things
		     state))
	  (value3
	   (evaluate (forward-diagonal?-expression-expression3 expression)
		     environment
		     things
		     state)))
     (and (board-square? value1)
	  (player? value2)
	  (board-square? value3)
	  (or (= (board-square-column value1)
		 (+ (board-square-column value3) 1))
	      (= (board-square-column value1)
		 (- (board-square-column value3) 1)))
	  (= (board-square-row value1)
	     (+ (case (player-player value2)
		 ((x) 1)
		 ((o) -1)
		 (else (fuck-up)))
		(board-square-row value3))))))
   ((empty?-expression? expression)
    (let ((value (evaluate (empty?-expression-expression expression)
			   environment
			   things
			   state)))
     ;; Could generalize to empty rows, columns, diagonals, cache
     ;; (for a player), and board.
     (or (and (board-square? value) (eq? (board-ref state value) #f))
	 (and (cache-square? value) (eq? (cache-ref state value) #f)))))
   ((has?-expression? expression)
    (let ((value1 (evaluate (has?-expression-expression1 expression)
			    environment
			    things
			    state))
	  (value2 (evaluate (has?-expression-expression2 expression)
			    environment
			    things
			    state)))
     ;; Could generalize to rows, columns, diagonals, cache (for a player), and
     ;; board.
     (or (and (board-square? value1)
	      (piece? value2)
	      (eq? (board-ref state value1) (piece-player value2)))
	 (and (cache-square? value1)
	      (piece? value2)
	      (eq? (cache-ref state value1) (piece-player value2)))
	 (and (player? value1)
	      (move? value2)
	      (eq? (player-player value1) (state-player state))))))
   ((application? expression)
    (call (evaluate (application-callee expression) environment things state)
	  (evaluate (application-argument expression) environment things state)
	  things
	  state))
   (else (fuck-up))))

 (define (call callee-value argument-value things state)
  (evaluate
   (lambda-expression-expression (closure-expression callee-value))
   (cons (make-binding
	  (lambda-expression-variable (closure-expression callee-value))
	  argument-value)
	 (closure-environment callee-value))
   things
   state))

 (define (a-type)
  (a-member-of
   (remove-duplicatesp
    equal-type?
    (domain
     (let loop ((type (typed-meaning-type (cdr (a-member-of *lexicon*)))))
      (amb type
	   ;; needs work: pp/{of,for,in,from,to}/np, pp/by/vp, and pp/when/s
	   (cond ((leftward-arrow-type? type)
		  (loop (leftward-arrow-type-result type)))
		 ((rightward-arrow-type? type)
		  (loop (rightward-arrow-type-result type)))
		 (else (fail)))))))))

 (define (a-lambda-expression-of-type type)
  (let loop ((expression (typed-meaning-meaning (cdr (a-member-of *lexicon*)))))
   (cond
    ((variable-access-expression? expression) (fail))
    ((lambda-expression? expression)
     (amb (begin (unless (equal-type? (lambda-expression-type expression)
				      type)
		  (fail))
		 expression)
	  (loop (lambda-expression-expression expression))))
    ((and-expression? expression)
     (loop (a-member-of (and-expression-expressions expression))))
    ((or-expression? expression)
     (loop (a-member-of (or-expression-expressions expression))))
    ((a-expression? expression)
     (loop ((amb a-expression-expression1 a-expression-expression2)
	    expression)))
    ((some-expression? expression)
     (loop ((amb some-expression-expression1 some-expression-expression2)
	    expression)))
    ((every-expression? expression)
     (loop ((amb every-expression-expression1 every-expression-expression2)
	    expression)))
    ((that-expression? expression)
     (loop ((amb that-expression-expression1 that-expression-expression2)
	    expression)))
    ((no-expression? expression)
     (loop ((amb no-expression-expression1 no-expression-expression2)
	    expression)))
    ((the-expression? expression)
     (loop ((amb the-expression-expression1 the-expression-expression2)
	    expression)))
    ((player?-expression? expression)
     (loop (player?-expression-expression expression)))
    ((row?-expression? expression)
     (loop (row?-expression-expression expression)))
    ((column?-expression? expression)
     (loop (column?-expression-expression expression)))
    ((diagonal?-expression? expression)
     (loop (diagonal?-expression-expression expression)))
    ((move?-expression? expression)
     (loop (move?-expression-expression expression)))
    ((opponent?-expression? expression)
     (loop ((amb opponent?-expression-expression1
		 opponent?-expression-expression2)
	    expression)))
    ((cache?-expression? expression)
     (loop ((amb cache?-expression-expression1 cache?-expression-expression2)
	    expression)))
    ((square?-expression? expression)
     (loop ((amb square?-expression-expression1 square?-expression-expression2)
	    expression)))
    ((piece?-expression? expression)
     (loop ((amb piece?-expression-expression1 piece?-expression-expression2)
	    expression)))
    ((distant?-expression? expression)
     (loop ((amb distant?-expression-expression1
		 distant?-expression-expression2)
	    expression)))
    ((close?-expression? expression)
     (loop ((amb close?-expression-expression1 close?-expression-expression2)
	    expression)))
    ((forward-adjacent?-expression? expression)
     (loop ((amb forward-adjacent?-expression-expression1
		 (amb forward-adjacent?-expression-expression2
		      forward-adjacent?-expression-expression3))
	    expression)))
    ((forward-diagonal?-expression? expression)
     (loop ((amb forward-diagonal?-expression-expression1
		 (amb forward-diagonal?-expression-expression2
		      forward-diagonal?-expression-expression3))
	    expression)))
    ((empty?-expression? expression)
     (loop (empty?-expression-expression expression)))
    ((has?-expression? expression)
     (loop ((amb has?-expression-expression1 has?-expression-expression2)
	    expression)))
    ((application? expression)
     (loop ((amb application-callee application-argument) expression)))
    (else (fuck-up)))))

 (define (a-value-of-type type things)
  (let loop ((type type) (expressions '()))
   (cond
    ((equal-type? type 'boolean) (a-boolean))
    ((equal-type? type 'thing) (a-member-of things))
    ((or (equal-type? type 'pp/of/np)
	 (equal-type? type 'pp/for/np)
	 (equal-type? type 'pp/in/np)
	 (equal-type? type 'pp/from/np)
	 (equal-type? type 'pp/to/np))
     (loop (parse-type *np*) expressions))
    ((equal-type? type 'pp/by/vp) (loop (parse-type *vp*) expressions))
    ((equal-type? type 'pp/when/s) (loop (parse-type *s*) expressions))
    ((or (leftward-arrow-type? type) (rightward-arrow-type? type))
     (let ((expression (a-lambda-expression-of-type type)))
      (make-closure
       (map (lambda (variable type)
	     (when (memq expression expressions) (fail))
	     (make-binding variable (loop type (cons expression expressions))))
	    (lambda-expression-variables expression)
	    (lambda-expression-types expression))
       expression)))
    (else (fuck-up)))))

 ;; Type-based generator

 (define (a-phrase-of-type type n)
  (when (zero? n) (fail))
  (amb
   (let ((lexical-entry (a-member-of *lexicon*)))
    (unless (equal-type? (typed-meaning-type (cdr lexical-entry)) type)
     (fail))
    (list (car lexical-entry)))
   (let ((callee-type (a-type)))
    (cond
     ;; needs work: pp/{of,for,in,from,to}/np, pp/by/vp, and pp/when/s
     ((leftward-arrow-type? callee-type)
      (unless (equal-type? (leftward-arrow-type-result callee-type) type)
       (fail))
      (let ((left (a-phrase-of-type
		   (leftward-arrow-type-argument callee-type) (- n 1))))
       (append left (a-phrase-of-type callee-type (- n (length left))))))
     ((rightward-arrow-type? callee-type)
      (unless (equal-type? (rightward-arrow-type-result callee-type) type)
       (fail))
      (let ((left (a-phrase-of-type callee-type (- n 1))))
       (append
	left
	(a-phrase-of-type
	 (rightward-arrow-type-argument callee-type) (- n (length left))))))
     (else (fail))))))

 ;; Value-based generator

 (define (a-phrase-of-value value type things state n)
  (when (zero? n) (fail))
  (amb
   (let ((lexical-entry (a-member-of *lexicon*)))
    (unless (and (equal-type? (typed-meaning-type (cdr lexical-entry)) type)
		 (equal-value?
		  (evaluate
		   (typed-meaning-meaning (cdr lexical-entry)) '() things state)
		  value))
     (fail))
    (list (car lexical-entry)))
   (let* ((callee-type (a-type))
	  (callee-value (a-value-of-type callee-type things)))
    (cond
     ;; needs work: pp/{of,for,in,from,to}/np, pp/by/vp, and pp/when/s
     ((leftward-arrow-type? callee-type)
      (unless (equal-type? (leftward-arrow-type-result callee-type) type)
       (fail))
      (let* ((argument-type (leftward-arrow-type-argument callee-type))
	     (argument-value (a-value-of-type argument-type things)))
       (unless (equal-value? (call callee-value argument-value things state)
			     value)
	(fail))
       (let ((left (a-phrase-of-value
		    argument-value argument-type things state (- n 1))))
	(append left
		(a-phrase-of-value
		 callee-value callee-type things state (- n (length left)))))))
     ((rightward-arrow-type? callee-type)
      (unless (equal-type? (rightward-arrow-type-result callee-type) type)
       (fail))
      (let* ((argument-type (rightward-arrow-type-argument callee-type))
	     (argument-value (a-value-of-type argument-type things)))
       (unless (equal-value? (call callee-value argument-value things state)
			     value)
	(fail))
       (let ((left (a-phrase-of-value
		    callee-value callee-type things state (- n 1))))
	(append
	 left
	 (a-phrase-of-value
	  argument-value argument-type things state (- n (length left)))))))
     (else (fail))))))

 ;; Type-based understander

 (define (a-bottom-up-parse type words)
  (let loop ((stack '()) (words words))
   (amb
    ;; shift
    (if (null? words)
	(if (and (not (null? stack))
		 (null? (rest stack))
		 (equal-type? (stack-entry-type (first stack)) type))
	    (stack-entry-parse (first stack))
	    (fail))
	(let ((lexical-entry (a-member-of *lexicon*)))
	 (unless (eq? (car lexical-entry) (first words)) (fail))
	 (loop (cons (make-stack-entry (typed-meaning-type (cdr lexical-entry))
				       (first words))
		     stack)
	       (rest words))))
    ;; reduce
    (amb
     (if (and (not (null? stack))
	      (not (null? (rest stack)))
	      (leftward-arrow-type? (stack-entry-type (first stack)))
	      (equal-type?
	       (leftward-arrow-type-argument (stack-entry-type (first stack)))
	       (stack-entry-type (second stack))))
	 (loop
	  (cons (make-stack-entry
		 (leftward-arrow-type-result (stack-entry-type (first stack)))
		 (list (stack-entry-parse (second stack))
		       (stack-entry-parse (first stack))))
		(rest (rest stack)))
	  words)
	 (fail))
     (if (and (not (null? stack))
	      (not (null? (rest stack)))
	      (rightward-arrow-type? (stack-entry-type (second stack)))
	      (equal-type?
	       (rightward-arrow-type-argument (stack-entry-type (second stack)))
	       (stack-entry-type (first stack))))
	 (loop
	  (cons (make-stack-entry
		 (rightward-arrow-type-result (stack-entry-type (second stack)))
		 (list (stack-entry-parse (second stack))
		       (stack-entry-parse (first stack))))
		(rest (rest stack)))
	  words)
	 (fail))))))

 (define (parse-length parse)
  (if (list? parse)
      (+ (parse-length (first parse)) (parse-length (second parse)))
      1))

 (define (a-top-down-parse type words)
  (let ((result
	 (let loop ((type type) (words words) (n (length words)))
	  (when (zero? n) (fail))
	  (amb
	   (let ((lexical-entry (a-member-of *lexicon*)))
	    (unless (and (not (null? words))
			 (eq? (car lexical-entry) (first words))
			 (equal-type? (typed-meaning-type (cdr lexical-entry))
				      type))
	     (fail))
	    (make-result (first words) (rest words)))
	   (let ((callee-type (a-type)))
	    (cond
	     ;; needs work: pp/{of,for,in,from,to}/np, pp/by/vp, and pp/when/s
	     ((leftward-arrow-type? callee-type)
	      (unless (equal-type? (leftward-arrow-type-result callee-type)
				   type)
	       (fail))
	      (let* ((result1 (loop (leftward-arrow-type-argument callee-type)
				    words
				    (- n 1)))
		     (result2
		      (loop callee-type
			    (result-words result1)
			    (- n (parse-length (result-parse result1))))))
	       (make-result (list (result-parse result1) (result-parse result2))
			    (result-words result2))))
	     ((rightward-arrow-type? callee-type)
	      (unless (equal-type? (rightward-arrow-type-result callee-type)
				   type)
	       (fail))
	      (let* ((result1 (loop callee-type words (- n 1)))
		     (result2
		      (loop (rightward-arrow-type-argument callee-type)
			    (result-words result1)
			    (- n (parse-length (result-parse result1))))))
	       (make-result (list (result-parse result1) (result-parse result2))
			    (result-words result2))))
	     (else (fail))))))))
   (unless (null? (result-words result)) (fail))
   (result-parse result)))

 ;; Value-based understander

 (define (things)
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
	  ;; debugging
	  (if #t (list (make-move)) '())))

 (define (a-typed-apply left right things state)
  ;; needs work: pp/{of,for,in,from,to}/np, pp/by/vp, and pp/when/s
  (amb (if (and (leftward-arrow-type? (typed-meaning-type right))
		(equal-type?
		 (typed-meaning-type left)
		 (leftward-arrow-type-argument (typed-meaning-type right))))
	   (make-typed-meaning
	    (leftward-arrow-type-result (typed-meaning-type right))
	    (call (typed-meaning-meaning right)
		  (typed-meaning-meaning left)
		  things
		  state))
	   (fail))
       (if (and (rightward-arrow-type? (typed-meaning-type left))
		(equal-type?
		 (typed-meaning-type right)
		 (rightward-arrow-type-argument (typed-meaning-type left))))
	   (make-typed-meaning
	    (rightward-arrow-type-result (typed-meaning-type left))
	    (call (typed-meaning-meaning left)
		  (typed-meaning-meaning right)
		  things
		  state))
	   (fail))))

 (define (possibly-true? words things state)
  (possibly?
   (domain
    (let ((typed-meaning
	   (let loop ((words words))
	    (if (= (length words) 1)
		(let ((lexical-entry (a-member-of *lexicon*)))
		 (unless (eq? (first words) (car lexical-entry)) (fail))
		 (make-typed-meaning
		  (typed-meaning-type (cdr lexical-entry))
		  (evaluate (typed-meaning-meaning (cdr lexical-entry))
			    '()
			    things
			    state)))
		(let ((i (+ (a-member-of (enumerate (- (length words) 1))) 1)))
		 (a-typed-apply (loop (sublist words 0 i))
				(loop (sublist words i (length words)))
				things
				state))))))
     (and (eq? (typed-meaning-type typed-meaning) 'boolean)
	  (typed-meaning-meaning typed-meaning))))))

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
