#!r6rs

(library
 (generative-montague-grammar)
 (export parse-type pretty-type parse-expression pretty-expression pretty-value
	 pretty-environment type free-variables equal-type? equal-value?
	 create-typed-meaning *lexicon* evaluate call a-type
	 a-lambda-expression-of-type a-value-of-type a-vacuous-value-of-type
	 a-phrase-of-type
	 a-phrase-of-value a-bottom-up-parse parse-length a-top-down-parse
	 things a-typed-apply possibly-true?)
 (import (rnrs) (QobiScheme) (nondeterministic-scheme))

 (define-record-type typed-meaning (fields type meaning))

 (define-record-type stack-entry (fields type parse))

 (define-record-type result (fields parse words))

 (define-record-type position (fields position))

 (define-record-type position-state (fields position state))

 (define-record-type leftward-arrow-type (fields result argument))

 (define-record-type rightward-arrow-type (fields argument result))

 (define-record-type variable-access-expression (fields variable type))

 (define-record-type lambda-expression
  (fields variable expression variables types type))

 (define-record-type application (fields callee argument type))

 (define-record-type and-expression (fields expressions))

 (define-record-type one-expression (fields expression))

 (define-record-type find-if-expression (fields expression))

 (define-record-type position?-expression (fields expression))

 (define-record-type position-center?-expression (fields expression))

 (define-record-type position-state?-expression (fields expression))

 (define-record-type position-state-x?-expression (fields expression))

 (define-record-type same-position?-expression (fields expression1 expression2))

 (define-record-type binding (fields variable value))

 (define-record-type closure (fields environment expression))

 (define (parse-type type)
  (cond ((eq? type 'boolean) 'boolean)
	((eq? type 'thing) 'thing)
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
	  (= (length expression) 2)
	  (eq? (first expression) 'one))
     (unless (equal-type? type 'boolean)
      (error #f "one expression not of type boolean"))
     (make-one-expression
      (loop (second expression)
	    (make-rightward-arrow-type 'thing 'boolean)
	    variables
	    types)))
    ((and (list? expression)
	  (= (length expression) 2)
	  (eq? (first expression) 'find-if))
     (unless (equal-type? type 'thing)
      (error #f "find-if expression not of type thing"))
     (make-find-if-expression
      (loop (second expression)
	    (make-rightward-arrow-type 'thing 'boolean)
	    variables
	    types)))
    ((and (list? expression)
	  (= (length expression) 2)
	  (eq? (first expression) 'position?))
     (unless (equal-type? type 'boolean)
      (error #f "position? expression not of type boolean"))
     (make-position?-expression
      (loop (second expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 2)
	  (eq? (first expression) 'position-center?))
     (unless (equal-type? type 'boolean)
      (error #f "position-center? expression not of type boolean"))
     (make-position-center?-expression
      (loop (second expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 2)
	  (eq? (first expression) 'position-state?))
     (unless (equal-type? type 'boolean)
      (error #f "position-state? expression not of type boolean"))
     (make-position-state?-expression
      (loop (second expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 2)
	  (eq? (first expression) 'position-state-x?))
     (unless (equal-type? type 'boolean)
      (error #f "position-state-x? expression not of type boolean"))
     (make-position-state-x?-expression
      (loop (second expression) 'thing variables types)))
    ((and (list? expression)
	  (= (length expression) 3)
	  (eq? (first expression) 'same-position?))
     (unless (equal-type? type 'boolean)
      (error #f "same-position? expression not of type boolean"))
     (make-same-position?-expression
      (loop (second expression) 'thing variables types)
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
   ((one-expression? expression)
    `(one ,(pretty-expression (one-expression-expression expression))))
   ((find-if-expression? expression)
    `(find-if ,(pretty-expression (find-if-expression-expression expression))))
   ((position?-expression? expression)
    `(position?
      ,(pretty-expression (position?-expression-expression expression))))
   ((position-center?-expression? expression)
    `(position-center?
      ,(pretty-expression (position-center?-expression-expression expression))))
   ((position-state?-expression? expression)
    `(position-state?
      ,(pretty-expression (position-state?-expression-expression expression))))
   ((position-state-x?-expression? expression)
    `(position-state-x?
      ,(pretty-expression
	(position-state-x?-expression-expression expression))))
   ((same-position?-expression? expression)
    `(same-position?
      ,(pretty-expression (same-position?-expression-expression1 expression))
      ,(pretty-expression (same-position?-expression-expression2 expression))))
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
	((one-expression? expression) 'boolean)
	((find-if-expression? expression) 'thing)
	((position?-expression? expression) 'boolean)
	((position-center?-expression? expression) 'boolean)
	((position-state?-expression? expression) 'boolean)
	((position-state-x?-expression? expression) 'boolean)
	((same-position?-expression? expression) 'boolean)
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
   ((one-expression? expression)
    (free-variables (one-expression-expression expression)))
   ((find-if-expression? expression)
    (free-variables (find-if-expression-expression expression)))
   ((position?-expression? expression)
    (free-variables (position?-expression-expression expression)))
   ((position-center?-expression? expression)
    (free-variables (position-center?-expression-expression expression)))
   ((position-state?-expression? expression)
    (free-variables (position-state?-expression-expression expression)))
   ((position-state-x?-expression? expression)
    (free-variables (position-state-x?-expression-expression expression)))
   ((same-position?-expression? expression)
    (unionq
     (free-variables (same-position?-expression-expression1 expression))
     (free-variables (same-position?-expression-expression2 expression))))
   ((application? expression)
    (unionq (free-variables (application-callee expression))
	    (free-variables (application-argument expression))))
   (else (fuck-up))))

 (define (equal-type? type1 type2)
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
      (and (position? value1)
	   (position? value2)
	   (= (position-position value1) (position-position value2)))
      (and (position-state? value1)
	   (position-state? value2)
	   (= (position-state-position value1) (position-state-position value2))
	   (eq? (position-state-state value1) (position-state-state value2)))
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

 (define *lexicon*
  (list
   (cons 'the
	 (create-typed-meaning
	  '(-> (-> thing boolean) (-> (-> thing boolean) boolean))
	  '(lambda (noun1)
	    (lambda (noun2)
	     ;; Montague semantics of "the" is wrong
	     (and (one noun1) (noun2 (find-if noun1) (-> thing boolean)))))))
   (cons
    'x
    (create-typed-meaning
     '(-> thing boolean)
     '(lambda (thing) (and (position-state? thing) (position-state-x? thing)))))
   (cons 'is-on
	 (create-typed-meaning
	  '(-> (-> (-> thing boolean) boolean)
	       (<- boolean (-> (-> thing boolean) boolean)))
	  '(lambda (np2)
	    (lambda (np1)
	     (np2 (lambda (thing2)
		   (np1 (lambda (thing1)
			 (and (position-state? thing1)
			      (position? thing2)
			      (same-position? thing1 thing2)))
			(-> (-> thing boolean) boolean)))
		  (-> (-> thing boolean) boolean))))))
   (cons
    'center
    (create-typed-meaning
     '(-> thing boolean)
     '(lambda (thing) (and (position? thing) (position-center? thing)))))))

 (define (evaluate expression environment things)
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
    (every (lambda (expression) (evaluate expression environment things))
	   (and-expression-expressions expression)))
   ((one-expression? expression)
    (let ((v (evaluate
	      (one-expression-expression expression) environment things)))
     (one (lambda (thing) (call v thing things)) things)))
   ((find-if-expression? expression)
    (let ((v (evaluate
	      (find-if-expression-expression expression) environment things)))
     (find-if (lambda (thing) (call v thing things)) things)))
   ((position?-expression? expression)
    (position?
     (evaluate
      (position?-expression-expression expression) environment things)))
   ((position-center?-expression? expression)
    (= (position-position
	(evaluate (position-center?-expression-expression expression)
		  environment
		  things))
       4))
   ((position-state?-expression? expression)
    (position-state?
     (evaluate
      (position-state?-expression-expression expression) environment things)))
   ((position-state-x?-expression? expression)
    (eq? (position-state-state
	  (evaluate (position-state-x?-expression-expression expression)
		    environment
		    things))
	 'x))
   ((same-position?-expression? expression)
    (= (position-state-position
	(evaluate (same-position?-expression-expression1 expression)
		  environment
		  things))
       (position-position
	(evaluate (same-position?-expression-expression2 expression)
		  environment
		  things))))
   ((application? expression)
    (call (evaluate (application-callee expression) environment things)
	  (evaluate (application-argument expression) environment things)
	  things))
   (else (fuck-up))))

 (define (call callee-value argument-value things)
  (evaluate
   (lambda-expression-expression (closure-expression callee-value))
   (cons (make-binding
	  (lambda-expression-variable (closure-expression callee-value))
	  argument-value)
	 (closure-environment callee-value))
   things))

 (define (a-type)
  (a-member-of
   (remove-duplicatesp
    equal-type?
    (domain
     (let loop ((type (typed-meaning-type (cdr (a-member-of *lexicon*)))))
      (amb type
	   (cond ((leftward-arrow-type? type)
		  (loop (leftward-arrow-type-result type)))
		 ((rightward-arrow-type? type)
		  (loop (rightward-arrow-type-result type)))
		 (else (fail)))))))))

 (define (a-lambda-expression-of-type type)
  (let loop ((expression (typed-meaning-meaning (cdr (a-member-of *lexicon*)))))
   (cond ((variable-access-expression? expression) (fail))
	 ((lambda-expression? expression)
	  (amb
	   (begin (unless (equal-type? (lambda-expression-type expression)
				       type)
		   (fail))
		  expression)
	   (loop (lambda-expression-expression expression))))
	 ((and-expression? expression)
	  (loop (a-member-of (and-expression-expressions expression))))
	 ((one-expression? expression)
	  (loop (one-expression-expression expression)))
	 ((find-if-expression? expression)
	  (loop (find-if-expression-expression expression)))
	 ((position?-expression? expression)
	  (loop (position?-expression-expression expression)))
	 ((position-center?-expression? expression)
	  (loop (position-center?-expression-expression expression)))
	 ((position-state?-expression? expression)
	  (loop (position-state?-expression-expression expression)))
	 ((position-state-x?-expression? expression)
	  (loop (position-state-x?-expression-expression expression)))
	 ((same-position?-expression? expression)
	  (loop ((amb same-position?-expression-expression1
		      same-position?-expression-expression2)
		 expression)))
	 ((application? expression)
	  (loop ((amb application-callee application-argument) expression)))
	 (else (fuck-up)))))

 (define (a-value-of-type type things)
  (let loop ((type type) (expressions '()))
   (cond
    ((equal-type? type 'boolean) (a-boolean))
    ((equal-type? type 'thing) (a-member-of things))
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

 (define (a-vacuous-value-of-type type)
  (let loop ((type type) (expressions '()))
   (cond
    ((equal-type? type 'boolean) (fail))
    ((equal-type? type 'thing) (fail))
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

 (define (a-phrase-of-type type)
  (amb
   (let ((lexical-entry (a-member-of *lexicon*)))
    (unless (equal-type? (typed-meaning-type (cdr lexical-entry)) type)
     (fail))
    (list (car lexical-entry)))
   (let ((callee-type (a-type)))
    (cond
     ((leftward-arrow-type? callee-type)
      (unless (equal-type? (leftward-arrow-type-result callee-type) type)
       (fail))
      (append (a-phrase-of-type (leftward-arrow-type-argument callee-type))
	      (a-phrase-of-type callee-type)))
     ((rightward-arrow-type? callee-type)
      (unless (equal-type? (rightward-arrow-type-result callee-type) type)
       (fail))
      (append (a-phrase-of-type callee-type)
	      (a-phrase-of-type (rightward-arrow-type-argument callee-type))))
     (else (fail))))))

 ;; Value-based generator

 (define (a-phrase-of-value value type things)
  (amb
   (let ((lexical-entry (a-member-of *lexicon*)))
    (unless (and (equal-type? (typed-meaning-type (cdr lexical-entry)) type)
		 (equal-value?
		  (evaluate
		   (typed-meaning-meaning (cdr lexical-entry)) '() things)
		  value))
     (fail))
    (list (car lexical-entry)))
   (let* ((callee-type (a-type))
	  (callee-value (a-vacuous-value-of-type callee-type)))
    (cond
     ((leftward-arrow-type? callee-type)
      (unless (equal-type? (leftward-arrow-type-result callee-type) type)
       (fail))
      (let* ((argument-type (leftward-arrow-type-argument callee-type))
	     (argument-value (a-vacuous-value-of-type argument-type)))
       (unless (equal-value? (call callee-value argument-value things) value)
	(fail))
       (append (a-phrase-of-value argument-value argument-type things)
	       (a-phrase-of-value callee-value callee-type things))))
     ((rightward-arrow-type? callee-type)
      (unless (equal-type? (rightward-arrow-type-result callee-type) type)
       (fail))
      (let* ((argument-type (rightward-arrow-type-argument callee-type))
	     (argument-value (a-vacuous-value-of-type argument-type)))
       (unless (equal-value? (call callee-value argument-value things) value)
	(fail))
       (append (a-phrase-of-value callee-value callee-type things)
	       (a-phrase-of-value argument-value argument-type things))))
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

 (define (things game-state)
  (append (map-n make-position 9)
	  (map-n (lambda (position)
		  (make-position-state position (list-ref game-state position)))
		 9)))

 (define (a-typed-apply left right things)
  (amb (if (and (leftward-arrow-type? (typed-meaning-type right))
		(equal-type?
		 (typed-meaning-type left)
		 (leftward-arrow-type-argument (typed-meaning-type right))))
	   (make-typed-meaning
	    (leftward-arrow-type-result (typed-meaning-type right))
	    (call
	     (typed-meaning-meaning right) (typed-meaning-meaning left) things))
	   (fail))
       (if (and (rightward-arrow-type? (typed-meaning-type left))
		(equal-type?
		 (typed-meaning-type right)
		 (rightward-arrow-type-argument (typed-meaning-type left))))
	   (make-typed-meaning
	    (rightward-arrow-type-result (typed-meaning-type left))
	    (call
	     (typed-meaning-meaning left) (typed-meaning-meaning right) things))
	   (fail))))

 (define (possibly-true? words things)
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
			    things)))
		(let ((i (+ (a-member-of (enumerate (- (length words) 1))) 1)))
		 (a-typed-apply (loop (sublist words 0 i))
				(loop (sublist words i (length words)))
				things))))))
     (and (eq? (typed-meaning-type typed-meaning) 'boolean)
	  (typed-meaning-meaning typed-meaning)))))))
