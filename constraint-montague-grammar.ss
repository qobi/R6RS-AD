#!r6rs

(library
 (constraint-montague-grammar)
 (export generate understand)
 (import (rnrs)
	 (QobiScheme)
	 (nondeterministic-scheme)
	 (nondeterministic-constraints)
	 (nondeterministic-lifting))

 (define-record-type type (fields kind argument result))

 (define-record-type value (fields kind values))

 (define-record-type typed-meaning (fields type meaning))

 (define-record-type position (fields position))

 (define-record-type position-state (fields position state))

 (define-record-type variable-access-expression (fields variable type))

 (define-record-type lambda-expression
  (fields variable expression variables types type))

 (define-record-type llambda-expression
  (fields variable expression variables types type))

 (define-record-type rlambda-expression
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
   ((llambda-expression? expression)
    `(lambda (,(llambda-expression-variable expression))
      ,(pretty-expression (llambda-expression-expression expression))))
   ((rlambda-expression? expression)
    `(lambda (,(rlambda-expression-variable expression))
      ,(pretty-expression (rlambda-expression-expression expression))))
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

 (define (expression? expression)
  (or (variable-access-expression? expression)
      (lambda-expression? expression)
      (llambda-expression? expression)
      (rlambda-expression? expression)
      (and-expression? expression)
      (one-expression? expression)
      (find-if-expression? expression)
      (position?-expression? expression)
      (position-center?-expression? expression)
      (position-state?-expression? expression)
      (position-state-x?-expression? expression)
      (same-position?-expression? expression)
      (application? expression)))

 (define (type expression)
  (cond ((variable-access-expression? expression)
	 (variable-access-expression-type expression))
	((lambda-expression? expression) (lambda-expression-type expression))
	((llambda-expression? expression) (llambda-expression-type expression))
	((rlambda-expression? expression) (rlambda-expression-type expression))
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
   ((llambda-expression? expression) (llambda-expression-variables expression))
   ((rlambda-expression? expression) (rlambda-expression-variables expression))
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
	      (implies (memq parent-kind '(internal leftward rightward))
		       (used? child-kind))))
	kind-variable
	(type-kind result))
       (assert-nondeterministic-constraint!
	(lambda (parent-kind child-kind)
	 (and (implies (memq parent-kind '(unused boolean thing))
		       (unused? child-kind))
	      (implies (memq parent-kind '(internal leftward rightward))
		       (used? child-kind))))
	kind-variable
	(type-kind argument))
       (make-type kind-variable result argument))))

 (define (internal-arrow-type?-constraint type)
  (memq-constraint (type-kind type) '(internal)))

 (define (leftward-arrow-type?-constraint type)
  (memq-constraint (type-kind type) '(leftward)))

 (define (rightward-arrow-type?-constraint type)
  (memq-constraint (type-kind type) '(rightward)))

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
	((and (list? type) (= (length type) 3) (eq? (first type) '->))
	 (make-type (new-domain-variable '(internal))
		    (parse-type (third type))
		    (parse-type (second type))))
	((and (list? type) (= (length type) 3) (eq? (first type) '<=))
	 (make-type (new-domain-variable '(leftward))
		    (parse-type (third type))
		    (parse-type (second type))))
	((and (list? type) (= (length type) 3) (eq? (first type) '=>))
	 (make-type (new-domain-variable '(rightward))
		    (parse-type (second type))
		    (parse-type (third type))))
	(else (error #f "Bad type"))))

 (define (scalar-value?-constraint value)
  (let ((boolean-variable (create-boolean-variable)))
   (assert-nondeterministic-constraint!
    (lambda (boolean kind) (eq? boolean (not (expression? kind))))
    boolean-variable
    (value-kind value))
   boolean-variable))

 (define (create-value n m things expressions)
  (if (zero? n)
      (make-value (new-domain-variable (append '(unused #t #f) things))
		  (map-n (lambda (i) #f) m))
      (let ((values
	     (map-n (lambda (i) (create-value (- n 1) m things expressions)) m))
	    (kind-variable (append '(unused #t #f) things expressions)))
       (for-each (lambda (value)
		  (assert-nondeterministic-constraint!
		   (lambda (parent-kind child-kind)
		    (eq? (expression? parent-kind) (used? child-kind)))
		   kind-variable
		   (value-kind values)))
		 values)
       (make-value kind-variable values))))

 (define (equal-value-kind? kind1 kind2)
  ;; needs work
  (or (equal? kind1 kind2)
      (and (thing? kind1) (thing? kind2) (thing=? thing1 thing2))))

 (define (equal-value-kind?-constraint kind-variable1 kind-variable2)
  (let ((boolean-variable (create-boolean-variable)))
   (assert-nondeterministic-constraint!
    (lambda (boolean kind1 kind2) (eq? boolean (equal-value-kind? kind1 kind2)))
    boolean-variable
    kind-variable1
    kind-variable2)
   boolean-variable))

 (define (equal-value?-constraint value1 value2)
  (if (and value1 value2)
      (and-constraint
       (equal-value-kind?-constraint (value-kind value1) (value-kind value2))
       (or-constraint
	(scalar-value?-constraint value1)
	(every-constraint
	 equal-value?-constraint (value-values value1) (value-values value2))))
      (false-domain-variable)))

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

 (define (typed-apply-constraint parent left right grid)
  (or-constraint
   (and-constraint
    (leftward-arrow-type?-constraint (typed-meaning-type right))
    (equal-type?-constraint (typed-meaning-type left)
			    (type-argument (typed-meaning-type right)))
    (equal-type?-constraint (typed-meaning-type parent)
			    (type-result (typed-meaning-type right)))
    (call-constraint (typed-meaning-meaning parent)
		     (typed-meaning-meaning right)
		     (typed-meaning-meaning left)
		     grid))
   (and-constraint
    (rightward-arrow-type?-constraint (typed-meaning-type left))
    (equal-type?-constraint (typed-meaning-type right)
			    (type-argument (typed-meaning-type left)))
    (equal-type?-constraint (typed-meaning-type parent)
			    (type-result (typed-meaning-type left)))
    (call-constraint (typed-meaning-meaning parent)
		     (typed-meaning-meaning left)
		     (typed-meaning-meaning right)
		     grid))))

 (define (a-meaning-constraint words grid)
  ;; needs work: here I am
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
   (typed-meaning-meaning typed-meaning))))
