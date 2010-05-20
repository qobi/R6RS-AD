;;; scc -o gui -O2 gui.sc ~/lib/i686-Linux-2.6.26-2-686/QobiScheme.a ~/lib/i686-Linux-2.6.26-2-686/scxl.a -L /usr/X11R6/lib -lX11;rm gui.c;mv gui ~/bin/i686-Linux-2.6.26-2-686/.

(module gui (with qobischeme xlib) (main main))

(include "QobiScheme.sch")

(set! *program* "gui")
(set! *panic?* #t)

(define-structure grid-point x y z)

(define-structure grid-point-contents notches notch)

(define *grid* #f)

(define *theta* 0)

(define *center* #f)

(define *observer* '#(0 -40 100))

(define *focal-length* 300)

;;; horizontal distance between notches
(define *l1* 20)

;;; log radius
(define *l2* 2)

;;; overhang
(define *l3* 5)

(define *i* 0)

(define (grid-xy? grid-point) (even? (grid-point-y grid-point)))

(define (grid-zy? grid-point) (odd? (grid-point-y grid-point)))

(define (log->line-segment grid-point grid-point-contents)
 (cond
  ((grid-xy? grid-point)
   (make-line-segment
    (vector (- (* *l1* (grid-point-x grid-point)) *l3*)
	    (* *l2* (grid-point-y grid-point))
	    (* *l1* (grid-point-z grid-point)))
    (vector (+ (* *l1*
		  (+ (grid-point-x grid-point)
		     (- (grid-point-contents-notches grid-point-contents) 1)))
	       *l3*)
	    (* *l2* (grid-point-y grid-point))
	    (* *l1* (grid-point-z grid-point)))))
  ((grid-zy? grid-point)
   (make-line-segment
    (vector (* *l1* (grid-point-x grid-point))
	    (* *l2* (grid-point-y grid-point))
	    (- (* *l1* (grid-point-z grid-point)) *l3*))
    (vector (* *l1* (grid-point-x grid-point))
	    (* *l2* (grid-point-y grid-point))
	    (+ (* *l1*
		  (+ (grid-point-z grid-point)
		     (- (grid-point-contents-notches grid-point-contents) 1)))
	       *l3*))))
  (else (fuck-up))))

(define (line-segments)
 (removeq
  #f
  (map (lambda (grid-element)
	(let ((grid-point (first grid-element))
	      (grid-point-contents (second grid-element)))
	 (if (and grid-point-contents
		  ;; If the grid is malformed, i.e. if it does not meet the
		  ;; occupancy constraints, it might display incorrectly.
		  (zero? (grid-point-contents-notch grid-point-contents)))
	     (log->line-segment grid-point grid-point-contents)
	     #f)))
       *grid*)))

(define (read-grid pathname)
 (map (lambda (string)
       (list (make-grid-point (string->number (field-ref string 0))
			      (string->number (field-ref string 1))
			      (string->number (field-ref string 2)))
	     (if (zero? (string->number (field-ref string 3)))
		 #f
		 (make-grid-point-contents
		  (string->number (field-ref string 3))
		  (string->number (field-ref string 4))))))
      (read-file (default-extension pathname "logs"))))

(define (object-center)
 (let ((line-segments (line-segments)))
  (if (null? line-segments)
      '#(0 0 0)
      (let ((v (k*v (/ (length line-segments))
		    (reduce
		     v+
		     (map (lambda (l)
			   (k*v 0.5 (v+ (line-segment-p l) (line-segment-q l))))
			  line-segments)
		     '#(0 0 0)))))
       (vector (x v) 0 (z v))))))

(define (point-3d->2d p)
 (let ((theta (degrees->radians *theta*)))
  (project (v+ (m*v (vector (vector (cos theta) 0 (sin theta))
			    (vector 0 1 0)
			    (vector (- (sin theta)) 0 (cos theta)))
		    (v- p *center*))
	       *observer*)
	   *focal-length*)))

(define (line-segment-3d->2d l)
 (make-line-segment (point-3d->2d (line-segment-p l))
		    (point-3d->2d (line-segment-q l))))

(define-application viewer 640 480 #f 1 6
 (lambda ()
  (define-button 0 0 "Help" #f help-command)
  (define-button 5 0 "Quit" #f quit)
  (define-button 1 0 "+Theta" #f
   (lambda () (set! *theta* (+ *theta* 10)) (redraw-display-pane)))
  (define-button 2 0 "-Theta" #f
   (lambda () (set! *theta* (- *theta* 10)) (redraw-display-pane)))
  (define-button 3 0 "Next" #f
   (lambda ()
    (unless (can-open-file-for-input? (format #f "solution-~s.logs" (+ *i* 1)))
     (abort))
    (set! *i* (+ *i* 1))
    (set! *grid* (read-grid (format #f "solution-~s.logs" *i*)))
    (set! *center* (object-center))
    (redraw-display-pane)))
  (define-button 4 0 "Previous" #f
   (lambda ()
    (when (zero? *i*) (abort))
    (set! *i* (- *i* 1))
    (set! *grid* (read-grid (format #f "solution-~s.logs" *i*)))
    (set! *center* (object-center))
    (redraw-display-pane)))
  (define-key (list (control #\x) (control #\c)) "Quit" quit)
  (define-key (control #\h) "Help" help-command))
 (lambda () #f)
 (lambda () #f)
 (lambda ()
  (for-each (lambda (l)
	     (let ((l (line-segment-3d->2d l)))
	      (xdrawline *display* *display-pane* *thin-gc*
			 (+ 320 (x (line-segment-p l)))
			 (- 240 (y (line-segment-p l)))
			 (+ 320 (x (line-segment-q l)))
			 (- 240 (y (line-segment-q l))))))
	    (line-segments))
  (xdrawstring
   *display* *display-pane* *roman-gc* 5 (- *display-pane-height* 5)
   (number->string *i*) (string-length (number->string *i*)))))

(define (view)
 (set! *i* 0)
 (set! *grid* (read-grid (format #f "solution-~s.logs" *i*)))
 (set! *center* (object-center))
 (viewer '()))

(define-command (main) (view))
