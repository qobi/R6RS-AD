#!r6rs

(import (except (rnrs) + - * / sqrt exp log expt sin cos atan = < > <= >=
		zero? positive? negative? real? magnitude)
	(QobiScheme)
	(AD))

(define (hessian-vector-product f)
 ;; f:vector(real)->real, x:vector(real), u:vector(real)
 ;; (hessian-vector-product f):x*u->(\nabla^2 f(x))*u
 (directional-derivative-vector-F (gradient-vector-R f)))

(define (identity-matrix n)
 (map-n-vector (lambda (i) (map-n-vector (lambda (j) (if (= i j) 1 0)) n)) n))

(define (hessian f)
 (lambda (x)
  (map-vector (lambda (u) ((hessian-vector-product f) x u))
	      (identity-matrix (vector-length x)))))

(define (f u) (let ((x (vector-ref u 0)) (y (vector-ref u 1))) (* 3 x x x y y)))

(define (example) ((hessian f) '#(3 4)))

(define (Hf u)
 (let ((x (vector-ref u 0)) (y (vector-ref u 1)))
  (vector (vector (* 3 3 2 x y y)
		  (* 3 3 2 x x y))
	  (vector (* 3 3 2 x x y)
		  (* 3 2 x x x)))))

(define (check) (Hf '#(3 4)))
