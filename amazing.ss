#!r6rs

(import (except (rnrs) + - * / sqrt exp log expt sin cos atan = < > <= >=
		zero? positive? negative? real? magnitude)
	(AD))

(define (diffUff f) (lambda (x) (lambda (g) (derivative-F ((f x) g)))))

(define (f x) (lambda (g) (lambda (y) (g (+ x y)))))

(define f-hat ((diffUff f) 3))

(define (should-be-7) (log ((f-hat (f-hat exp)) 1)))
