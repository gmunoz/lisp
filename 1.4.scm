#!r5rs

; From a guile repl: (load "1.4.scm")

; Define some functions needed not included in scheme
(define (atom? a)
  (cond ((number? a) #t)
		((symbol? a) #t)
		((string? a) #t)
		(else #f) ) )

(define wrong
  (lambda (msg . stuff)
	msg))

; 1.4
(define (evaluate e env)
  (if (atom? e)
	(cond ((symbol? e) (lookup e env))
		  ((or (number? e)(string? e)(char? e)(boolean? e)(vector? e))
		   e )
		  (else (wrong "Cannot evaluate" e)) )
	(case (car e)
	  ((quote)  (cadr e))
	  ((if)     (if (evaluate (cadr e) env)
				    (evaluate (caddr e) env)
					(evaluate (cadddr e) env) ))
	  ((begin)  (eprogn (cdr e) env))
	  ((set!)   (update! (cadr e) env (evaluate (caddr e) env)))
	  ((lambda) (make-function (cadr e) (cddr e) env))
	  (else     (invoke (evaluate (car e) env)
						(evlis (cdr e) env) )) ) ) )

; 1.4.3 Sequence
(define (eprogn exps env)
  (if (pair? exps)
	(if (pair? (cdr exps))
	  (begin (evaluate (car exps) env)
			 (eprogn (cdr exps) env) )
	  (evaluate (car exps) env) )
	;'() ) )
	empty-begin ) )

(define empty-begin 813)

(define (evlis exps env)
  (if (pair? exps)
	  (cons (evaluate (car exps) env)
			(evlis (cdr exps) env) )
	  '() ) )

; Implemented as an associative list (key value pair).
; If the first element of a key/value pair is the same
; as the id, the return the value, otherwise recurse on
; the rest of the list. If no longer a pair, return error
; no value found.
(define (lookup id env)
  (if (pair? env)
	(if (eq? (caar env) id)
	    (cdar env)
		(lookup id (cdr env)) )
	(wrong "No such binding" id) ) )

(define (update! id env value)
  (if (pair? env)
	  (if (eq? (caar env) id)
		  (begin (set-cdr! (car env) value)
				 value )
		  (update! id (cdr env) value) )
	  (wrong "No such binding" id) ) )

(define env.init '())

(define (extend env variables values)
  (cond ((pair? variables)
		 (if (pair? values)
		     (cons (cons (car variables) (car values))
				   (extend env (cdr variables) (cdr values)) )
			 (wrong "Too less values") ) )
		((null? variables)
		     (if (null? values)
			   env
			   (wrong "Too much values") ) )
		((symbol? variables) (cons (cons variables values) env)) ) )

(define (invoke fn args)
  (if (procedure? fn)
	  (fn args)
	  (wrong "Not a function" fn) ) )

(define (make-function variables body env)
  (lambda (values)
	(eprogn body (extend env variables values)) ) )

; 1.6.1 - Dynamic and Lexical Binding
(define (d.evaluate e env)
  (if (atom? e)
	(cond ((symbol? e) (lookup e env))
		  ((or (number? e)(string? e)(char? e)(boolean? e)(vector? e))
		   e )
		  (else (wrong "Cannot evaluate" e)) )
	(case (car e)
	  ((quote)  (cadr e))
	  ((if)     (if (d.evaluate (cadr e) env)
				    (d.evaluate (caddr e) env)
					(d.evaluate (cadddr e) env) ))
	  ((begin)  (eprogn (cdr e) env))
	  ((set!)   (update! (cadr e) env (d.evaluate (caddr e) env)))
	  ((function)   ; Syntax: (function (lambda variables body))
	   (let* ((f   (cadr e))
			  (fun (d.make-function (cadr f) (cddr f) env)) )
		 (d.make-closure fun env) ) )
	  ((lambda) (d.make-function (cadr e) (cddr e) env))
	  (else (d.invoke (d.evaluate (car e) env)
					  (evlis (cdr e) env)
					  env )) ) ) )

(define (d.invoke fn args env)
  (if (procedure? fn)
	  (fn args env)
	  (wrong "Not a function" fn) ) )

(define (d.make-function variables body def.env)
  (lambda (values current.env)
	(eprogn body (extend current.env variables values)) ) )

; 1.6.1
(define (d.make-closure fun env)
  (lambda (values current.env)
	(fun values env) ) )

; 1.6.2
; define some dummy methods to compile
(define (getprop var symbol)
  (wrong "getprop not implemented" var) )
(define (putprop var symbol val)
  (wrong "putprop not implemented" var) )

(define (s.make-function variables body env)
  (lambda (values current.env)
	(let ((old-bindings
		   (map (lambda (var val)
				      (let ((old-value (getprop var 'apval)))
						(putprop var 'apval val)
						(cons var old-value) ) )
				variables
				values ) ))
	  (let ((result (eprogn body current.env)))
		(for-each (lambda (b) (putprop (car b) 'apval (cdr b)))
				  old-bindings )
		result ) ) ) )

(define (s.lookup id env)
  (getprop id 'apval) )

(define (s.update! id env value)
  (putprop id 'apval value) )

; 1.7 - Global environment
(define env.global env.init)
(define-syntax definitial
  (syntax-rules ()
	((definitial name)
	 (begin (set! env.global (cons (cons 'name 'void) env.global))
			'name ) )
	((definitial name value)
	 (begin (set! env.global (cons (cons 'name value) env.global))
			'name ) ) ) )
(define-syntax defprimitive
  (syntax-rules ()
	((defprimitive name value arity)
	 (definitial name
		(lambda (values)
		  (if (= arity (length values))
			(apply value values)         ; The real apply of Scheme
			(wrong "Incorrect arity"
				   (list 'name values) ) ) ) ) ) ) )

(definitial t #t)
(definitial f #f)
(definitial nil '())

(definitial foo)
(definitial bar)
(definitial fib)
(definitial fact)

(defprimitive cons cons 2)
(defprimitive car car 1)
(defprimitive set-cdr! set-cdr! 2)
(defprimitive + + 2)
(defprimitive eq? eq? 2)
(defprimitive < < 2)

; 1.8
(define (chapter1-scheme)
  (define (toplevel)
	(display (evaluate (read) env.global))
	(toplevel) )
  (toplevel) )
