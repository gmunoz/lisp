(define (f.evaluate e env fenv)
  (if (atom? e)
	(cond ((symbol? e) (lookup e env))
		  ((or (number? e)(string? e)(char? e)(boolean? e)(vector? e))
		   e)
		  (else (wrong "Cannot evaluate" e)) )
	(case (car e)
	  ((quote)  (cadr e))
	  ((if)     (if (f.evaluate (cadr e) env fenv)
				    (f.evaluate (caddr e) env fenv)
					(f.evaluate (cadddr e) env fenv) ))
	  ((begin)  (f.eprogn (cdr e) env fenv))
	  ((set!)   (update! (cadr e)
						 env
						 (f.evaluate (caddr e) env fenv) ))
	  ((lambda) (f.make-function (cadr e) (cddr e) env fenv))
	  ((function)
	   (cond ((symbol? (cadr e))
			  (lookup (cadr e) fenv) )
			 (else (wrong "Incorrect function" (cadr e))) ) )
	  ((flet)
	   (f.eprogn
		 (cddr e)
		 env
		 (extend fenv
				 (map car (cadr e) )
				 (map (lambda (def)
						(f.make-function (cadr def) (cddr def) env fenv) )
					  (cadr e) ) ) ))
	  (else     (evaluate-application (car e)
									  (f.evlis (cdr e) env fenv)
									  env
									  fenv )) ) ) )

(define (f.evlis exps env fenv)
  (if (pair? exps)
	  (cons (f.evaluate (car exps) env fenv)
			(f.evlis (cdr exps) env fenv) )
	  '() ) )

(define (f.eprogn exps env fenv)
  (if (pair? exps)
	  (if (pair? (cdr exps))
		  (begin (f.evaluate (car exps) env fenv)
				 (f.eprogn (cdr exps) env fenv) )
		  (f.evaluate (car exps) env fenv) )
	  empty-begin ) )

(define (f.make-function variables body env fenv)
  (lambda (values)
	(f.eprogn body (extend env variables values) fenv) ) )

(define (evaluate-application fn args env fenv)
  (cond ((symbol? fn) ((lookup fn fenv) args))
		 (invoke (lookup fn fenv) args) )
		((and (pair? fn) (eq? (car fn) 'lambda))
		 (f.eprogn (cddr fn)
				   (extend env (cadr fn) args)
				   fenv ) )
		(else (wrong "Incorrect functional term" fn)) )

(define (evaluate-application2 fn args env fenv)
  (cond ((symbol? fn)
		 ((lookup fn fenv) args) )
		((and (pair? fn) (eq? (car fn) 'lambda))
		 (f.eprogn (cddr fn)
				   (extend env (cadr fn) args)
				   fenv ) )
		(else (evaluate-application2                 ; ** Modified **
			   (f.evaluate fn env fenv) args env fenv )) ) )

(define (evaluate-application3 fn args env fenv)
  (cond
	((symbol? fn)
	 (let ((fun (lookup fn fenv)))
	   (if fun (fun args)
		 (evaluate-application3 (lookup fn env) args env fenv)) ) )
	((and (pair? fn) (eq? (car fn) 'lambda))
	 (f.eprogn (cddr fn)
			   (extend env (cadr fn) args)
			   fenv ) )
	(else (evaluate-application3
		   (f.evaluate fn env fenv) args env fenv )) ) )

(define funcall
  (lambda (args)
	(if (> (length args) 1)
	    (invoke (car args) (cdr args))
		(wrong "Incorrect arity" 'funcall) ) ) )

; 2.2.3 Using Lisp(2)
(define fenv.global '())

(define-syntax definitial-function
  (syntax-rules ()
	((definitial-function name)
	 (begin (set! fenv.global (cons (cons 'name 'void) fenv.global))
			'name ) )
	((definitial-function name value)
	 (begin (set! fenv.global (cons (cons 'name value) fenv.global))
			'name ) ) ) )

(define-syntax defprimitive
  (syntax-rules ()
	((defprimitive name value arity)
	 (definitial-function name
	   (lambda (values)
		 (if (= arity (length values))
		     (apply value values)
			 (wrong "Incorrect arity" (list 'name values)) ) ) ) ) ) )

(defprimitive car car 1)
(defprimitive cons cons 2)

(define (chapter2-lisp2)
  (define (toplevel)
	(display (f.evaluate (read) env.global fenv.global))
	(toplevel) )
  (toplevel) )
