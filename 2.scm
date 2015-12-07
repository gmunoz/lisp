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
			  (f.lookup (cadr e) fenv) )
			 ((and (pair? (cadr e)) (eq? (car (cadr e)) 'lambda))
			  (f.make-function
				(cadr (cadr e)) (cddr (cadr e)) env fenv ) )
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
	  ((labels)
	   (let ((new-fenv (extend fenv
							   (map car (cadr e))
							   (map (lambda (def) 'void) (cadr e)) )))
		 (for-each (lambda (def)
					 (update! (car def)
							  new-fenv
							  (f.make-function (cadr def) (cddr def) env new-fenv) ) )
				   (cadr e) )
		 (f.eprogn (caddr e) env new-fenv) ) )
	  (else     (f.evaluate-application (car e)
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

(define (f.evaluate-application fn args env fenv)
  (cond ((symbol? fn)
		 ((f.lookup fn fenv) args) )
		((and (pair? fn) (eq? (car fn) 'lambda))
		 (f.eprogn (cddr fn)
				   (extend env (cadr fn) args)
				   fenv ) )
		(else (wrong "Incorrect functional term" fn)) ) )

(define (f.lookup id fenv)
  (if (pair? fenv)
	  (if (eq? (caar fenv) id)
		  (cdar fenv)
		  (f.lookup id (cdr fenv)) )
	  (lambda (values)
		(wrong "No such functional binding" id) ) ) )

(define (evaluate-application fn args env fenv)
  (cond ((symbol? fn)
		 ((lookup fn fenv) args))
		 ;(invoke (lookup fn fenv) args) )
		((and (pair? fn) (eq? (car fn) 'lambda))
		 (f.eprogn (cddr fn)
				   (extend env (cadr fn) args)
				   fenv ) )
		(else (wrong "Incorrect functional term" fn)) ) )

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

; 2.5.1 Dynamic variables

(define (df.evaluate e env fenv denv)
  (if (atom? e)
	(cond ((symbol? e) (lookup e env))
		  ((or (number? e)(string? e)(char? e)(boolean? e)(vector? e)) e)
		  (else (wrong "Cannot evaluate" e)) )
	(case (car e)
	  ((quote) (cadr e))
	  ((if) (if (df.evaluate (cadr e) env fenv denv)
			    (df.evaluate (caddr e) env fenv denv)
				(df.evaluate (cadddr e) env fenv denv) ))
	  ((begin) (df.eprogn (cdr e) env fenv denv))
	  ((set!) (update! (cadr e)
					   env
					   (df.evaluate (caddr e) env fenv denv) ))
	  ((function)
	   (cond ((symbol? (cadr e))
			  (f.lookup (cadr e) fenv) )
			 ((and (pair? (cadr e)) (eq? (car (cadr e)) 'lambda))
			  (df.make-function
				(cadr (cadr e)) (cddr (cadr e)) env fenv ) )
			 (else (wrong "Incorrect function" (cadr e))) ) )
	  ((dynamic) (lookup (cadr e) denv))
	  ((dynamic-set!)
	   (update! (cadr e)
				denv
				(df.evaluate (caddr e) env fenv denv) ) )
	  ((dynamic-let)
	   (df.eprogn (cddr e)
				  env
				  fenv
				  (extend denv
						  (map car (cadr e))
						  (map (lambda (e)
								 (df.evaluate e env fenv denv) )
							   (map cadr (cadr e)) ) ) ) )
	  (else (df.evaluate-application (car e)
									 (df.evlis (cdr e) env fenv denv)
									 env
									 fenv
									 denv )) ) ) )

(define (df.evaluate-application fn args env fenv denv)
  (cond ((symbol? fn) ((f.lookup fn fenv) args denv) )
		((and (pair? fn) (eq? (car fn) 'lambda))
		 (df.eprogn (cddr fn)
					(extend env (cadr fn) args)
					fenv
					denv ) )
		(else (wrong "Incorrect functional term" fn)) ) )

(define (df.make-function variables body env fenv)
  (lambda (values denv)
	(df.eprogn body (extend env variables values) fenv denv) ) )

(define (df.eprogn e* env fenv denv)
  (if (pair? e*)
	(if (pair? (cdr e*))
	    (begin (df.evaluate (car e*) env fenv denv)
			   (df.eprogn (cdr e*) env fenv denv) )
		(df.evaluate (car e*) env fenv denv) )
	empty-begin ) )

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

; Chapter 1

(define atom?
  (lambda (x) (not (pair? x))))

(define wrong
  (lambda (msg . stuff)
	msg))

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

(define empty-begin 813)

(define (invoke fn args)
  (if (procedure? fn)
	  (fn args)
	  (wrong "Not a function" fn) ) )

(define env.init '())
(define env.global env.init)
