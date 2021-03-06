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

; Lisp1 from chapter1

(define the-non-initialized-marker (cons 'non 'initialized))

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
	  ((let)  ; ch 2.6.5
	   (eprogn (cddr e)
			   (extend env
					   (map (lambda (binding)
							  (if (symbol? binding) binding
								  (car binding) ) )
							(cadr e) )
					   (map (lambda (binding)
							  (if (symbol? binding) the-non-initialized-marker
								  (evaluate (cadr binding) env) ) )
							(cadr e) ) ) ) )
	  ((letrec)
	   (let ((new-env (extend env
							  (map car (cadr e))
							  (map (lambda (binding) the-non-initialized-marker)
								   (cadr e) ) )))
		 (map (lambda (binding)
				(update! (car binding)
						 new-env
						 (evaluate (cadr binding) new-env) ) )
			  (cadr e) )
		 (eprogn (cddr e) new-env) ) )
	  (else     (invoke (evaluate (car e) env)
						(evlis (cdr e) env) )) ) ) )

(define (eprogn exps env)
  (if (pair? exps)
	(if (pair? (cdr exps))
	  (begin (evaluate (car exps) env)
			 (eprogn (cdr exps) env) )
	  (evaluate (car exps) env) )
	empty-begin ) )

(define (evlis exps env)
  (if (pair? exps)
	  (cons (evaluate (car exps) env)
			(evlis (cdr exps) env) )
	  '() ) )

(define (make-function variables body env)
  (lambda (values)
	(eprogn body (extend env variables values)) ) )

(define (lookup id env)
  (if (pair? env)
	(if (eq? (caar env) id)
	    (let ((value (cdar env)))  ; 2.6.5
		  (if (eq? value the-non-initialized-marker)
			  (wrong "Uninitialized binding" id)
			  value ) )
		(lookup id (cdr env)) )
	(wrong "No such binding" id) ) )

(define (chapter2-lisp1)
  (define (toplevel)
	(display (evaluate (read) env.global))
	(toplevel) )
  (toplevel) )

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

(define (df.evlis exps env fenv denv)
  (if (pair? exps)
	(cons (df.evaluate (car exps) env fenv denv)
		  (df.evlis (cdr exps) env fenv denv) )
	'() ) )

; 2.5.3 Dynamic Variables without a Special Form

(define (dd.evaluate e env denv)
  (if (atom? e)
	  (cond ((symbol? e) (lookup e env))
			((or (number? e)(string? e)(char? e)(boolean? e)(vector? e)) e)
			(else (wrong "Cannot evaluate" e)) )
	  (case (car e)
		((quote) (cadr e))
		((if) (if (dd.evaluate (cadr e) env denv)
				  (dd.evaluate (caddr e) env denv)
				  (dd.evaluate (cadddr e) env denv) ))
		((begin) (dd.eprogn (cdr e) env denv))
		((set!) (update! (cadr e)
						 env
						 (dd.evaluate (caddr e) env denv)))
		((lambda) (dd.make-function (cadr e) (cddr e) env))
		(else (invoke (dd.evaluate (car e) env denv)
					  (dd.evlis (cdr e) env denv)
					  denv )) ) ) )

(define (dd.make-function variables body env)
  (lambda (values denv)
	(dd.eprogn body (extend env variables values) denv) ) )

(define (dd.evlis e* env denv)
  (if (pair? e*)
	(if (pair? (cdr e*))
	    (cons (dd.evaluate (car e*) env denv)
			  (dd.evlis (cdr e*) env denv) )
		(list (dd.evaluate (car e*) env denv)) )
	'() ) )

(define (dd.eprogn e* env denv)
  (if (pair? e*)
	(if (pair? (cdr e*))
	    (begin (dd.evaluate (car e*) env denv)
			   (dd.eprogn (cdr e*) env denv) )
		(dd.evaluate (car e*) env denv) )
	empty-begin ) )

(define-syntax definitial  ; from chapter 1
  (syntax-rules ()
	((definitial name)
	 (begin (set! env.global (cons (cons 'name 'void) env.global))
			'name ) )
	((definitial name value)
	 (begin (set! env.global (cons (cons 'name value) env.global))
			'name ) ) ) )

(define env.init '())
(define env.global env.init)

(definitial bind/de  ; bind-with-dynamic-extent
  (lambda (values denv)
	(if (= 3 (length values))
	  (let ((tag (car values))
			(value (cadr values))
			(thunk (caddr values)) )
		(invoke thunk '() (extend denv (list tag) (list value))) )
	  (wrong "Incorrect arity" 'bind/de) ) ) )

(definitial assoc/de
  (lambda (values current.denv)
	(if (= 2 (length values))
	    (let ((tag     (car values))
			  (default (cadr values)) )
		  (let look ((denv current.denv))
			(if (pair? denv)
			    (if (eqv? tag (caar denv))
				    (cdar denv)
					(look (cdr denv)) )
				(invoke default (list tag) current.denv) ) ) )
		(wrong "Incorrect arity" 'assoc/de) ) ) )

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
(defprimitive * * 2)

(define (chapter2-lisp2)
  (define (toplevel)
	(display (f.evaluate (read) env.global fenv.global))
	(toplevel) )
  (toplevel) )

; Chapter 1

(define atom?
  (lambda (x) (not (pair? x))))

(define wrong
  (lambda (msg stuff)
	(cons msg stuff)))

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
			 (wrong "Too less values" values) ) )
		((null? variables)
		     (if (null? values)
			   env
			   (wrong "Too much values" values) ) )
		((symbol? variables) (cons (cons variables values) env)) ) )

(define empty-begin 813)

(define (invoke fn args)
  (if (procedure? fn)
	  (fn args)
	  (wrong "Not a function" fn) ) )
