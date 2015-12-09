; Conventions:
; * A variable suffixed by a star represents a list of whatever the same
;   variable without the star would represent.
;
; e, et, ec, ef ...   expression, form
;             r ...   environment
;         k, kk ...   continuation
;             v ...   value (integer, pair, closure, etc.)
;             f ...   function
;             n ...   identifier

; 3.2.2 The Interpreter for Continuations
(define (evaluate e r k)
  (if (atom? e)
	(cond ((symbol? e) (evaluate-variable e r k))
		  (else        (evaluate-quote e r k)) )
	(case (car e)
	  ((quote)  (evaluate-quote (cadr e) r k))
	  ((if)     (evaluate-if (cadr e) (caddr e) (cadddr e) r k))
	  ((begin)  (evaluate-begin (cdr e) r k))
	  ((set!)   (evaluate-set! (cadr e) (caddr e) r k))
	  ((lambda) (evaluate-lambda (cadr e) (cddr e) r k))
	  (else     (evaluate-application (car e) (cdr e) r k)) ) ) )

(define-generic (invoke (f) v* r k)
  (wrong "not a function" f r k) )
(define-generic (resume (k continuation) v)
  (wrong "Unknown continuation" k) )
(define-generic (lookup (r environment) n k)
  (wrong "not an environment" r n k) )
(define-generic (update! (r environment) n k v)
  (wrong "not an environment" r n k) )

(define-class value Object ())
(define-class environment Object ())
(define-class continuation Object (k))

; 3.2.3 Quoting
(define (evaluate-quote v r k)
  (resume k v) )

; 3.2.4 Alternatives
(define-class if-cont continuation (et ef r))
(define (evaluate-if ec et ef r k)
  (evaluate ec r (make-if-cont k
							   et
							   ef
							   r )) )
(define-method (resume (k if-cont) v)
  (evaluate (if v (if-cont-et k) (if-cont-ef k))
			(if-cont-r k)
			(if-cont-k k) ) )

; 3.2.5 Sequence
(define-class begin-cont continuation (e* r))
(define (evaluate-begin e* r k)
  (if (pair? e*)
	(if (pair? (cdr e*))
	  (evaluate (car e*) r (make-begin-cont k e* r))
	  (evaluate (car e*) r k) )
	(resume k empty-begin-value) ) )
(define-method (resume (k begin-cont) v)
  (evaluate-begin (cdr (begin-cont-e* k))
				  (begin-cont-r k)
				  (begin-cont-k k) ) )

; 3.2.6 Variable Environment
(define-class null-env environment ())
(define-class full-env environment (others name))
(define-class variable-env full-env (value))

(define (evaluate-variable n r k)
  (lookup r n k) )
(define-method (lookup (r null-env) n k)
  (wrong "Unknown variable" n r k) )
(define-method (lookup (r full-env) n k)
  (lookup (full-env-others r) n k) )
(define-method (lookup (r variable-env) n k)
  (if (eqv? n (variable-env-name r))
	(resume k (variable-env-value r))
	(lookup (variable-env-others r) n k) ) )

(define-class set!-cont continuation (n r))
(define (evaluate-set! n e r k)
  (evaluate e r (make-set!-cont k n r)) )
(define-method (resume (k set!-cont) v)
  (update! (set!-cont-r k) (set!-cont-n k) (set!-cont-k k) v) )
(define-method (update! (r null-env) n k v)
  (wrong "Unknown variable" n r k) )
(define-method (update! (r full-env) n k v)
  (update! (full-env-others r) n k v) )
(define-method (update! (r variable-env) n k v)
  (if (eqv? n (variable-env-name r))
	(begin (set-variable-env-value! r v)
		   (resume k v) )
	(update! (variable-env-others r) n k v) ) )

; 3.2.7 Functions
(define-class function value (variables body env))
(define (evaluate-lambda n* e* r k)
  (resume k (make-function n* e* r)) )

(define-method (invoke (f function) v* r k)
  (let ((env (extend-env (function-env f)
						 (function-variables f)
						 v* )))
	(evaluate-begin (function-body f) env k) ) )

(define (extend-env env names values)
  (cond ((and (pair? names) (pair? values))
		 (make-variable-env
		   (extend-env env (cdr names) (cdr values))
		   (car names)
		   (car values) ) )
		((and (null? names) (null? values)) env)
		((symbol? names) (make-variable-env env names values))
		(else (wrong "Arity mismatch")) ) )

(define-class evfun-cont continuation (e* r))
(define-class apply-cont continuation (f r))
(define-class argument-cont continuation (e* r))
(define-class gather-cont continuation (v))
(define (evaluate-application e e* r k)
  (evaluate e r (make-evfun-cont k e* r)) )
(define-method (resume (k evfun-cont) f)
  (evaluate-arguments (evfun-cont-e* k)
					  (evfun-cont-r k)
					  (make-apply-cont (evfun-cont-k k)
									   f
									   (evfun-cont-r k) ) ) )
(define (evaluate-arguments e* r k)
  (if (pair? e*)
	(evaluate (car e*) r (make-argument-cont k e* r))
	(resume k no-more-arguments) ) )
(define no-more-arguments '())
(define-method (resume (k argument-cont) v)
  (evaluate-arguments (cdr (argument-cont-e* k))
					  (argument-cont-r k)
					  (make-gather-cont (argument-cont-k k) v)) )
(define-method (resume (k gather-cont) v*)
  (resume (gather-cont-k k) (cons (gather-cont-v k) v*)) )
(define-method (resume (k apply-cont) v)
  (invoke (apply-cont-f k)
		  v
		  (apply-cont-r k)
		  (apply-cont-k k) ) )

; 3.3 Initializing the Interpreter
(define-syntax definitial
  (syntax-rules ()
	((definitial name)
	 (definitial name 'void) )
	((definitial name value)
	 (begin (set! r.init (make-variable-env r.init 'name value))
			'name ) ) ) )
(define-class primitive value (name address))
(define-syntax defprimitive
  (syntax-rules ()
	((defprimitive name value arity)
	 (definitial name
	   (make-primitive
		 'name (lambda (v* r k)
				 (if (= arity (length v*))
				     (resume k (apply value v*))
					 (wrong "Incorrect arity" 'name v*) ) ) ) ) ) ) )
(define r.init (make-null-env))
(defprimitive cons cons 2)
(defprimitive car car 1)

(define-method (invoke (f primitive) v* r k)
  ((primitive-address f) v* r k) )

(define-class bottom-cont continuation (f))
(define-method (resume (k bottom-cont) v)
  ((bottom-cont-f k) v) )
(define (chapter3-interpreter)
  (define (toplevel)
	(evaluate (read)
			  r.init
			  (make-bottom-cont 'void display) )
	(toplevel) )
  (toplevel) )
