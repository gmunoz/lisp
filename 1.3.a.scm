(define (evaluate exp env)
  (if (atom? exp)
  	(if (symbol? exp) (lookup exp env) exp)
	(case (car exp)
	  ...
	  (else ...) ) ) )

; (define (lookup variable environment) )
