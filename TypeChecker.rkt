#lang plai


(define-type Expr
  [num (n number?)]
  [id (v symbol?)]
  [bool (b boolean?)]
  [bin-num-op (op procedure?) (lhs Expr?) (rhs Expr?)]
  [iszero (e Expr?)]
  [bif (test Expr?) (then Expr?) (else Expr?)]
  [with (bound-id symbol?) (bound-body Expr?) (body Expr?)]
  [fun (arg-id symbol?)
       (arg-type Type?) (result-type Type?)
       (body Expr?)]
  [app (fun-expr Expr?) (arg-expr Expr?)]
  [nempty]
  [ncons (first Expr?) (rest Expr?)]
  [nfirst (e Expr?)]
  [nrest (e Expr?)]
  [isnempty (e Expr?)])
 
(define-type Type
  [t-num]
  [t-bool]
  [t-nlist]
  [t-fun (arg Type?) (result Type?)])
 
; parse : s-expression -> Expr
(define (parse sexp)
  (cond
    [(number? sexp) 
     (num sexp)]
    [(symbol? sexp) 
     (if (or (symbol=? 'with sexp) (symbol=? '+ sexp) (symbol=? '- sexp)
             (symbol=? '* sexp) (symbol=? '/ sexp) (symbol=? 'if0 sexp)
             (symbol=? 'fun sexp))
         (error 'parse "Invalid syntax")
         (id sexp))]
    [(list? sexp)
     (if (empty? sexp)
         (nempty)
         (cond
           [(procedure? (lookup-op (first sexp)))
            (if (and (equal? (length sexp) 3)
                     (Expr? (parse (second sexp)))
                     (Expr? (parse (third sexp))))
                (binop (lookup-op (first sexp)) (parse (second sexp)) (parse (third sexp)))
                (error 'parse "Invalid syntax"))]
           [(symbol? (first sexp))
            (cond
              [(symbol=? 'with (first sexp))
               (if (and (equal? (length sexp) 3)
                        (list? (second sexp))
                        (list? (parse-bindings (second sexp)))
                        (not (multipleBindings? (second sexp)))
                        (Expr? (parse (third sexp))))
                   (with (parse-bindings (second sexp)) (parse (third sexp)))
                   (error 'parse "Invalid syntax"))]
              [(symbol=? 'bif (first sexp))
               (if (and (equal? (length sexp) 4)
                        (Expr? (parse (second sexp)))
                        (Expr? (parse (third sexp)))
                        (Expr? (parse (fourth sexp))))
                   (bif (parse (second sexp)) (parse (third sexp)) (parse (fourth sexp)))
                   (error 'parse "Invalid syntax"))]
              [(symbol=? 'fun (first sexp))
               (if (and (equal? (length sexp) 3)
                        (list? (second sexp))
                        (andmap symbol? (second sexp))
                        (not (multipleBindingsFun? (second sexp)))
                        (Expr? (parse (third sexp))))
                   (fun (second sexp) (parse (third sexp))) ;create fun object
                   (error 'parse "Invalid syntax"))]
              [else
               (if (andmap (lambda (x) (CFWAE? (parse x))) sexp)
                   (app (parse (first sexp)) (map parse (rest sexp)))
                   (error 'parse "Invalid syntax"))])]
           [else
            (if (andmap (lambda (x) (CFWAE? (parse x))) sexp)
                (app (parse (first sexp)) (map parse (rest sexp)))
                (error 'parse "Invalid syntax"))]
           ))]
    [else
     (error 'parse "Invalid syntax")]))
 
; type-of : Expr -> Type
(define (type-of e)
  (cond
    [(num? e)
     (t-num)
     ]
    [(id? e)
     ;type check the id
     ]
    [(bool? e)
     (t-boolean)
     ]
    [(iszero? e)
     ;check if is a bool
     ;recurse on e checking if the exp has a num
     (t-bool)
     ]
    [(bif? e)
     ;check if is a bool
     ;recurse on e checking if the first exp is a bool
     ;second and third exp are equal return type of second
     ]
    [(with? e)
     ;recurse on the third expr,(the body) 
     ;check second that ID tied to exp, that ID type should be taken in of body of with
     ]
    [(fun? e)
     ;using the paremeter type in the body results in the specificed return type
     ;return type matchs the body's return type
     ]
    [(app? e)
     ;make sure parm type passed in matchs the expected
     ;return type matchs the body's return type
     ]
    [(nempty? e)
     (t-nlist)
     ]
    [(ncons? e)
     ;recurse on the first item
     ;if all is well returns nlist
     ]
    [(nfirst? e)
     ;input should be a list 
     ;recurse on the item in the list and return that type
     ]
    [(nrest? e)
     ;input should be a list
     ;should be nlist if all is well
     ]
    [(isnempty? e)
     ;make sure input is a list
     ;output is a t-bool
     ]
     )















(define-type Binding
  [binding (name symbol?) (named-expr CFWAE?)])

;; abstract syntax
(define-type CFWAE
  [num (n number?)]
  [binop (op procedure?) (lhs CFWAE?) (rhs CFWAE?)]
  [with (lob (listof Binding?)) (body CFWAE?)]
  [id (name symbol?)]
  [if0 (c CFWAE?) (t CFWAE?) (e CFWAE?)]
  [fun (args (listof symbol?)) (body CFWAE?)]
  [app (f CFWAE?) (args (listof CFWAE?))])

;; internal representation of possible return values
(define-type CFWAE-Value
  [numV (n number?)]
  [closureV (params (listof symbol?))
            (body CFWAE?)
            (env Env?)])

;; internal representation of an environment
(define-type Env
  [mtEnv]
  [anEnv (name symbol?) (value CFWAE-Value?) (env Env?)])

;; a function that extends the given environment with the list of bindings
(define (extend-Env env lob)
  (cond [(empty? lob) env]
        [else 
         (anEnv (binding-name (first lob)) (interp (binding-named-expr (first lob)) env) (extend-Env env (rest lob)))]))

;; lookup : symbol Env -> CFWAE-Value
;; looks up an identifier in an environment and returns the value
;; bound to it (or reports error if not found)
(define (lookup name env)
  (type-case Env env
    [mtEnv () (error 'lookup "no binding for identifier")]
    [anEnv (bound-name bound-value rest-env)
           (if (symbol=? bound-name name)
               bound-value
               (lookup name rest-env))]))


;op-table used to define the valid operations for binop
(define op-table
  (list (list '+ +) (list '- -) (list '* *) (list '/ /)))

;(lookup-op op) -> (or/c procedure? false/c)
; op : symbol?
(define (lookup-op op)
  (if (list? (assoc op op-table))
      (second (assoc op op-table))
      false))

;(parse-bindings (listof list?)) -> (listof Binding?)
; takes a list of lists and creates a list of bindings
(define (parse-bindings lob)
  (if (andmap (lambda (x) 
                (and (list? x) 
                     (equal? (length x) 2)
                     (symbol? (first x)) 
                     (CFWAE? (parse(second x)))))
              lob)
      (map (lambda (x) (binding (first x) (parse (second x)))) lob)
      false))

;This function is called to determine whether a with statement has duplicate bindings
(define (multipleBindings? lob)
  (cond [(empty? lob) 
         false]
        [(equal? (length lob) 1)
         false]
        [else
         (or (ormap (lambda (x) (symbol=? (first (first lob)) (first x))) (rest lob))
              (multipleBindings? (rest lob)))]))
         
;This function is called to determine whether a fun statement has duplicate bindings
(define (multipleBindingsFun? los)
  (cond [(empty? los)
         false]
        [(equal? (length los) 1)
         false]
        [else
         (or (ormap (lambda (x) (symbol=? (first los) x)) (rest los))
             (multipleBindingsFun? (rest los)))]))


;for app make sure the first thing returns a closure.
;make sure the length of the list of params in the closure matches the list of params in app.
;correct number of args and parameters (too few and too many)


;; parse : sexp −> CFWAE
;; to convert s-expressions into CFWAEs
(define (parse sexp)
  )

;PARSER TESTS
;id not +
(test/exn (parse '+) "Invalid syntax")
;id not -
(test/exn (parse '-) "Invalid syntax")
;id not *
(test/exn (parse '*) "Invalid syntax")
;id not /
(test/exn (parse '/) "Invalid syntax")
;id not with
(test/exn (parse 'with) "Invalid syntax")
;id not if0
(test/exn (parse 'if0) "Invalid syntax")
;id not fun
(test/exn (parse 'fun) "Invalid syntax")
;valid id
(test (parse 'x) (id 'x))
;duplicate identifiers with
(test/exn (parse '(with ([x 10] [x 20]) 50)) "Invalid syntax")
;duplicate identifiers fun
(test/exn (parse '(fun (x x) 10)) "Invalid syntax")
;parsing a number
(test (parse '5) (num 5))
;parsing a non-number literal
(test/exn (parse true) "Invalid syntax")
;parsing binop one operation
(test (parse '(+ 1 2)) (binop + (num 1) (num 2)))
;parsing binop another operation
(test (parse '(- 4 2)) (binop - (num 4) (num 2)))
;binop too many pieces
(test/exn (parse '(+ 2 4 6)) "Invalid syntax")
;binop too few pieces
(test/exn (parse '(- 6)) "Invalid syntax")
;valid with expression
(test (parse '(with ((x 2) (e 3)) 4))
      (with (list (binding 'x (num 2))
                  (binding 'e (num 3)))
            (num 4)))
;with too few pieces
(test/exn (parse '(with ((x 2)))) "Invalid syntax")
;with too many pieces
(test/exn (parse '(with ((x 2)) x 2)) "Invalid syntax")
;with bindings list not a list
(test/exn (parse '(with x 2)) "Invalid syntax")
;with individual binding expression not a list
(test/exn (parse '(with ((x 2) y) x)) "Invalid syntax")
;with individual binding too few pieces
(test/exn (parse '(with ((x) (y 2)) y)) "Invalid syntax")
;with individual binding too many pieces
(test/exn (parse '(with ((x 2 3)) x)) "Invalid syntax")
;with individual binding not bound to symbol
(test/exn (parse '(with ((2 2)) 1)) "Invalid syntax")
;valid with, no parameters
(test (parse '(with () 2)) (with '() (num 2)))
;empty list test
(test/exn (parse '()) "Invalid syntax")
;valid if0
(test (parse '(if0 0 1 2)) (if0 (num 0) (num 1) (num 2)))
;if0 too few pieces
(test/exn (parse '(if0 0 1)) "Invalid syntax")
;if0 too many pieces
(test/exn (parse '(if0 0 1 2 3)) "Invalid syntax")
;valid fun
(test (parse '(fun (x) x)) (fun '(x) (id 'x)))
;fun too few pieces
(test/exn (parse '(fun (x))) "Invalid syntax")
;fun too many pieces
(test/exn (parse '(fun (x) x 3)) "Invalid syntax")
;fun second element not a list
(test/exn (parse '(fun x x)) "Invalid syntax")
;valid fun empty args
(test (parse '(fun () 4)) (fun '() (num 4)))
;fun element of args is not a symbol
(test/exn (parse '(fun (2) 4)) "Invalid syntax")
;valid app
(test (parse '((fun (x) (* x 2)) 4)) (app (fun '(x) (binop * (id 'x) (num 2))) (list (num 4))))


;this function is called by the interpreter. It performs the given op on the operands and returns the appropriate numV
(define (performBinop op left right)
  (cond [(and (equal? op /)
              (zero? (numV-n right)))
         (error 'interp "Divide by zero error")]
        [(or (not (numV? left))
             (not (numV? right)))
         (error 'interp "Cannot apply operator to non-number value")]
        [else
         (numV (op (numV-n left) (numV-n right)))]))

(define (extendEnvFun lop args env fun-env)
  (if (empty? lop)
      fun-env
      (anEnv (first lop) (interp (first args) env) (extendEnvFun (rest lop) (rest args) env fun-env))))


;; interp : CFWAE Env -> CFWAE-Value
;; evaluates an expression with respect to the current environment
(define (interp expr env)
  (type-case CFWAE expr
    [num (n) (numV n)]
    [binop (op l r) (performBinop op (interp l env) (interp r env))]
    [id (v) (lookup v env)]
    [with (lob body)
          (interp body (extend-Env env lob))]
    [if0 (test then else)
         (if (numV? (interp test env))
             (if (zero? (numV-n (interp test env)))
                 (interp then env)
                 (interp else env))
             (error 'interp "test condition did not evaluate to a number"))]
    [fun (args bound-body)
         (closureV args bound-body env)]
    [app (fun-expr args)
         (if (closureV? (interp fun-expr env))
             (if (equal? (length args) (length (closureV-params (interp fun-expr env))))
                 (interp (closureV-body (interp fun-expr env)) (extendEnvFun 
                                                                (closureV-params (interp fun-expr env)) 
                                                                args 
                                                                env 
                                                                (closureV-env (interp fun-expr env))))
                 (error 'interp "wrong number of arguments"))
             (error 'interp "Invalid first argument to app production"))]))



;; run : s-expression -> numV
;; parses then evaluates an s-expression in the CFWAE language
(define (run expr) 
  (interp 
   (parse expr)
   (mtEnv)))

;INTERP TESTS

;num TESTS
;interpreting a num
(test (run '0) (numV 0))

;id TESTS
;interpreting an id
(test/exn (run 'x) "no binding for identifier")

;binop TESTS
;interpreting a binop with +
(test (run '(+ 2 4)) (numV 6))
;interpreting a binop with -
(test (run '(- 5 1)) (numV 4))
;interpreting a binop with *
(test (run '(* 3 4)) (numV 12))
;interpreting a binop with /
(test (run '(/ 10 2)) (numV 5))
;divide by zero test
(test/exn (run '(/ 4 0)) "Divide by zero error")
;binop operand not numV
(test/exn (run '(* (fun (x) x) 3)) "Cannot apply operator to non-number value")

;if0 TESTS
;test condition of if0 does not return numV
(test/exn (run '(if0 (fun (x) x) 1 2)) "test condition did not evaluate to a number")
;if0 test is true
(test (run '(if0 0 3 4)) (numV 3))
;if0 test is false
(test (run '(if0 1 3 4)) (numV 4))
;if0 returns a closure
(test (run '(if0 (with ((x 0)) x) (fun (x) x) 4)) (closureV '(x) (id 'x) (mtEnv)))

;with TESTS
;basic bound id
(test (run '(with ((x 3)) x)) (numV 3))
;with shadowing
(test (run '(with ((x 3)) (with ((x (- x 1))) x))) (numV 2))
;the other shadowing test case that I'm hoping I'm understanding correctly
(test (run '(with ((x 2)) (with ((y 4)) (+ x y)))) (numV 6))

;fun TESTS
;interpreting a fun
(test (run '(fun (x) (+ x 1))) (closureV '(x) (binop + (id 'x) (num 1)) (mtEnv)))

;app TESTS
;the first element does not evaluate to a closureV
(test/exn (run '(4 (* 4 3))) "Invalid first argument to app production")
;too few arguments
(test/exn (run '((fun (x y) (+ x y)) 3)) "wrong number of arguments")
;too many arguments
(test/exn (run '((fun (x) (* x x)) 2 3)) "wrong number of arguments")
;zero arguments
(test (run '((fun () (* 2 3)))) (numV 6))
;with as beginning of app
(test (run '((with ((x 4)) (fun (y) (* x y))) 2)) (numV 8))
;if0 as beginning of app
(test (run '((if0 1 0 (fun (x) (+ 2 x))) 3)) (numV 5))



;; -- some examples --

;(run '(with ((double (fun (x) (+ x x)))) {(double 5)}))

;(run '{fun {x} x})

;(run '{fun {x}
;           {fun {y} 
 ;               {+ x y}}})

;(run '{
  ;     {fun {x}
   ;         {fun {y} 
    ;             {+ x y}}}
     ;  3
      ; })

;(run '{with {x 3}
 ;           {fun {y}
  ;               {+ x y}}})

;(run '{with {add3 {with {x 3}
 ;                       {fun {y}
  ;                           {+ x y}}}}
   ;         {add3 5}})

