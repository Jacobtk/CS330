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

(define-type Env
  [mtEnv]
  [anEnv (name symbol?) (value Type?) (env Env?)])


(define (lookup name env)
  (type-case Env env
    [mtEnv () (error 'lookup "no binding for identifier")]
    [anEnv (bound-name bound-value rest-env)
           (if (symbol=? bound-name name)
               bound-value
               (lookup name rest-env))]))

(define-type Binding
  [binding (name symbol?) (named-expr Type?)])


;op-table used to define the valid operations for binop
(define op-table
  (list (list '+ +) (list '- -) (list '* *)))

;(lookup-op op) -> (or/c procedure? false/c)
; op : symbol?
(define (lookup-op op)
  (if (list? (assoc op op-table))
      (second (assoc op op-table))
      false))

;parses a symbol into a Type
(define (parse-type sym)
  (cond [(symbol=? sym 't-num)
         (t-num)]
        [(symbol=? sym 't-bool)
         (t-bool)]
        [(symbol=? sym 't-nlist)
         (t-nlist)]
        [else
         (error 'parse-type "haven't implemented this function for t-fun type")]))

; parse : s-expression -> Expr
(define (parse sexp)
  (cond
    [(number? sexp) 
     (num sexp)]
    [(symbol? sexp) 
     (cond [(or (symbol=? 'with sexp) (symbol=? '+ sexp) (symbol=? '- sexp)
                (symbol=? '* sexp) (symbol=? '/ sexp) (symbol=? 'bif sexp)
                (symbol=? 'fun sexp))
            (error 'parse "Invalid syntax")]
           [(symbol=? 'true sexp)
            (bool true)]
           [(symbol=? 'false sexp)
            (bool false)]
           [(symbol=? 'nempty sexp)
            (nempty)]
           [else
            (id sexp)])]
    [(list? sexp)
     (if (empty? sexp)
         (error 'parse "Invalid syntax")
         (cond
           [(procedure? (lookup-op (first sexp)))
            (if (and (equal? (length sexp) 3)
                     (Expr? (parse (second sexp)))
                     (Expr? (parse (third sexp))))
                (bin-num-op (lookup-op (first sexp)) (parse (second sexp)) (parse (third sexp)))
                (error 'parse "Invalid syntax"))]
           [(symbol? (first sexp))
            (cond
              [(symbol=? 'with (first sexp))  ;change to reflect new with 
               (with (second sexp)
                     (parse (third sexp))
                     (parse (fourth sexp)))]
              [(symbol=? 'bif (first sexp))
               (if (and (equal? (length sexp) 4)
                        (Expr? (parse (second sexp)))
                        (Expr? (parse (third sexp)))
                        (Expr? (parse (fourth sexp))))
                   (bif (parse (second sexp)) (parse (third sexp)) (parse (fourth sexp)))
                   (error 'parse "Invalid syntax"))]
              [(symbol=? 'fun (first sexp))
               (fun (second sexp) (parse-type (third sexp)) (parse-type (fourth sexp)) (parse (fifth sexp)))]
              [(symbol=? 'iszero (first sexp))
               (iszero (parse (second sexp)))]               
              [(symbol=? 'ncons (first sexp))
               (ncons (parse (second sexp)) (parse (third sexp)))]
              [(symbol=? 'nfirst (first sexp))
               (nfirst (parse (second sexp)))]
              [(symbol=? 'nrest (first sexp))
               (nrest (parse (second sexp)))]
              [(symbol=? 'isnempty (first sexp))
               (isnempty (parse (second sexp)))]
              [else
               (if (andmap (lambda (x) (Expr? (parse x))) sexp)
                   (app (parse (first sexp)) (parse (second sexp)))
                   (error 'parse "Invalid syntax"))])]
           [else
            (if (andmap (lambda (x) (Expr? (parse x))) sexp)
                (app (parse (first sexp)) (parse (second sexp)))
                (error 'parse "Invalid syntax"))]
           ))]
    [else
     (error 'parse "Invalid syntax")]))



(define (type-of e)
  (type-of-rec e (mtEnv))
  )

; type-of : Expr -> Type
(define (type-of-rec e env) ;make a recursive helper fun that takes an empty type env
  (cond
    [(num? e)
     (t-num)]
    [(id? e)
     (type-case Expr e
       [id (v) (lookup v env)]
       [else 
        (error 'type-of "casting to symbol error")]
         )]
    [(bool? e)
     (t-bool)]
    [(bin-num-op? e)
     (if (and (equal? (type-of-rec (bin-num-op-lhs e) env) (t-num))
              (equal? (type-of-rec (bin-num-op-rhs e) env) (t-num)))
         (t-num)
         (error 'type-of "error in typing of bin-num-op"))]
    [(iszero? e)
     (if (t-num? (type-of-rec (iszero-e e) env))
         (t-bool)
         (error 'type-of "expression for iszero did not evaluate to a number"))]
    [(bif? e)
     (if (and (t-bool? (type-of-rec (bif-test e) env))
              (equal? (type-of-rec (bif-then e) env) (type-of-rec (bif-else e) env)))
         (type-of-rec (bif-then e) env)
         (error 'type-of "error type checking bif"))]
    [(with? e)
     ;bind the var to its type
     ;(binding (with-bound-id e) (type-of-rec (with-bound-body e) env))
     ;exntend the env by adding the freshly created binding
     (type-of-rec (with-body e) (anEnv (with-bound-id e) (type-of-rec (with-bound-body e) env) env))
     ;call (type-of-rec (with-body e) env)
     ]
    [(fun? e)
     (if (equal? (fun-result-type e)
                 (type-of-rec (fun-body e) (anEnv (fun-arg-id e) (fun-arg-type e) env)))
         (t-fun (fun-arg-type e) (fun-result-type e))
         (error 'type-of "error type checking fun"))
     ]
    [(app? e)
     (if (and (t-fun? (type-of-rec (app-fun-expr e) env))
              (equal? (type-of-rec (app-arg-expr e) env) (fun-arg-type (app-fun-expr e))))
         (fun-result-type (app-fun-expr e))
         (error 'type-of "error type checking app expression"))
     ]
    [(nempty? e)
     (t-nlist)
     ]
    [(ncons? e)
     (if (and (t-num? (type-of-rec (ncons-first e) env))
              (t-nlist? (type-of-rec (ncons-rest e) env)))
         (t-nlist)
         (error 'type-of "error type checking ncons"))]
    [(nfirst? e)
     (if (t-nlist? (type-of-rec (nfirst-e e) env))
         (t-num)
         (error 'type-of "error type checking nfirst"))
     ]
    [(nrest? e)
     (if (t-nlist? (type-of-rec (nrest-e e) env))
         (t-nlist)
         (error 'type-of "error type checking nrest"))
     ]
    [(isnempty? e)
     (if (t-nlist? (type-of-rec (isnempty-e e) env))
         (t-bool)
         (error 'type-of "error type checking isnempty"))
     ]
    ))





;TESTS
;correct typing of num
(test (type-of (parse 2)) (t-num))
;correct typing of bools
(test (type-of (parse 'true)) (t-bool))
(test (type-of (parse 'false)) (t-bool))
;correct typing of empty list
(test (type-of (parse 'nempty)) (t-nlist))
(test/exn (type-of (parse 'x)) "no binding")

;BIN-NUM-OP
;correct typing of bin-op expressions
(test (type-of (parse '(+ 2 3))) (t-num))
(test (type-of (parse '(- 4 5))) (t-num))
(test (type-of (parse '(* 1 2))) (t-num))
;error catching for bin-op expressions
(test/exn (type-of (parse '(+ nempty 4))) "error in typing of bin-num-op")
(test/exn (type-of (parse '(* 4 nempty))) "error in typing of bin-num-op")
(test/exn (type-of (parse '(- 5 true))) "error in typing of bin-num-op")
(test/exn (type-of (parse '(* false 6))) "error in typing of bin-num-op")
;test bin-num-op with t-fun as parameters
(test/exn (type-of (parse '(+ (fun x t-bool t-num (bif x 1 0)) 4))) "error in typing of bin-num-op")
(test/exn (type-of (parse '(+ 3 (fun x t-bool t-num (bif x 1 0))))) "error in typing of bin-num-op")

;ISZERO
;correct typing of iszero
(test (type-of (parse '(iszero 0))) (t-bool))
(test (type-of (parse '(iszero 7))) (t-bool))
;incorrect typing of iszero
(test/exn (type-of (parse '(iszero false))) "iszero")
(test/exn (type-of (parse '(iszero nempty))) "iszero")
(test/exn (type-of (parse '(iszero (fun x t-num t-num x)))) "iszero")

;BIF
;correct typing of bif
(test (type-of (parse '(bif true 4 5))) (t-num))
(test (type-of (parse '(bif true false true))) (t-bool))
(test (type-of (parse '(bif false nempty (ncons 4 nempty)))) (t-nlist))
(test (type-of (parse '(bif true (fun x t-num t-num (+ x 1)) (fun y t-num t-num (- y 1))))) (t-fun (t-num) (t-num)))
;incorrect typing of bif
(test/exn (type-of (parse '(bif 4 3 2))) "error type checking bif")
(test/exn (type-of (parse '(bif nempty 0 1))) "error type checking bif")
(test/exn (type-of (parse '(bif (fun x t-bool t-bool x) 4 5))) "error type checking bif")
(test/exn (type-of (parse '(bif true 4 false))) "error type checking bif")
(test/exn (type-of (parse '(bif true (fun x t-num t-num x) (fun y t-bool t-bool y)))) "error type checking bif")

;WITH
(test/exn (type-of (parse '(with x 5 y))) "no binding")
(test (type-of (parse '(with x 5 x))) (t-num))

;FUN
;correct typing of fun
(test (type-of (parse '(fun x t-bool t-num (bif x 0 1)))) (t-fun (t-bool) (t-num)))
;incorrect typing of fun
(test/exn (type-of (parse '(fun x t-bool t-bool (bif x 0 1)))) "error type checking fun")

;APP
;correct typing of app
(test (type-of (parse '((fun x t-num t-bool (iszero (- x 1))) 1))) (t-bool))
;incorrect typing of app
(test/exn (type-of (parse '(4 3))) "error type checking app")
(test/exn (type-of (parse '(true 3))) "error type checking app")
(test/exn (type-of (parse '(nempty 4))) "error type checking app")
(test/exn (type-of (parse '((fun x t-num t-bool (iszero (- x 1))) true))) "error type checking app")

;NCONS
;correct typing of ncons
(test (type-of (parse '(ncons 3 nempty))) (t-nlist))
;ncons first param is incorrect
(test/exn (type-of (parse '(ncons true nempty))) "error type checking ncons")
(test/exn (type-of (parse '(ncons nempty nempty))) "error type checking ncons")
(test/exn (type-of (parse '(ncons (fun x t-num t-num x) nempty))) "error type checking ncons")
;ncons second param is incorrect
(test/exn (type-of (parse '(ncons 4 4))) "error type checking ncons")
(test/exn (type-of (parse '(ncons 4 false))) "error type checking ncons")
(test/exn (type-of (parse '(ncons 4 (fun x t-nlist t-nlist nempty)))) "error type checking ncons")

;NFIRST
;correct typing of nfirst on list
(test (type-of (parse '(nfirst nempty))) (t-num))
(test (type-of (parse '(nfirst (ncons 3 nempty)))) (t-num))
;incorrect nfirst typing
(test/exn (type-of (parse '(nfirst 4))) "error type checking nfirst")
(test/exn (type-of (parse '(nfirst true))) "error type checking nfirst")
(test/exn (type-of (parse '(nfirst (fun x t-nlist t-nlist nempty)))) "error type checking nfirst")

;NREST
;correct typing of nrest
(test (type-of (parse '(nrest nempty))) (t-nlist))
(test (type-of (parse '(nrest (ncons 7 nempty)))) (t-nlist))
;incorrect nrest typing
(test/exn (type-of (parse '(nrest 3))) "error type checking nrest")
(test/exn (type-of (parse '(nrest false))) "error type checking nrest")
(test/exn (type-of (parse '(nrest (fun x t-nlist t-nlist nempty)))) "error type checking nrest")

;ISNEMPTY
;correct typing of isnempty
(test (type-of (parse '(isnempty nempty))) (t-bool))
(test (type-of (parse '(isnempty (ncons 4 nempty)))) (t-bool))
;incorrect isnempty typing
(test/exn (type-of (parse '(isnempty 4))) "error type checking isnempty")
(test/exn (type-of (parse '(isnempty false))) "error type checking isnempty")
(test/exn (type-of (parse '(isnempty (fun x t-nlist t-nlist nempty)))) "error type checking isnempty")













;(parse-bindings (listof list?)) -> (listof Binding?)
; takes a list of lists and creates a list of bindings
(define (parse-bindings lob)
  (if (andmap (lambda (x) 
                (and (list? x) 
                     (equal? (length x) 2)
                     (symbol? (first x)) 
                     (Expr? (parse(second x)))))
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


