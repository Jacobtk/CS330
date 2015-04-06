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

;op-table used to define the valid operations for binop
(define op-table
  (list (list '+ +) (list '- -) (list '* *)))

;(lookup-op op) -> (or/c procedure? false/c)
; op : symbol?
(define (lookup-op op)
  (if (list? (assoc op op-table))
      (second (assoc op op-table))
      false))
 
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
                   (app (parse (first sexp)) (map parse (rest sexp)))
                   (error 'parse "Invalid syntax"))])]
           [else
            (if (andmap (lambda (x) (Expr? (parse x))) sexp)
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
     (t-bool)
     ]
    [(bin-num-op? e)
     (if (and (equal? (type-of (bin-num-op-lhs e)) (t-num))
              (equal? (type-of (bin-num-op-rhs e)) (t-num)))
         (t-num)
         (error 'type-of "error in typing of bin-num-op"))]
    [(iszero? e)
     (if (t-num? (type-of (iszero-e e)))
         (t-bool)
         (error 'type-of "expression for iszero did not evaluate to a number"))]
     
    [(bif? e)
     (if (and (t-bool? (type-of (bif-test e)))
              (equal? (type-of (bif-then e)) (type-of (bif-else e))))
         (type-of (bif-then e))
         (error 'type-of "problem type checking bif"))
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
     (if (and (t-fun? (type-of (app-fun-expr e)))
              (equal? (type-of (app-arg-expr e)) (fun-arg-type (app-fun-expr e))))
         (fun-result-type (app-fun-expr e))
         (error 'type-of "error type checking app expression"))
     ]
    [(nempty? e)
     (t-nlist)
     ]
    [(ncons? e)
     (t-nlist)
     ]
    [(nfirst? e)
     (if (t-nlist? (type-of (nfirst-e e)))
         (t-num)
         (error 'type-of "error type checking nfirst"))
     ]
    [(nrest? e)
     (if (t-nlist? (type-of (nfirst-e e)))
         (t-nlist)
         (error 'type-of "error type checking nrest"))
     ]
    [(isnempty? e)
     (if (t-nlist? (type-of (nfirst-e e)))
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
;correct typing of bin-op expressions
(test (type-of (parse '(+ 2 3))) (t-num))
(test (type-of (parse '(- 4 5))) (t-num))
(test (type-of (parse '(* 1 2))) (t-num))
;error catching for bin-op expressions
(test/exn (type-of (parse '(+ nempty 4))) "error in typing of bin-num-op")
(test/exn (type-of (parse '(- 5 true))) "error in typing of bin-num-op")

;correct typing of ncons
(test (type-of (parse '(ncons 3 nempty))) (t-nlist))
;correct typing of nfirst on empty list
(test (type-of (parse '(nfirst nempty))) (t-num))
;correct typing of nfirst on a cons
(test (type-of (parse '(nfirst (ncons 3 nempty)))) (t-num))
;correct typing of nrest






(define-type Binding
  [binding (name symbol?) (named-expr Expr?)])













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


