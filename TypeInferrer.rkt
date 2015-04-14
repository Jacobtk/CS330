#lang plai


(define-type Expr
  [num (n number?)]
  [id (v symbol?)]
  [bool (b boolean?)]
  [bin-num-op (op procedure?) (lhs Expr?) (rhs Expr?)]
  [iszero (e Expr?)]
  [bif (test Expr?) (then Expr?) (else Expr?)]
  [with (bound-id symbol?) (bound-body Expr?) (body Expr?)]
  [rec-with (bound-id symbol?) (bound-body Expr?) (body Expr?)]
  [fun (arg-id symbol?) (body Expr?)]
  [app (fun-expr Expr?) (arg-expr Expr?)]
  [tempty]
  [tcons (first Expr?) (rest Expr?)]
  [tfirst (e Expr?)]
  [trest (e Expr?)]
  [istempty (e Expr?)])
 
(define-type Type
  [t-num]
  [t-bool]
  [t-list (elem Type?)]
  [t-fun (arg Type?) (result Type?)]
  [t-var (v symbol?)])

(define-type locAlos
  [loi (loc list?) (los list?)])

(define-type Constraint
  [eqc (lhs Type?) (rhs Type?)])

(define-type Env
  [mtEnv]
  [anEnv (name symbol?) (value symbol?) (env Env?)])

(define (lookup name env)
  (type-case Env env
    [mtEnv () (error 'lookup "no binding for identifier")]
    [anEnv (bound-name bound-value rest-env)
           (if (symbol=? bound-name name)
               bound-value
               (lookup name rest-env))]))


;op-table used to define the valid operations for binop
(define op-table
  (list (list '+ +) (list '- -) (list '* *)))

;(lookup-op op) -> (or/c procedure? false/c)
; op : symbol?
(define (lookup-op op)
  (if (list? (assoc op op-table))
      (second (assoc op op-table))
      false))

;parse-type : symbol -> Type
;parses a symbol into a Type
(define (parse-type sym)
  (cond [(symbol=? sym 't-num)
         (t-num)]
        [(symbol=? sym 't-bool)
         (t-bool)]
        [(symbol=? sym 't-nlist)
         (t-list)]
        [else
         (error 'parse-type "haven't implemented this function for t-fun type")]))



; parse : s-expression -> Expr
; parses the sexp passed in and builds an abstract syntax tree
(define (parse sexp)
  (cond
    [(number? sexp) 
     (num sexp)]
    [(symbol? sexp) 
     (cond [(or (symbol=? 'rec-with sexp) (symbol=? '+ sexp) (symbol=? '- sexp)
                (symbol=? '* sexp) (symbol=? 'iszero sexp) (symbol=? 'bif sexp)
                (symbol=? 'fun sexp))
            (error 'parse "Invalid syntax")]
           [(symbol=? 'true sexp)
            (bool true)]
           [(symbol=? 'false sexp)
            (bool false)]
           [(symbol=? 'tempty sexp)
            (tempty)]
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
              [(symbol=? 'rec-with (first sexp))
               (rec-with (second sexp)
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
               (fun (second sexp) (parse (third sexp)))]
              [(symbol=? 'iszero (first sexp))
               (iszero (parse (second sexp)))]               
              [(symbol=? 'tcons (first sexp))
               (tcons (parse (second sexp)) (parse (third sexp)))]
              [(symbol=? 'tfirst (first sexp))
               (tfirst (parse (second sexp)))]
              [(symbol=? 'trest (first sexp))
               (trest (parse (second sexp)))]
              [(symbol=? 'istempty (first sexp))
               (istempty (parse (second sexp)))]
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


(define (alpha-vary e)
  (alpha-vary-rec e (mtEnv)))

(define (alpha-vary-rec e env)
  (cond
    [(num? e) e]
    [(id? e)
        ;id
       (if (lookup (id-v e) env)
           (id (lookup (id-v e) env))
           (error 'type-of "casting to symbol error")
         )
        ]
    [(bool? e) e]
    [(bin-num-op? e)
               (bin-num-op (bin-num-op-op e) 
                           (alpha-vary-rec (bin-num-op-lhs e) env) 
                           (alpha-vary-rec (bin-num-op-rhs e) env)) 
                ]
    [(iszero? e) e]
    [(bif? e) 
         (bif 
          (alpha-vary-rec (bif-test e) env) 
          (alpha-vary-rec (bif-then e) env) 
          (alpha-vary-rec (bif-else e) env))
         ]
    [(with? e) 
          ;with ;how to check for unbound symbol in body
          (begin
           (local ([define x (gensym (with-bound-id e))])
         ; (with x (alpha-vary-rec (with-bound-body e) env) (alpha-vary-rec (with-body e) (anEnv (with-bound-id e) x env)))))
             (with x 
                   (alpha-vary-rec (with-bound-body e) env) 
                   (alpha-vary-rec (with-body e) (anEnv (with-bound-id e) x env)))
             ))
          ]
    [(rec-with? e) 
              ;rec with
          (begin
           (local ([define x (gensym (rec-with-bound-id e))])
             (rec-with x 
                       (alpha-vary-rec (rec-with-bound-body e) (anEnv (rec-with-bound-id e) x env)) 
                       (alpha-vary-rec (rec-with-body e) (anEnv (rec-with-bound-id e) x env)))))]

    [(fun? e) 
         ;fun
          (begin
           (local ([define x (gensym (fun-arg-id e))])
             (fun (fun-arg-id e) (alpha-vary-rec (fun-body e) (anEnv (fun-arg-id e) x env)))
             ))
     ]
    [(app? e) 0]
    [(tempty? e) e]
    [(tcons? e)  
           (tcons (tcons-first e) (tcons-rest e))
           ]
    [(tfirst? e) e]
    [(trest? e) e]
    [(istempty? e) e]
    ))
    
    


(define (generate-constraints e-id e)
  (type-case Expr e
    (num (n) (list (eqc (t-var e-id) (t-num))))
    (id (v) (list (eqc (t-var e-id) (t-var v))))
    (bool (b) (list (eqc (t-var e-id) (t-bool))))
    (bin-num-op (op lhs rhs)
                (local ([define lhs-id (gensym)]
                        [define rhs-id (gensym)]
                        [define lhs-c (generate-constraints lhs-id lhs)]
                        [define rhs-c (generate-constraints rhs-id rhs)])
                  (append 
                   (list (eqc (t-var e-id) (t-num))
                         (eqc (t-var lhs-id) (t-num))
                         (eqc (t-var rhs-id) (t-num)))
                   lhs-c
                   rhs-c)))
    (iszero (expr) 
            (local ([define expr-id (gensym)]
                    [define expr-c (generate-constraints expr-id expr)])
              (append
               (list (eqc (t-var e-id) (t-bool))
                     (eqc (t-var expr-id) (t-num)))
               expr-c)))
    (bif (test then else) 
         (local ([define test-id (gensym)]
                 [define then-id (gensym)]
                 [define else-id (gensym)]
                 [define test-c (generate-constraints test-id test)]
                 [define then-c (generate-constraints then-id then)]
                 [define else-c (generate-constraints else-id else)])
           (append
            (list (eqc (t-var test-id) (t-bool))
                  (eqc (t-var e-id) (t-var then-id))
                  (eqc (t-var then-id) (t-var else-id)))
            test-c
            then-c
            else-c)))
    (with (bound-id bound-body body) 
          0)
    (rec-with (bound-id bound-body body) 0)
    (fun (arg-id body) 0)
    (app (fun-expr arg-expr) 0)
    (tempty () (list (eqc (t-var e-id) (t-list (t-var (gensym))))))
    (tcons (first rest) 
           (local ([define first-id (gensym)]
                   [define rest-id (gensym)]
                   [define first-c (generate-constraints first-id first)]
                   [define rest-c (generate-constraints rest-id rest)])
             (append 
              (list (eqc (t-var e-id) (t-list (t-var first-id)))
                    (eqc (t-var rest-id) (t-list (t-var first-id))))
              first-c
              rest-c)))
    (tfirst (expr) 
            (local ([define expr-id (gensym)]
                    [define return (gensym)]
                    [define expr-c (generate-constraints expr-id expr)])
              (append
               (list (eqc (t-var e-id) (t-var return))
                     (eqc (t-var expr-id) (t-list (t-var return)))   
                     )
               expr-c)))
                     
    (trest (expr) 
           (local ([define expr-id (gensym)]
                   [define list-type (gensym)]
                   [define expr-c (generate-constraints expr-id expr)])
             (append
              (list (eqc (t-var expr-id) (t-list (t-var list-type)))
                    (eqc (t-var e-id) (t-list (t-var list-type))))
              expr-c)))
    (istempty (expr) 
              (local ([define expr-id (gensym)]
                      [define list-type (gensym)]
                      [define expr-c (generate-constraints expr-id expr)])
                (append
                 (list (eqc (t-var e-id) (t-bool))
                       (eqc (t-var expr-id) (t-list (t-var list-type))))
                 expr-c)))
     
    ))



(define (unify loc)
   (unify-helper (loi loc empty))
  )

(define (unify-helper listIn)
  (if (empty? (loi-loc listIn)) ;if list of constraints is empty
      (loi-los listIn) ;return list of subs
      ;else
      (local ([define const (first (loi-loc listIn))]
              [define shipping (loi (rest (loi-loc listIn)) (loi-los listIn))])
      (cond
        [(equal? (eqc-lhs const) (eqc-rhs const))
         ;do nothing 
         (display "do nothing")
          ]
        [(t-var? (eqc-lhs const))
         ;(unify-helper (helperFun (shipping)))
         (display "replace all lhs with rhs in shipping (help function needed")
         ]
        [(t-var? (eqc-rhs const))
         ;(unify-helper (helperFun (shipping)))
         (display "replace all rhs with lhs in shipping")         
         ]
        [(and (t-fun? (eqc-rhs const))
              (t-fun? (eqc-lhs const)))
         (unify-helper (loi (append (list (eqc (t-fun-arg (eqc-rhs const))
                                               (t-fun-arg (eqc-lhs const)))
                                          (eqc (t-fun-result (eqc-rhs const))
                                               (t-fun-result (eqc-lhs const))))
                                    (rest (loi-loc listIn)))
                            (loi-los listIn)))
                                          
            ]
        [else
         (error "type mismatch")
         ]
      
      )))
  )


(define (infer-type e)
  0)


;***************************************************************************************
;********************     Alpha-vary tests     *****************************************
;***************************************************************************************
;********* Num *****************************
(test (alpha-vary (parse 4)) (num 4))
;********* ID *****************************
(test (alpha-vary-rec (parse 'x) (anEnv 'x 'x4 (mtEnv))) (id 'x4))
(test/exn (alpha-vary-rec (parse 'y) (anEnv 'x 'x4 (mtEnv))) "no binding")
;********* Bool *****************************
(test (alpha-vary (parse 'true)) (bool #t))
(test (alpha-vary (parse 'false)) (bool #f))
;********* bin-num-op *****************************
(test (alpha-vary (bin-num-op + (num 3) (num 4))) (bin-num-op + (num 3) (num 4)))
;********* iszero *****************************
;****(test (alpha-vary (parse '(tempty))) (tempty)) Do we need a tempty in the parser?
;********* bif *****************************
(test (alpha-vary-rec (parse '(bif true a 4)) (anEnv 'a 'x4 (mtEnv))) (bif (bool #t) (id 'x4) (num 4)))
;********* app *****************************
;see the function tests
;********* tempty *****************************

;********* tcons *****************************
(test (alpha-vary (parse '(tcons 4 5))) (tcons (num 4) (num 5)))
;********* tfirst *****************************
(test (alpha-vary (parse '(tfirst (tcons 4 5)))) (tfirst (tcons (num 4) (num 5))))
;********* trest *****************************
(test (alpha-vary (parse '(trest (tcons 4 5)))) (trest (tcons (num 4) (num 5))))
;********* isempty *****************************
(test (alpha-vary (parse '(istempty (tcons 4 5)))) (istempty (tcons (num 4) (num 5))))
;********* With *****************************
(alpha-vary (parse '(+ 3 4)))
(alpha-vary (parse '(+ (with x 4 x) (with x 5 x))))
(alpha-vary (parse '(with x 4 (with x 5 (+ x 9)))))
(alpha-vary (parse '(with x 4 x)))
(alpha-vary (parse '(with x (with x (with x 6 x) (+ x 9)) (+ x 5)))) ;show the correct position of x as opposed to rec-with
(alpha-vary (parse '(with x 4 (with x 5 (with x 7 x)))))
(alpha-vary (parse '(with x 4 (with x (+ x 1) (+ x 3)))))
(test/exn (alpha-vary (parse '(with x 4 y))) "no binding")
(test/exn (alpha-vary (parse '(with x 4 (+ y 5)))) "no binding")

;********* With rec *******************************
(alpha-vary (parse '(+ 3 4)))
(alpha-vary (parse '(+ (rec-with x 4 x) (rec-with x 5 x))))
(alpha-vary (parse '(rec-with x 4 (rec-with x 5 (+ x 9)))))
(alpha-vary (parse '(rec-with x 4 x)))
(alpha-vary (parse '(rec-with x 4 (rec-with x 5 x))))
(alpha-vary (parse '(rec-with x (rec-with x (rec-with x 6 x) x) x)))
(alpha-vary (parse '(rec-with x (rec-with x (rec-with x 6 x) (+ x 9)) (+ x 5))))
(alpha-vary (parse '(rec-with x 4 (rec-with x (+ x 1) (+ x 3)))))
(test/exn (alpha-vary (parse '(rec-with x 4 y))) "no binding")
(test/exn (alpha-vary (parse '(rec-with x 4 (+ y 5)))) "no binding")

;********** Fun *************************************
(alpha-vary (parse '(fun x (+ x 5))))
(alpha-vary (parse '(fun x (with y 5 (+ x y)))))
(alpha-vary (parse '(fun x (- (with x 5 (+ x x)) x)))) ;show shadowing correctly
(test/exn (alpha-vary (parse '(fun x (+ y 5)))) "no binding")





; type=?/mapping : hash hash Type Type -> Bool
; determines if types are equal modulo renaming
(define (type=?/mapping ht1 ht2 t1 t2)
  (define (teq? t1 t2)
    (type=?/mapping ht1 ht2 t1 t2))
  (cond
    [(and (t-num? t1) (t-num? t2)) true]
    [(and (t-bool? t1) (t-bool? t2)) true]
    [(and (t-list? t1) (t-list? t2))
     (teq? (t-list-elem t1) (t-list-elem t2))]
    [(and (t-fun? t1) (t-fun? t2))
     (and (teq? (t-fun-arg t1) (t-fun-arg t2))
          (teq? (t-fun-result t1) (t-fun-result t2)))]
    [(and (t-var? t1) (t-var? t2))
     (local ([define v1 ; the symbol that ht1 says that t1 maps to
               (hash-ref
                ht1 (t-var-v t1)
                (lambda ()
                  ; if t1 doesn't map to anything, it's the first
                  ; time we're seeing it, so map it to t2
                  (hash-set! ht1 (t-var-v t1) (t-var-v t2))
                  (t-var-v t2)))]
             [define v2
               (hash-ref
                ht2 (t-var-v t2)
                (lambda ()
                  (hash-set! ht2 (t-var-v t2) (t-var-v t1))
                  (t-var-v t1)))])
       ; we have to check both mappings, so that distinct variables
       ; are kept distinct. i.e. a -> b should not be isomorphic to
       ; c -> c under the one-way mapping a => c, b => c.
       (and (symbol=? (t-var-v t2) v1)
            (symbol=? (t-var-v t1) v2)))]
    [(and (Type? t1) (Type? t2)) false]
    [else (error 'type=? "either ~a or ~a is not a Type" t1 t2)]))
 
; type=? Type -> Type -> Bool
; signals an error if arguments are not variants of Type
(define ((type=? t1) t2)
  (or (type=?/mapping (make-hash) (make-hash) t1 t2)
      ; Unfortunately, test/pred simply prints false;
      ; this helps us see what t2 was.
      (error 'type=?
             "~s and ~a are not equal (modulo renaming)"
             t1 t2)))
 
(test/pred (t-var 'a)
           (type=? (t-var 'b)))
(test/pred (t-fun (t-var 'a) (t-var 'b))
           (type=? (t-fun (t-var (gensym)) (t-var (gensym)))))
(test/pred (t-fun (t-var 'a) (t-var 'b))
           (type=? (t-fun (t-var (gensym)) (t-var (gensym)))))
(test/pred (t-fun (t-var 'a) (t-var 'a)) ; fails
           (type=? (t-fun (t-var (gensym)) (t-var (gensym)))))
(test/pred (t-fun (t-var 'a) (t-var 'b)) ; fails
           (type=? (t-fun (t-var 'c) (t-var 'c))))
(test/exn ((type=? 34) 34) "not a Type")
 
; constraint-list=? : Constraint list -> Constraint list -> Bool
; signals an error if arguments are not variants of Constraint
(define ((constraint-list=? lc1) lc2)
  (define htlc1 (make-hash))
  (define htlc2 (make-hash))
  (or (andmap (lambda (c1 c2)
                (and
                 (type=?/mapping
                  htlc1 htlc2
                  (eqc-lhs c1) (eqc-lhs c2))
                 (type=?/mapping
                  htlc1 htlc2
                  (eqc-rhs c1) (eqc-rhs c2))))
              lc1 lc2)
      (error 'constraint-list=?
             "~s and ~a are not equal (modulo renaming)"
             lc1 lc2)))