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
    (fun (arg-id body) 
         (local ([define arg-id-id (gensym)]
                 [define body-id (gensym)]
                 ;[define arg-c (generate-constraints arg-id-id arg-id)]
                 [define body-c (generate-constraints body-id body)])
           (append
            (list (eqc (t-var e-id) (t-fun (t-var arg-id-id) (t-var body-id)))
                  (eqc (t-var arg-id-id) (t-var arg-id)))
            ;arg-c
            body-c)))
    (app (fun-expr arg-expr) 
         (local ([define fun-id (gensym)]
                 [define arg-id (gensym)]
                 [define fun-c (generate-constraints fun-id fun-expr)]
                 [define arg-c (generate-constraints arg-id arg-expr)])
           (append
            (list (eqc (t-var fun-id) (t-fun (t-var arg-id) (t-var e-id))))
            fun-c
            arg-c)))
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

;(define (findMyType var typeIn)
;  (cond
;    [(t-list? typeIn) 
;     (if (equal? (t-var-v (t-list-elem typeIn)) var)
;         (t-list (t-var var)))]
;     
;    [(t-num? typeIn) typeIn]
;    [(t-bool? typeIn) typeIn]))

(define (findAndReplace lookFor replaceWith typeIn)
  (cond
    [(t-var? typeIn)
     (if (equal? (t-var-v typeIn) lookFor)
         (t-var replaceWith)
         typeIn)]
    [(t-list? typeIn)
     (if (equal? (t-list-elem typeIn) lookFor)
         (t-list replaceWith)
         typeIn)]
    [(t-fun? typeIn)
     (t-fun (findAndReplace lookFor replaceWith (t-fun-arg typeIn)) 
            (findAndReplace lookFor replaceWith (t-fun-result typeIn)))]
    [#t
     typeIn] ;everything else just return itself
      
  ))

;(define-type Type
;  [t-num]
;  [t-bool]
;  [t-list (elem Type?)]
;  [t-fun (arg Type?) (result Type?)]
;  [t-var (v symbol?)])

(define (replaceHelper-Stack lookFor replaceWith list)
  (if (empty? list) list
      (cons (eqc (findAndReplace lookFor replaceWith (eqc-lhs (first list))) 
                 (findAndReplace lookFor replaceWith (eqc-rhs (first list)))) 
            (replaceHelper-Stack lookFor replaceWith (rest list)))
  ))

(define (replaceHelper-Sub lookFor replaceWith list)
  (if (empty? list) list
      (cons (eqc (eqc-lhs (first list)) 
                 (findAndReplace lookFor replaceWith (eqc-rhs (first list)))) 
            (replaceHelper-Sub lookFor replaceWith (rest list)))
  ))

(define (replaceHelper lookFor replaceWith listsO)
  (if (empty? (loi-loc listsO)) listsO
      
              ;make replacements in stack and sub
             (loi (replaceHelper-Stack lookFor replaceWith (loi-loc listsO)) 
                  (replaceHelper-Sub lookFor replaceWith (loi-los listsO)))
  
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
         (append (unify-helper (replaceHelper (eqc-lhs const) (eqc-rhs const) shipping)) (list const))
         ;(display "replace all lhs with rhs in shipping (help function needed")
         ]
        [(t-var? (eqc-rhs const))
         (append (unify-helper (replaceHelper (eqc-rhs const) (eqc-lhs const) shipping)) (list const))
         ;(display "replace all rhs with lhs in shipping")         
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
  (local ([define root-id (gensym)]
          [define final-c (unify (generate-constraints root-id (alpha-vary e)))])
    (eqc-rhs (first (filter (lambda (x)
                              (symbol=? root-id
                                        (t-var-v (eqc-lhs x))))
                            final-c)))
    ))


;*************************************************************************************
;*********************    Infer-type tests    ****************************************
;*************************************************************************************

(test (infer-type (parse '5)) (t-num))
(test (infer-type (parse 'true)) (t-bool))
(test (infer-type (parse '(tcons 5 1))) (t-list (t-num)))
(test (infer-type (parse '(bif true 5 1))) (t-num))
(test (infer-type (parse '(iszero 0))) (t-bool))
(test (infer-type (parse '(+ 5 1))) (t-num))
(test (infer-type (parse '(with x 5 x))) (t-num))
(test (infer-type (parse '(rec-with x 5 x))) (t-num))
(test (infer-type (parse '(fun x (+ x 5)))) (t-num))
(test (infer-type (parse '(fun x (iszero (tcons 5 1))))) (t-bool))
(test (infer-type (parse '(istempty (tcons 4 4)))) (t-bool))
(test (infer-type (parse '(trest (tcons 4 4)))) (t-list (t-num)))
(test (infer-type (parse '(tfirst (tcons true false)))) (t-bool))
(test (infer-type (parse '(tfirst (tcons 1 2)))) (t-num))

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
(test (alpha-vary (parse 'tempty)) (tempty))
;********* bif *****************************
(test (alpha-vary-rec (parse '(bif true a 4)) (anEnv 'a 'x4 (mtEnv))) (bif (bool #t) (id 'x4) (num 4)))
;********* app *****************************
;see the function tests
;********* tempty *****************************
(test (alpha-vary (parse 'tempty)) (tempty))
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


;TESTS FOR CONSTRAINTS
;num
(test (generate-constraints 'root (parse 4)) (list (eqc (t-var 'root) (t-num))))
;bool
(test (generate-constraints 'root (parse 'true)) (list (eqc (t-var 'root) (t-bool))))
;id
(test (generate-constraints 'root (parse 'x)) (list (eqc (t-var 'root) (t-var 'x))))
;bin-num-op
(define binConstraints (generate-constraints 'root (parse '(+ 4 5))))
(test (length binConstraints) 5)
(test (first binConstraints) (eqc (t-var 'root) (t-num)))
;more tests??
;iszero
(define iszeroConstraints (generate-constraints 'root (parse '(iszero 0))))
(test (length iszeroConstraints) 3)
(test (first iszeroConstraints) (eqc (t-var 'root) (t-bool)))
;bif
(define bifConstraints (generate-constraints 'root (parse '(bif true 2 3))))
(test (length bifConstraints) 6)
;with
;rec-with
;fun
(define funConstraints (generate-constraints 'root (parse '(fun x (+ x 5)))))
(test (length funConstraints) 7)
;app
(define appConstraints (generate-constraints 'root (parse '((fun x (+ x 5)) 3))))
(test (length appConstraints) 9)
;tempty
(define temptyConstraints (generate-constraints 'root (parse 'tempty)))
(test (length temptyConstraints) 1)
(test (eqc-lhs (first temptyConstraints)) (t-var 'root))
(test (t-list? (eqc-rhs (first temptyConstraints))) true)
;tcons
(define tconsConstraints (generate-constraints 'root (parse '(tcons 4 tempty))))
(test (length tconsConstraints) 4)
;tfirst
(define tfirstConstraints (generate-constraints 'root (parse '(tfirst tempty))))
(test (length tfirstConstraints) 3)
;trest;
(define trestConstraints (generate-constraints 'root (parse '(trest tempty))))
(test (length trestConstraints) 3)
;istempty
(define istemptyConstraints (generate-constraints 'root (parse '(istempty tempty))))
(test (length istemptyConstraints) 3)
(test (first istemptyConstraints) (eqc (t-var 'root) (t-bool)))



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