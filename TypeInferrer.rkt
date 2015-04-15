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


;given an expression will change the vars to be unique
;e (Expr?) -> Expr?
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



;generates a list of constraints
;e-id (symbol?) e (Expr?) -> (listof Constraint?)
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
            (list (eqc (t-var e-id) (t-var then-id))
                  (eqc (t-var test-id) (t-bool))
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
              (list (eqc (t-var e-id) (t-list (t-var list-type)))
                    (eqc (t-var expr-id) (t-list (t-var list-type))))
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



;typeVar : Type?
;lookFor : Type?
;replaceWith : Type?
(define (replaceType typeVar lookFor replaceWith)
  (type-case Type typeVar
    (t-num () typeVar)
    (t-bool () typeVar)
    (t-list (elem) 
            (t-list (replaceType elem lookFor replaceWith)))
    (t-fun (arg return) 
           (t-fun (replaceType arg lookFor replaceWith)
                  (replaceType return lookFor replaceWith)))           
    (t-var (sym) 
           (if (equal? lookFor typeVar)
               replaceWith
               typeVar))))
    
    

;this function looks through a list of constraints and replaces all instances of lookFor with replaceWith
;loc : listof Constraint?
;lookFor : Type?
;replaceWith : Type?
(define (findAndReplace loc lookFor replaceWith)
  (if (empty? loc)
      empty
      (local ([define constraint (first loc)])
        (append (list (eqc (replaceType (eqc-lhs constraint) lookFor replaceWith)
                           (replaceType (eqc-rhs constraint) lookFor replaceWith)))
                (findAndReplace (rest loc) lookFor replaceWith)))))

(define (unify-helper loc subs)
  (if (empty? loc)
      subs
      (local ([define constraint (first loc)])
        (cond [(equal? (eqc-lhs constraint) (eqc-rhs constraint))
               (unify-helper (rest loc) subs)] ;do nothing, but continue on checking other constraints
              [(t-var? (eqc-lhs constraint))
               (unify-helper (findAndReplace (rest loc)
                                             (eqc-lhs constraint)
                                             (eqc-rhs constraint))
                             (append (list constraint)
                                     (findAndReplace subs
                                                     (eqc-lhs constraint)
                                                     (eqc-rhs constraint))))]
              [(t-var? (eqc-rhs constraint))
               (unify-helper (findAndReplace (rest loc)
                                             (eqc-rhs constraint)
                                             (eqc-lhs constraint))
                             (append (list (eqc (eqc-rhs constraint) (eqc-lhs constraint)))
                                     (findAndReplace subs
                                                     (eqc-rhs constraint)
                                                     (eqc-lhs constraint))))]
              [(and (t-fun? (eqc-rhs constraint))
                    (t-fun? (eqc-lhs constraint)))
               (unify-helper (append (list (eqc (t-fun-arg (eqc-lhs constraint))
                                                (t-fun-arg (eqc-rhs constraint)))
                                           (eqc (t-fun-result (eqc-lhs constraint))
                                                (t-fun-result (eqc-rhs constraint))))
                                     (rest loc))
                             subs)]
              [(and (t-list? (eqc-lhs constraint))
                    (t-list? (eqc-rhs constraint)))
               (unify-helper (append (list (eqc (t-list-elem (eqc-lhs constraint))
                                                (t-list-elem (eqc-rhs constraint))))
                                     (rest loc))
                             subs)]
              [else
               (error 'unify "type mismatch")]))))
              
(define (unify loc)
  (unify-helper loc empty))

(define (findRootConstraint constraints root-id)
  (local ([define constraint (first constraints)]
          [define left (eqc-lhs constraint)]
          [define right (eqc-rhs constraint)])
    (if (and (t-var? left)
             (symbol=? (t-var-v left) root-id))
        right
        (if (and (t-var? right)
                 (symbol=? (t-var-v right) root-id))
            left
            (findRootConstraint (rest constraints) root-id)))))

;e (Expr?) -> (Type?)
  ;given an expresion will find the type produced by that expersion
  (define (infer-type e)
    (local ([define root-id (gensym)]
            [define final-c (unify (generate-constraints root-id (alpha-vary e)))])
      (findRootConstraint final-c root-id)))  
  
  ;*************************************************************************************
  ;*********************    Infer-type tests    ****************************************
  ;*************************************************************************************
  
  (test (infer-type (parse '5)) (t-num))
  (test (infer-type (parse 'true)) (t-bool))
  (test (infer-type (parse 'false)) (t-bool))
(test (t-list? (infer-type (parse 'tempty))) true)
;tcons
  (test (infer-type (parse '(tcons 5 tempty))) (t-list (t-num)))
(test/exn (infer-type (parse '(tcons false (tcons 4 tempty)))) "type mismatch")
(test/exn (infer-type (parse '(tcons true true))) "type mismatch")
(test (infer-type (parse '(tcons false (tcons true tempty)))) (t-list (t-bool)))
(test (infer-type (parse '(tcons (tcons 4 tempty) tempty))) (t-list (t-list (t-num))))
(test/exn (infer-type (parse '(tcons (tcons 4 tempty) (tcons (tcons true tempty) tempty)))) "type mismatch")
;tfirst
(test/exn (infer-type (parse '(tfirst false))) "type mismatch")
  (test/exn (infer-type (parse '(tfirst 0))) "type mismatch")
(test (infer-type (parse '(tfirst (tcons 4 tempty)))) (t-num))
(test (infer-type (parse '(tfirst (tcons true tempty)))) (t-bool))
(test (t-var? (infer-type (parse '(tfirst tempty)))) true)
;trest
(test/exn (infer-type (parse '(trest 0))) "type mismatch")
(test (t-list? (infer-type (parse '(trest tempty)))) true)
(test (infer-type (parse '(trest (tcons 4 tempty)))) (t-list (t-num)))
(test (infer-type (parse '(trest (tcons false (tcons true tempty))))) (t-list (t-num)))
;istempty
(test/exn (infer-type (parse '(istempty true))) "type mismatch")
(test (infer-type (parse '(istempty tempty))) (t-bool))
;bif
  (test (infer-type (parse '(bif true 5 1))) (t-num))
(test (infer-type (parse '(bif false false true))) (t-bool))
(test (infer-type (parse '(bif true tempty (tcons 4 tempty)))) (t-list (t-num)))
(test/exn (infer-type (parse '(bif 0 4 5))) "type mismatch")
(test/exn (infer-type (parse '(bif tempty 4 5))) "type mismatch")
(test/exn (infer-type (parse '(bif true 4 tempty))) "type mismatch")
;iszero
  (test (infer-type (parse '(iszero 0))) (t-bool))
  (test (infer-type (parse '(iszero (+ 5 (- 6 3))))) (t-bool))
(test/exn (infer-type (parse '(iszero tempty))) "type mismatch")
;bin-num-op
  (test (infer-type (parse '(+ 5 1))) (t-num))
  (test (infer-type (parse '(+ (- (- 2 0) (- 0 2)) (* (+ 1 2) (+ 3 4))))) (t-num))
(test/exn (infer-type (parse '(+ true 5))) "type mismatch")
(test/exn (infer-type (parse '(+ 5 true))) "type mismatch")
(test/exn (infer-type (parse '(- false 4))) "type mismatch")
(test/exn (infer-type (parse '(- 4 false))) "type mismatch")
(test/exn (infer-type (parse '(* tempty 3))) "type mismatch")
(test/exn (infer-type (parse '(* 3 tempty))) "type mismatch")
  ;(test (infer-type (parse '(with x 5 x))) (t-num))
  ;(test (infer-type (parse '(rec-with x 5 x))) (t-num))
;fun
  (test (infer-type (parse '(fun x (+ x 5)))) (t-fun (t-var 'x) (t-num)))
  (test (infer-type (parse '(fun x (iszero 0)))) (t-fun (t-var 'x) (t-bool)))
;app
  (test (infer-type (parse '((fun x (tcons x tempty)) 4))) (t-list (t-num)))
  
  


  
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
  (test (alpha-vary (parse '(tcons true true))) (tcons (bool #t) (bool #t)))
  ;********* tfirst *****************************
  (test (alpha-vary (parse '(tfirst (tcons 4 5)))) (tfirst (tcons (num 4) (num 5))))
  (test (alpha-vary (parse '(tfirst (tcons true true)))) (tfirst (tcons (bool #t) (bool #t))))
  ;********* trest *****************************
  (test (alpha-vary (parse '(trest (tcons 4 5)))) (trest (tcons (num 4) (num 5))))
  (test (alpha-vary (parse '(trest (tcons true true)))) (trest (tcons (bool #t) (bool #t))))
  ;********* isempty *****************************
  (test (alpha-vary (parse '(istempty (tcons 4 5)))) (istempty (tcons (num 4) (num 5))))
  ;********* With *****************************
  (alpha-vary (parse '(+ 3 4))) ;(bin-num-op #<procedure:+> (num 3) (num 4))
  (alpha-vary (parse '(+ (with x 4 x) (with x 5 x)))) ;(bin-num-op #<procedure:+> (with 'x283024 (num 4) (id 'x283024)) (with 'x283025 (num 5) (id 'x283025)))
  (alpha-vary (parse '(with x 4 (with x 5 (+ x 9))))) ;(with 'x283026 (num 4) (with 'x283027 (num 5) (bin-num-op #<procedure:+> (id 'x283027) (num 9))))
  (alpha-vary (parse '(with x 4 x))) ;(with 'x283028 (num 4) (id 'x283028))
;show the correct position of x as opposed to rec-with
  (alpha-vary (parse '(with x (with x (with x 6 x) (+ x 9)) (+ x 5)))) ;(with
; 'x283029
; (with 'x283030 (with 'x283031 (num 6) (id 'x283031)) (bin-num-op #<procedure:+> (id 'x283030) (num 9)))
; (bin-num-op #<procedure:+> (id 'x283029) (num 5)))

  (alpha-vary (parse '(with x 4 (with x 5 (with x 7 x))))) ;(with 'x283032 (num 4) (with 'x283033 (num 5) (with 'x283034 (num 7) (id 'x283034))))
  (alpha-vary (parse '(with x 4 (with x (+ x 1) (+ x 3))))) ;(with 'x283035 (num 4) (with 'x283036 (bin-num-op #<procedure:+> (id 'x283035) (num 1)) (bin-num-op #<procedure:+> (id 'x283036) (num 3))))
  (test/exn (alpha-vary (parse '(with x 4 y))) "no binding")
  (test/exn (alpha-vary (parse '(with x 4 (+ y 5)))) "no binding")
  
  ;********* With rec *******************************
  (alpha-vary (parse '(+ 3 4))) ;(bin-num-op #<procedure:+> (num 3) (num 4))
  (alpha-vary (parse '(+ (rec-with x 4 x) (rec-with x 5 x)))) ;(bin-num-op #<procedure:+> (rec-with 'x283039 (num 4) (id 'x283039)) (rec-with 'x283040 (num 5) (id 'x283040)))
  (alpha-vary (parse '(rec-with x 4 (rec-with x 5 (+ x 9))))) ;(rec-with 'x283041 (num 4) (rec-with 'x283042 (num 5) (bin-num-op #<procedure:+> (id 'x283042) (num 9))))
  (alpha-vary (parse '(rec-with x 4 x))) ;(rec-with 'x283043 (num 4) (id 'x283043))
  (alpha-vary (parse '(rec-with x 4 (rec-with x 5 x)))) ;(rec-with 'x283044 (num 4) (rec-with 'x283045 (num 5) (id 'x283045)))
  (alpha-vary (parse '(rec-with x (rec-with x (rec-with x 6 x) x) x))) ;(rec-with 'x283046 (rec-with 'x283047 (rec-with 'x283048 (num 6) (id 'x283048)) (id 'x283047)) (id 'x283046))
  (alpha-vary (parse '(rec-with x (rec-with x (rec-with x 6 x) (+ x 9)) (+ x 5)))) ;(rec-with
; 'x283049
; (rec-with 'x283050 (rec-with 'x283051 (num 6) (id 'x283051)) (bin-num-op #<procedure:+> (id 'x283050) (num 9)))
; (bin-num-op #<procedure:+> (id 'x283049) (num 5)))

  (alpha-vary (parse '(rec-with x 4 (rec-with x (+ x 1) (+ x 3))))) ;(rec-with 'x283052 (num 4) (rec-with 'x283053 (bin-num-op #<procedure:+> (id 'x283053) (num 1)) (bin-num-op #<procedure:+> (id 'x283053) (num 3))))
  (test/exn (alpha-vary (parse '(rec-with x 4 y))) "no binding")
  (test/exn (alpha-vary (parse '(rec-with x 4 (+ y 5)))) "no binding")
  
  ;********** Fun *************************************
  (alpha-vary (parse '(fun x (+ x 5)))) ;(fun 'x (bin-num-op #<procedure:+> (id 'x283056) (num 5)))
  (alpha-vary (parse '(fun x (with y 5 (+ x y))))) ;(fun 'x (with 'y283058 (num 5) (bin-num-op #<procedure:+> (id 'x283057) (id 'y283058))))
  ;show shadowing correctly
  (alpha-vary (parse '(fun x (- (with x 5 (+ x x)) x)))) ;(fun 'x (bin-num-op #<procedure:-> (with 'x283060 (num 5) (bin-num-op #<procedure:+> (id 'x283060) (id 'x283060))) (id 'x283059)))
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
;  
;  (test/pred (t-var 'a)
;             (type=? (t-var 'b)))
;  (test/pred (t-fun (t-var 'a) (t-var 'b))
;             (type=? (t-fun (t-var (gensym)) (t-var (gensym)))))
;  (test/pred (t-fun (t-var 'a) (t-var 'b))
;             (type=? (t-fun (t-var (gensym)) (t-var (gensym)))))
;  (test/pred (t-fun (t-var 'a) (t-var 'a)) ; fails
;             (type=? (t-fun (t-var (gensym)) (t-var (gensym)))))
;  (test/pred (t-fun (t-var 'a) (t-var 'b)) ; fails
;             (type=? (t-fun (t-var 'c) (t-var 'c))))
;  (test/exn ((type=? 34) 34) "not a Type")
  
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