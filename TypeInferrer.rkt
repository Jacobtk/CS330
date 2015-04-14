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
 
(define-type Constraint
  [eqc (lhs Type?) (rhs Type?)])


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
  0)


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
    (tempty () 0)
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
                    [define expr-c (generate-constraints expr-id expr)])
              (append
               (list (eqc (t-var e-id) 
                     ;constraint about what first will return
                     )
               expr-c)))
                     
    (trest (expr) 
           (local ([define expr-id (gensym)]
                   [define expr-c (generate-constraints expr-id expr)])
             (append
              (list (eqc (t-var expr-id) (t-list))
                    (eqc (t-var e-id) (t-list)))
              expr-c)))
    (istempty (expr) 
              (local ([define expr-id (gensym)]
                      [define expr-c (generate-constraints expr-id expr)])
                (append
                 (list (eqc (t-var e-id) (t-bool))
                       (eqc (t-var expr-id) (t-list)))
                 expr-c)))
    
    
    ))


(define (unify loc)
  0)


(define (infer-type e)
  0)








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