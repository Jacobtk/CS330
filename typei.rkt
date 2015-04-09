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

(define (generate-constraints e-id e)
  (type-case Expr e
    (num (n) (list (eqc (t-var e-id) (t-num))))
    (id (v) (list (eqc (t-var e-id) (t-var v))))
    ; ...
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
    (else (error "Constraint generation not finished yet."))
    ))

