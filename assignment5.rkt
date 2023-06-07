#lang typed/racket
(require typed/rackunit)

;; tstruct defn
(define-syntax tstruct
  (syntax-rules ()
    [(_ name fields)
     (struct name fields #:transparent)]))

;; Definition of abstract syntax for VVQS language
(define-type ExprC (U NumC AppC Leq0? IdC BinopC)) 
(tstruct NumC ([n : Real]))
(tstruct AppC ([funct : ExprC] [args : (Listof ExprC)]))
(tstruct IfC  ([do : ExprC] [this : ExprC] [that : ExprC]))
(tstruct IdC   ([id : Symbol]))
(tstruct BinopC   ([op : Symbol] [l : ExprC] [r : ExprC]))
(tstruct StringC ([s : String]))
(tstruct LamC ([param : (Listof Symbol)] [body : ExprC]))

;; binding struct:
(tstruct Binding ([name : IdC] [val : ExprC]))

;; setting up Environment:
(define-type Environment (Listof Binding))

;(define topLevelEnv (Environment (Binding '+ )))

;; defining Value, which is the output of our interpreter
(define-type Value (U RealV StringV CloV))
(tstruct RealV ([n : Real]))
(tstruct StringV ([s : String]))
(struct CloV ([arg : Symbol] [body : ExprC] [env : Environment]))

;; Find the BinopC b in the list of BinopCs
; Data: Symbol ->  (-> Real Real * Real)
(define (get-BinopC [b : Symbol]) : (-> Real Real * Real)
  (match b
    ['+ +]
    ['- -]
    ['/ /]
    ['* *]))

; get-BinopC tests:
(check-equal? (get-BinopC '+) +)
(check-equal? (get-BinopC '-) -)
(check-equal? (get-BinopC '/) /)
(check-equal? (get-BinopC '*) *)

;; Keywords that IdC cannot be
(define Ikeywords '(+ - * / def then else = where))

;; Predicate to determine if s is a legal IdC
; Data: Any -> Boolean
(: legal-sym? (Any -> Boolean : #:+ Symbol))
(define (legal-sym? s)
  (and (symbol? s)
       (not (member s Ikeywords))))

; legal-sym? tests:
(check-equal? (legal-sym? +) #f)
(check-equal? (legal-sym? 'a) #t)

;; Parser converts Concrete Syntax to Abstract Syntax
; Data: Sexp -> ExprC
(define (parse [sexp : Sexp]) : ExprC
   (match sexp
     [(? real?) (NumC sexp)]
     [(list a 'if b 'else c) (IfC (parse a) (parse b) (parse c))]
     [(list funct 'where {list (list sym ':= assign) ...}) (AppC (parse funct) (map parse assign))]
     [(? symbol? sym) (IdC sym)]
     [(? string? str) (StringC str)]
     [(list (? legal-sym? param) ... '=> body) (LamC (cast param (Listof Symbol)) (parse body))]
     [other (error 'parse "VVQS: Syntax error, given invalid term ~e" other)]))

; parse tests:
;(check-equal? (parse '{+ 5 4}) (BinopC '+ (NumC 5) (NumC 4)))
;(check-equal? (parse '{leq0? 1 then 1 else {- 1 1}})
              ;(Leq0? (NumC 1) (NumC 1) (BinopC '- (NumC 1) (NumC 1))))
(check-equal? (parse '{1 if 1 else 2})
              (IfC (NumC 1) (NumC 1) (NumC 2)))
(check-equal? (parse '{foo 1}) (AppC 'foo (list (NumC 1))))
(check-equal? (parse 'abc) (IdC 'abc))
;(check-equal? (parse '{foo2 1 2 3}) (AppC 'foo2 (list (NumC 1) (NumC 2) (NumC 3))))
(check-equal? (parse '{{+ z y} where {[z := {+ 9 14}] [y := 98]}}) (AppC ((IdC '+) (IdC 'z) (IdC 'y))))
;(check-equal? (parse '{{x} => {+ 1 x}}) (LamC (list 'x) (BinopC '+ (NumC 1) (IdC 'x))))
(check-equal? (parse '{{x} => {+ 1 x}}) (LamC (list 'x) ((IdC '+) (NumC 1) (IdC 'x))))
(check-equal? (parse "hi") (StringC "hi"))
(check-exn #px"VVQS: Syntax error, given invalid term '=" (λ () (parse '=)))
(check-exn #px"VVQS: Syntax error, given invalid term" (λ () (parse '(= 1)))) 
(check-exn #px"VVQS: Syntax error, given invalid term" (λ () (parse '(1 2 3))))
(check-exn #px"VVQS: Syntax error, given invalid term" (λ () (parse '(+ + 3))))

;; Find the function n in the list of fundefs
; Data: Symbol + Listof FundefC -> FundefC
#;(define (get-fundef [n : Symbol] [fds : (Listof FundefC)]) : FundefC
  (cond
    [(empty? fds)
     (error 'get-fundef "VVQS: BOOL reference to undefined function ~e" n)]
    [(cons? fds)
     (cond
       [(equal? n (FundefC-name (first fds))) (first fds)] 
       [else (get-fundef n (rest fds))])]))

; get-fundef tests:
;(define test-fds (list (FundefC 'addone  (list 'x) (BinopC '+ (IdC 'x) (NumC 1)))
                      ; (FundefC 'subone  (list 'x 'y) (BinopC '- (IdC 'x) (IdC 'y)))))
;(check-equal? (get-fundef 'addone test-fds)
              ;(FundefC 'addone  (list 'x) (BinopC '+ (IdC 'x) (NumC 1))))
#;(check-exn #px"VVQS: BOOL reference to undefined function 'addtwo"
           (λ () (get-fundef 'addtwo test-fds)))

; parse-prog tests:
;(check-equal? (parse-prog '()) '())
;(check-equal? (parse-prog '({def {addone x} = {+ x 1}}))
              ;(list (FundefC 'addone  (list 'x) (BinopC '+ (IdC 'x) (NumC 1)))))

;; Consumes a symbol and parameter and checks if they match; if they do, return interparg; else return #f
; Symbol + Symbol + Real -> (U Real Boolean)
(define (match-param? [s : Symbol] [param : Symbol] [interpArg : Real]) : (U Real Boolean)
  (if (equal? s param) interpArg #f))

; match-param? tests:
(check-equal? (match-param? 'x 'x 5) 5)
(check-equal? (match-param? 'x 'y 0.5) #f)

;; Consumes a list that contains Any (Booleans and/or Reals) and an ExprC;
;; If a Real exists in the list, returns the Real as a NumC; else, returns the ExprC
; (Listof Any) + ExprC -> ExprC
(define (find-ExprC [l : (Listof Any)] [body : ExprC]) : ExprC
  (match l
    ['() body]
    [(cons f r) (if (real? f) (NumC f) (find-ExprC r body))]))

; find-ExprC tests:
(check-equal? (find-ExprC '(#f) (IdC 'x)) (IdC 'x))
(check-equal? (find-ExprC '(4) (IdC 'x)) (NumC 4))
#;(check-equal? (find-ExprC '(#f 4.1 #f) (BinopC '+ (IdC 'x) (NumC 1))) (NumC 4.1))

;; Substitutes the interpreted argument(s) for the provided parameter(s) where they occur in the body
; Data: (List of Real) + (Listof Symbol) + ExprC -> ExprC
#;(define (subst [interpArg : (Listof Real)] [param : (Listof Symbol)] [body : ExprC]) : ExprC
  (match body
    [(NumC n) body]
    [(IdC s) (find-ExprC (map match-param? (build-list (length param) (lambda (x) s))
                              param
                              interpArg) body)] 
    [(AppC f a) (AppC f (map subst
                             (build-list (length a) (lambda (x) interpArg))
                             (build-list (length a) (lambda (x) param))
                             a))] 
    [(BinopC op l r) (BinopC op (subst interpArg param l)
                        (subst interpArg param r))]
    [(Leq0? a b c) (Leq0? (subst interpArg param a)
                        (subst interpArg param b) (subst interpArg param c))]))

; subst tests:
#;(check-equal? (subst (list 5) (list 'x) (BinopC '+ (IdC 'x) (NumC 4)))
              (BinopC '+ (NumC 5) (NumC 4)))
#;(check-equal? (subst (list 5) (list 'x) (BinopC '+ (IdC 'y) (NumC 4)))
              (BinopC '+ (IdC 'y) (NumC 4)))
#;(check-equal? (subst (list 0) (list 'a) (AppC 'add1 (list (IdC 'a))))
              (AppC 'add1 (list (NumC 0))))
#;(check-equal? (subst (list 0 1 2) (list 'a 'b 'c) (AppC 'add1 (list (IdC 'a))))
              (AppC 'add1 (list (NumC 0))))
#;(check-equal? (subst (list 0 1 2) (list 'a 'b 'c) (BinopC '+ (IdC 'b) (BinopC '+ (IdC 'a) (IdC 'c))))
              (BinopC '+ (NumC 1) (BinopC '+ (NumC 0) (NumC 2))))

;; Interpret an ExperC
; Data: ExprC + Listof FundefC -> Real
(define (interp [exp : ExprC] [fds : (Listof FundefC)] [env : Environment]) : Real
  (match exp
    [(NumC b) b]
    ;[(Leq0? a b c) (if (<= (interp a fds) 0) (interp b fds) (interp c fds))]
    #;[(BinopC op lexp rexp)(cond
                            [(and (equal? (interp rexp fds) 0) (equal? op '/))
                             (error 'get-fundef "VVQS: Divide by 0 error: ~e" exp)]
                            [else ((get-BinopC op) (interp lexp fds) (interp rexp fds))])]  
    
    [(AppC funName arg) ; 1 evaluate arguments
                        (define interpArg
                          (cast (map interp arg (build-list (length arg) (lambda (x) fds))) (Listof Real))) 
                        ; 2 lookup function body
                        (define fd (get-fundef funName fds)) 
                        ; 3 substitute the parameters for the argument
                        (if (not (equal? (length interpArg) (length (FundefC-param fd))))
                            (error 'interp "VVQS: Incorrect number of arguments: ~e" exp)
                            (let ((substFunBody (subst interpArg
                                                    (FundefC-param fd)
                                                    (FundefC-body fd))))
                              (interp substFunBody fds)))]
    [(IdC sym) (error 'interp "VVQS: Got unbound id ~e" sym)]))

; interp tests:
#;(check-equal? (interp (BinopC '+ (NumC 5) (NumC 4)) '()) 9)
#;(check-equal? (interp (BinopC '* (NumC 5) (NumC 4)) '()) 20)
#;(check-equal? (interp (BinopC '- (NumC 5) (NumC 4)) '()) 1)
#;(check-equal? (interp (Leq0? (NumC 1) (NumC 1) (BinopC '- (NumC 1) (NumC 1))) '()) 0)
#;(check-equal? (interp (Leq0? (NumC 0) (NumC 1) (BinopC '- (NumC 1) (NumC 1))) '()) 1)
(check-equal? (interp (AppC 'addone (list (NumC 2))) test-fds) 3)
(check-equal? (interp (AppC 'subone (list (NumC 2) (NumC 0.5))) test-fds) 1.5)
(check-exn  #px"VVQS: Incorrect number of arguments"
            (λ () (interp (AppC 'addone (list (NumC 2) (NumC 1))) test-fds)))
(check-exn #px"VVQS: Got unbound id 'a" (λ () (interp (IdC 'a) '())))
#;(check-exn #px"VVQS: Divide by 0 error"
           (λ () (interp (BinopC '/ (NumC 5) (BinopC '+ (NumC 0) (NumC 0))) test-fds)))

;; Parses and interprets main given function definitions
; Data: Listof FundefC -> Real
(define (interp-fns [fds : (Listof FundefC)]) : Real
  (interp (parse '{main}) fds))

;; Parses, then interprets the program
; Sexp -> Real
(: top-interp (Sexp -> Real))
(define (top-interp fun-sexps)
  (interp-fns (parse-prog fun-sexps)))
 
; top-interp tests:
(check-equal? (top-interp (quote ((def (main) = (leq0? (* 3 1) then 3 else (+ 2 9)))))) 11)
(check-exn  #px"VVQS: Incorrect number of arguments"
            (λ () (top-interp '((def (f x) = (+ x 2)) (def (main) = (f 3 4 5))))))


