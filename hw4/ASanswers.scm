;; HW4 - part 1 and optimal BST
;;; Answer part 1 here.
(define make-account-lambda
  (lambda (balance)
    (define withdraw
      (lambda (amount)
        (if (>= balance amount)
            (begin (set! balance (- balance amount))
                   balance)
            "Insufficient Funds")))
    (define deposit
      (lambda (amount)
        (set! balance (+ balance amount))
        balance))
    (lambda (m)
      (cond ((eq? m 'withdraw) withdraw)
            ((eq? m 'deposit) deposit)
            (else (display "unknow request"))))))

(define make-account-inline
  (lambda(balance)
      (lambda (m)
        (cond ((eq? m 'withdraw)
               (lambda (amount)
                 (if (>= balance amount)
                     (begin (set! balance (- balance amount))
                            balance)
                     "insufficient funds")))  
              ((eq? m 'deposit)
               (lambda (amount)
                 (set! balance (+ balance amount))
                 balance))
              (else (display "unknow request"))))))

(define make-account-inline-factored
  (lambda(balance)
      (lambda (m)
        (lambda (amount)
          (cond((eq? m' withdraw)
                (if (>= balance amount)
                    (begin (set! balance (- balance amount))
                           balance)
                    "Insufficient funds"))
               ((eq? m' deposit)
                (set! balance (+ balance amount))
                balance)
               (else (display "unknown request")))))))

(define make-pw-account
  (lambda (balance psswd)
      (define withdraw
        (lambda (amount)
          (if (>= balance amount)
              (begin (set! balance (- balance amount))
                     balance)
              "Insufficient Funds")))
      (define deposit
        (lambda (amount)
          (set! balance (+ balance amount))
          balance))
      (lambda (n m)
        (if (equal? n psswd)
            (cond ((eq? m 'withdraw) withdraw)
                  ((eq? m 'deposit) deposit)
                  (else (display "Unknow Request")))
        (lambda (x) "Incorrect password")))))

(define make-monitored
  (lambda (f)
    (let ((count 0))
      (define mf
        (lambda (n)
          (cond ((equal? n 'how-many-calls?) count)
                ((equal? n 'reset-count)
                 (set! count 0))
                (else (set! count (+ count 1))
                      (f n)))))
      mf)))




;; Part 2 starts here!
(define (read-file)
    (let ((expr (read)))
      (if (eof-object? expr)
          '()
          (cons expr (read-file)))))

;(define data (with-input-from-file "keys.dat" read-file))

(define (get-left-subtree lst root)
  (cond((equal? lst '()) '())
       ((equal? (list-ref lst 0) root) '())
       (else(cons (car lst)
                  (get-left-subtree (cdr lst) root)))))


(define (get-right-subtree lst root)
  (cond((equal? lst '()) '())
       ((= (caar lst) (car root))
        (cdr lst))
       (else(get-right-subtree (cdr lst) root))))

(define (sum-tree lst)
  (if (null? lst)
      0
      (+ (car(cdar lst)) (sum-tree (cdr lst)))))

(define (min-cost-naive lst)
  (let((min 1000000))
    (define (cost-iter lst i j min)
      (cond ((equal? lst '())0)
        ((equal? (length lst)1) ;use let* to bind sequentially
         (car(cdr(car lst))))
        ((equal? i j) min)
        (else (let((root (list-ref lst i)))
                (let((tree-cost(+ (sum-tree lst)
                              (cost-iter (get-left-subtree lst root) 0 (length lst) min)
                              (cost-iter (get-right-subtree lst root) 0 (length lst) min))))
                (cond ((> min tree-cost)
                       (set! min tree-cost)
                       (cost-iter lst (+ i 1) (length lst) min))
                      (else(cost-iter lst (+ 1 i) (length lst) min))))))))
    (cost-iter lst 0 (length lst) min)))

(define new-withdraw
  (let((balance 100))
    (lambda (amount)
      (if (>= balance amount)
          (begin (set! balance (- balance amount))
                 balance)
          "Insufficient Funds."))))

(#%require (only racket/base current-milliseconds))
(define (runtime) (current-milliseconds))
(define (timed f . args)
  (let ((init (runtime)))
    (let ((v (apply f args)))
      (display (list 'time: (- (runtime) init)))
      (newline)
      v)))
           





    


;; read-file produces a list whose elements are the expressions in the file.
  