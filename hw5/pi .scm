 ;;; file: pi.scm
;;;
;;; This should be your second part of HW5.  All
;;; these definitions are from the textbook except cons-stream.

;;; cons-stream is defined (by a macro, as a special form). 

(define-syntax cons-stream
  (syntax-rules ()
    ((_ a b) (cons a (delay b)))))

(define stream-car car)
(define (stream-cdr stream) (force (cdr stream)))
(define (stream-null? x) (null? x))
(define the-empty-stream '())

(define (stream-ref stream i)
  (if(= i 0)
     (stream-car stream)
     (stream-ref (stream-cdr stream) (- i 1))))

(define (display-line x)
  (display x)
  (newline))

(define (stream-foreach f x)
  (if (stream-null? x)
      'done
      (begin (f (stream-car x))
             (stream-foreach f (stream-cdr x)))))

(define (stream-filter pred stream)
  (cond ((stream-null? stream) the-empty-stream)
        ((pred (stream-car stream))
         (cons-stream (stream-car stream)
                      (stream-filter pred (stream-cdr stream))))
        (else (stream-filter pred (stream-cdr stream)))))

(define (stream-map proc . argstreams)
 (if (stream-null? (car argstreams))
     the-empty-stream
     (cons-stream
       (apply proc (map stream-car argstreams))
       (apply stream-map
              (cons proc (map stream-cdr argstreams))))))

(define (display-n stream n)
  (define (display-n-iter i)
    (cond((= 1 n) (display (stream-ref stream 0)))
         ((= 0 n) 'pass)
         ((equal? (stream-ref stream i) '()) 'end)
         ((= i (- n 1)) (display (stream-ref stream (- n 1))))
         (else (display-line (stream-ref stream i))
               (display-n-iter (+ i 1)))))
  (display-n-iter 0))


;number to list of digits
(define (number->list-of-digits num)
  (let*((str (number->string num)))
    (string->list str)))

(define (chars->number character)
  (cond((number? character) character)
       ((char? character)
        (- (char->integer character) 48))))
    
;list of digits to number
(define (list-of-digits->number lst)
  (let*((str (list->string lst)))
    (string->number str)))


;takes a list converts to a stream (could help)
(define (lst->to->stream lst)
  (define (lst->stream-iter lst i)
    (if(equal? (cdr lst) '())
       (cons (chars->number(car lst)) (delay '()))
       (cons (chars->number(car lst)) (delay (lst->stream-iter (cdr lst) (+ i 1))))))
  (lst->stream-iter lst 0))

(define (power lst)
  (if (= (length lst) 3)
      100
      1000))

(define (prepend-zero lst1 lst2)
  (cond((equal? lst1 '()) '())
       ((equal? lst2 '()) lst1)
       ((> (length lst1) (length lst2))
        lst1)
        (else (prepend-zero (cons #\0 (append lst1))
                      lst2))))
    
(define (add-zeros lst1 lst2)
  (cond((> (length lst1) (length lst2)) lst1)
       ((< (length lst1) (length lst2))
        (add-zeros (cons #\0 (append lst1)) lst2))
       (else(add-zeros(cons #\0 (append lst1)) lst2))))
    
(define (mult-stream m stream)
  (define (consume-iter a stream strm a-list)
    (cond((stream-null? strm) (lst->to->stream a-list))
         ((stream-null? stream) (lst->to->stream a-list))
         ((let*((num (+ (* a 10)
                (* m (stream-car stream))))
                (old-a-list a-list)
                (a-list(prepend-zero (number->list-of-digits num) old-a-list))
                (pow (expt 10 (- (length a-list) 1)))
                (check (modulo num pow)))
                ;(newline)(display "num:")(display num)(newline)(display "pow:")(display pow)
                ;(newline)(display "m * stream-car: ") (display m)(display " x ")(display (stream-car stream)) (newline)
                ;(display "alist: ")(display a-list)(newline)(display "check:")(display check)
                ;(newline) (display "old a-list: ") (display old-a-list)
                ;(newline)(display "pow:")(display pow)(newline)(newline)
           (cond((and (>= (length a-list) 1)
                      (< (+ m check) pow))
                 (cons (chars->number (car a-list)) (delay(consume-iter (modulo num pow) (stream-cdr stream) (stream-cdr strm)
                                            (cdr a-list)))))
                (else (consume-iter num (stream-cdr stream) strm a-list)))))))
  (if(not (list? stream))
     (consume-iter 0 stream stream '())
     (consume-iter 0 (lst->to->stream stream) (lst->to->stream stream) '())))

(define matrix list)
(define first car)
(define second cadr)
(define third caddr)
(define fourth cadddr)

(define (add-matrix m1 m2)
  (cond((equal? m1 '()) '())
       ((equal? m2 '()) '())
       (else (cons (+ (car m1)
                      (car m2)) (add-matrix (cdr m1)
                                            (cdr m2))))))
(define (compose m1 m2)
  (matrix (+ (* (first m1) (first m2))
             (* (second m1) (third m2)))
          (+ (* (first m1) (second m2))
             (* (second m1) (fourth m2)))
          (+ (* (third m1) (first m2))
             (* (fourth m1) (third m2)))
          (+ (* (third m1) (second m2))
             (* (fourth m1) (fourth m2)))))


(define ones (cons (matrix 1 4 0 2) (delay ones)))
(define input (cons-stream (matrix 1 6 0 3) (add-stream input ones)))

(define (add-stream s1 s2)
  (stream-map add-matrix s1 s2))

(define (pi)
  (define (pi-iter stream a)
    (cond((stream-null? stream) '())
         ((let*((product1 (quotient (+ (* (first a) 3) (second a))
                                    (+ (* (third a) 3) (fourth a))))
                (product2 (quotient (+ (* (first a) 4) (second a))
                                    (+ (* (third a) 4) (fourth a)))))
            ;(display "product1: ") (display product1) (newline)
            ;(display "product2: ") (display product2) (newline)
            ;(display "stream-car: ") (display (stream-car stream))
            ;(display "a: ") (display a) (newline)
            (cond((= product1 product2)
                  (cons-stream product1 (pi-iter stream
                                                 (compose (matrix 10 (* -10 product1)
                                                                  0 1) a ))))
                 (else (pi-iter (stream-cdr stream)
                                (compose a (stream-car stream) ))))))))
  (pi-iter (stream-cdr input) (stream-car input)))
                                       
                                    
                
          


;(define lst '(9 8 7 4 3 6 9 1 7))
;(define new-list (cons 0 (append lst)))
;(define ones (cons 1 (delay ones)))
(define test (cons 9 (delay (cons 8 (delay (cons 7 (delay (cons 4 (delay (cons 3 (delay (cons 6 (delay (cons 9 (delay (cons 1 (delay (cons 7 (delay '())))))))))))))))))))
;(define integers (cons-stream 1 (add-streams ones integers)))

;(define st (cons 2 (delay '())))
;(define new (cons 2 (delay (cons 0 (delay '())))))