(define-syntax cons-stream
  (syntax-rules ()
    ((_ a b ) (cons a (delay b)))))

(define (stream-car stream) (car stream))
(define (stream-cadr stream) (stream-car(stream-cdr stream)))
(define (stream-cdr stream) (force(cdr stream)))
(define the-empty-stream '())
(define (stream-null? x) (null? x) )

(define (display-line x)
  (display x)
  (newline))

;stream for each
(define (stream-for-each proc s)
  (if (stream-null? s)
      'done
      (begin (proc (stream-car s))
             (stream-for-each proc (stream-cdr s)))))

(define (stream-ref stream i)
  (if(= i 0)
     (stream-car stream)
     (stream-ref (stream-cdr stream) (- i 1))))

;display-n homework problem 1
(define (display-n stream n)
  (define (display-n-iter i)
    (cond((= 1 n) (display (stream-ref stream 0)))
         ((= 0 n) 'pass)
         ((equal? (stream-ref stream i) '()) 'end)
         ((= i (- n 1)) (display (stream-ref stream (- n 1))))
         (else (display-line (stream-ref stream i))
               (display-n-iter (+ i 1)))))
  (display-n-iter 0))


(define (stream-filter pred stream)
  (cond ((stream-null? stream) the-empty-stream)
        ((pred (stream-car stream))
         (cons-stream (stream-car stream)
                       (stream-filter pred
                                      (stream-cdr stream))))
        (else (stream-filter pred (stream-cdr stream)))))


(define (stream-enumerate-interval low high)
  (if(> low high)
     the-empty-stream
     (cons-stream low
           (stream-enumerate-interval (+ low 1) high)))) 

(define (isSeven? num)
  (if(= 0 (modulo num 7))
     #t
     #f))

(define (my-apply proc lst)
  (define (my-apply-iter acc lst)
    (newline) (display "this is accum ") (display acc)
         (cond ((equal? lst '()) acc)
          (else (my-apply-iter (proc acc (car lst))
                               (cdr lst)))))
  (my-apply-iter (proc(car lst)) (cdr lst)))

(define (stream-map proc . argstreams)
 (if (stream-null? (car argstreams))
     the-empty-stream
     (cons-stream
       (apply proc (map stream-car argstreams))
       (apply stream-map
              (cons proc (map stream-cdr argstreams))))))


(define (add-streams s1 s2)
  (stream-map + s1 s2))

(define ones (cons-stream 1 ones))
(define integers (cons-stream 1 (add-streams ones integers)))

(define (not-div235-fn num)
  (cond((= (modulo num 2) 0) #f)
       ((= (modulo num 3) 0) #f)
       ((= (modulo num 5) 0) #f)
       (else #t)))


(define (fibgen a b)
  (cons-stream a (fibgen b (+ a b))))

(define (sieve stream)
  (cons-stream
   (stream-car stream)
   (sieve (stream-filter
           (lambda (x)
             (not (divisible? x (stream-car stream))))
           (stream-cdr stream)))))

(define (divisible? x num)
  (if(equal? (modulo x num) 0)
     #t
     #f))

(define notdiv-235 (stream-filter not-div235-fn integers)) 




          

 
       
;(number->string 123)
;(string->list "123")
;(char->integer #\A)





#|
;> lst
;(9 8 7 4 3 6 9 1 7)
;(9 8 7 4 3 6 9 1 7)
;> (+ (* (car lst) 10) (cadr lst))
;98
;> (* (car lst) 87)
;783
;> (+ (* ((car lst) 87) 10))(* cadr lst 87)

;> (+ (*(*(car lst) 87) 10)(* (cadr lst) 87))
;8526
;> (define b (+ (*(*(car lst) 87) 10)(* (cadr lst) 87)))
;> ( + (* b 10) (caadr lst))
;> ( + (* b 10) (caddr lst))
;85267
;> (caddr lst)
;7
;> (* b 10)
;85260
;> ( + (* b 10) (* 87 (caddr lst)))
;85869
;> (* 87 987436917)
;85907011779
;>
|#