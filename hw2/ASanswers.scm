(define (is-list? lst)
  (cond ((pair? lst) 
        (if (equal? (cdr lst) '())
            #t
            (is-list? (cdr lst))))
        ((equal? lst '()) #t)
        (else #f)))
         
(define (my-reverse lists)
  (if (null? lists)
      '()
      (append (my-reverse (cdr lists)) (list(car lists)))))

(define (same-parity . y)
  (if (odd? (car y))
      (filter odd? y)
      (filter even? y)))

(define (filter predicate sequence)
  (cond ((null? sequence) '())
       ((predicate (car sequence))
         (cons (car sequence)
               (filter predicate (cdr sequence))))
        (else (filter predicate (cdr sequence))) ))

(define (square-list items)
  (if (null? items)
     '()
      (cons  (* (car items)(car items))
         (square-list(cdr items)))))

(define (my-for-each procedure items)
  (if (not (null? items))
      (begin
        (procedure (car items))
        (my-for-each procedure (cdr items)))))

;(my-for-each odd? (list 1 2 3 4))

(define (every? pred seq)
  (cond ((null? seq) #t)
        ((pair? seq)
         (and(every? pred (car seq))
             (every? pred (cdr seq))))
        (else #f)))


;8b. when the list is empty the procedure needs to return true since
;this is the base case for the function. If every number in the list
;satified the pred and we did not have a base case the function would
;be forever looping since there is no basecase and the empty list
;return true does exactly that. 

(define (element-of-set? x set)
  (cond ((null? set) #f)
        ((equal? x (car set)) #t)
        (else (element-of-set? x (cdr set)))))

(define (adjoin x set)
  (if (element-of-set? x set)
      set
      (cons x set)))

(define (unordered-union-set set1 set2)
  (cond ((null? set1) set2)
        ((null? set2) set1)
        ((not(element-of-set? (car set1) set2))
         (adjoin (car set1) (unordered-union-set (cdr set1) set2)))
        (else (unordered-union-set (cdr set1) set2))))

;(unordered-union-set '(1 2 3) '(4 5))

(define (ordered-union-set set1 set2)
  (cond ((null? set1) set2)
        ((null? set2) set1)
        ((not(element-of-set? (car set1) set2))
         (adjoin (car set1) (ordered-union-set (cdr set1) set2)))
        (else (ordered-union-set (cdr set1) set2))))

(define (remove-val x lst)
  (cond ((null? lst) '())
        ((not(element-of-set? x lst)) lst)
        ((not(equal? x (car lst)))
         (cons (car lst)
               (remove-val x (cdr lst))))
        (else (remove-val x (cdr lst)))))

;(remove-val 3 '(1 2 3 3 6 3 7))


                          
   
                                  


         
        
       


