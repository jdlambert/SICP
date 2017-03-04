;CHAPTER TWO: BUILDING ABSTRACTIONS WITH DATA

; SECTION 2.1: Introduction to Data Abstraction

;2.1 rational number datatype with sign checking

(define (make-rat n d)
  (let ((g (gcd n d)))
    (cond ((= 0 d) (error "Divide by zero!"))
          ((= 0 n) (cons 0 1))
          ((or (and (> n 0) (> d 0))  
               (and (< n 0) (< d 0)))
               (cons (/ (abs n) g) (/ (abs d) g)))
          (else (cons (/ (* -1 (abs n)) g) (/ (abs d) g))))))

;2.2 Line segments in a plane (layers of abstraction exercise)

; point level of abstraction, cons cdr and car

(define (make-point x y)
  (cons x y))

(define (x-point point)
  (car point))

(define (y-point point)
  (cdr point)) 

; segment level of abstraction, make-point x-point and y-point

(define (make-segment x1 y1 x2 y2)
  (cons (make-point x1 y1) (make-point x2 y2)))

(define (start-segment segment)
  (car segment))

(define (end-segment segment)
  (cdr segment))

(define (segment-length segment)
  (let ((start (start-segment segment))
        (end (end-segment segment)))
       (sqrt (+ (square (- (x-point start) (x-point end)))
                (square (- (y-point start) (y-point end)))))))

(define (average-x first-point second-point)
  (/ (+ (x-point first-point) (x-point second-point))))

(define (average-y first-point second-point)
  (/ (+ (y-point first-point) (y-point second-point))))

; one level of abstraction up, applications of segments

(define (midpoint-segment segment)
  (make-point (average-x (start-segment segment)
                         (end-segment segment))
              (average-y (start-segment segment)
                         (end-segment segment))))

(define (print-point p)
   (newline)
   (display "(")
   (display (x-point p))
   (display ",")
   (display (y-point p))
   (display ")"))

;2.3 Representation for rectangles in a plane, an exercise in barriers between levels of abstraction

; The first implementation uses two segments that meet at a point
(define (make-rectangle-segment first second) (cons first second))

(define (first-edge rectangle)
  (car rectangle))

(define (second-edge rectangle)
  (cdr rectangle))

; This second implementation uses the first implementation with different constructor parameters

(define (make-rectangle-point first second)
  (make-rectangle-segment (make-segment first
                                        (make-point (x-point first) (y-point second)))
                          (make-segment first
                                        (make-point (x-point second) (y-point first)))))

; Lastly, the procedures at a higher level of abstraction
(define (perimeter rectangle)
  (* 2 (+ (segment-length (first-edge rectangle)) (segment-length (second-edge-length rectangle)))))

(define (area rectangle)
  (* (segment-length (first-edge rectangle)) (segment-length (second-edge-length rectangle))))

;2.4 Procedural representation of pairs

(define (cons x y)
  (lambda (m) (m x y)))

(define (car z)
  (z (lambda (p q) p)))

;    (car (cons (x y))) y
; => (car (lambda (m) (m x y)))
; => ((lambda (m) (m x y)) (lambda (p q) p))
; => ((lambda (p q) p) (x y))
; => x

; The analogous definition for (cdr z) is

(define (cdr z)
  (z (lambda (p q) q)))

;2.5 Alternate representation of pairs of natural numbers (cons a b) as the product (2^a)(3^b)

(define (num-cons a b)
  (* (expt 2 a) (expt 3 b)))

(define (num-car p)
  (define (iter total return)
    (if (= 0 (remainder total 2))
        (iter (/ total 2) (+ return 1))
        return))
  (iter p 0))

(define (num-cdr p)
  (define (iter total return)
    (if (= 0 (remainder total 3))
        (iter (/ total 3) (+ return 1))
        return))
  (iter p 0))
      
;2.6 Church numerals

(define zero (lambda (f) (lambda (x) x))) 
; zero is a nested lambda expression that results in (lambda (x) x) regardless of input

(define (add-1 n)
   (lambda (f) (lambda (x) (f ((n f) x)))))

; (add-1 zero)
; (lambda (f) (lambda (x) (f ((zero f) x))))
; Since (zero f) evaluates to (lambda (x) x), ((zero f) x) evaluates to x
; (lambda (f) (lambda (x) (f x)))
(define one (lambda (f) (lambda (x) (f x))))
; one is a nested lambda expression that results in a single application of f on x

; Analogously,
; (add-1 one)
; (lambda (f) (lambda (x) (f ((one f) x))))
; ((one f) x) evaluates to (f x)
(define two (lambda (f) (lambda (x) (f (f x)))))
; two is a nested lambda expression that results in two applications of f on x

; zero is zero applications of f, one is one application, two is two applications
; the nth church numeral corresponds to n applications of f

; From the above observations, I conclude that addition of church numerals is just composition
(define church-plus compose)

; Also, as a little bonus, the church numerals can be generalized using a procedure from Chapter 1:
(define (church-n n) (lambda (f) (repeated f n)))

; INTERVAL ARITHMETIC

(define (add-interval  x y)
   (make-interval (+ (lower-bound x) (lower-bound y))
                  (+ (upper-bound x) (upper-bound y))))

(define (mul-interval x y)
   (let ((p1 (* (lower-bound x) (lower-bound y)))
         (p2 (* (lower-bound x) (upper-bound y)))
         (p3 (* (upper-bound x) (lower-bound y)))
         (p4 (* (upper-bound x) (upper-bound y))))
        (make-interval (min p1 p2 p3 p4)
                       (max p1 p2 p3 p4))))

(define (div-interval x y)
  (mul-interval x
                (make-interval (/ 1.0 (upper-bound y))
                               (/ 1.0 (lower-bound y)))))

; 2.7 Some late constructors and selectors

(define (make-interval a b)
   (cons a b))

(define (lower-bound interval)
   (car interval))
 
(define (upper-bound interval)
   (cdr interval))

; 2.8 Subtract interval, analogous to add interval

(define (sub-interval  x y)
   (make-interval (- (lower-bound x) (lower-bound y))
                  (- (upper-bound x) (upper-bound y))))

; 2.9 Width of an interval

(define (width interval)
  (/ (- (upper-bound interval) (lower-bound interval)) 2))

; For addition of interval (a, b) and (c, d), with widths (b-a)/2 and (d-c)/2 respectively
; The sum is (a + c, b + d), so the width of the sum is (b + d - a - c)/2, which is simply the sum of the two original widths
; For difference is (a - c, b - d), which has a width of (b - d - a + c)/2 = ((b-a) - (d-c))/2, the difference in the two original widths
; Multiplication and division are a bit trickier, since they involve conditionals, hidden in the implementations of min and max
; As a consequence of this, the width 

(define first (make-interval 1 2))
(width first) ; 1
(define second (make-interval -6 -5))
(width second) ; 1
(define thousand (make-interval 0 1000))
(width thousand) ; 500

(width (mul-interval first thousand))  ; 1000, the interval is (0, 2000)
(width (mul-interval second thousand)) ; 3000, the interval is (-6000, 0) 

(width (mul-interval thousand first))  ; 500, the interval remains (0, 1000)
(width (mul-interval thousand second)) ; 100, the interval is (-200, 0) 

; The widths of first and second are equal, but the widths of the products and quotients are different
; Thus, the width of a product or quotient interval is not a function of the widths of the factors or divisors

; 2.10 Division with an interval spanning zero

(define (div-interval x y)
  (if (spans-zero? y)
      (error "INVALID OPERATION: Division by a zero-spanning interval! div-interval")
      (mul-interval x
                    (make-interval (/ 1.0 (upper-bound y))
                                   (/ 1.0 (lower-bound y)))))

(define (spans-zero? x)
  (and (< (lower-bound x) 0) (> (upper-bound x) 0)))

; 2.11 Refactoring mul-interval

(define (pos? x)
  (and (> (lower-bound x) 0) (> (upper-bound x) 0)))

(define (neg? x)
  (and (< (lower-bound x) 0) (< (upper-bound x) 0)))

; The point of this refactored mul-interval is to rely on conditionals to split the multiplication up into 9 cases
; Most of the cases only involve two multiplications, as opposed to the original mul-interval's four
; However, if both intervals span zero, the four multiplications are still necessary
; Along with the conditionals, this makes the operation a bit slower for zero-spanning intervals
; But, if multiplication is more resource-expensive than the pos? and neg? predicates,
; this mul-interval should be much more performant

(define (mul-interval x y)
  (let ((x-lo (lower-bound x))
        (x-hi (upper-bound x))
        (y-lo (lower-bound y))
        (y-hi (upper-bound y)))
       (cond ((pos? x)
                (cond ((pos? y) (make-interval (* x-lo y-lo) (* x-hi y-hi)))
                      ((neg? y) (make-interval (* x-hi y-lo) (* x-lo y-hi)))
                      (else     (make-interval (* x-hi y-lo) (* x-hi y-hi)))))
             ((neg? x)
                (cond ((pos? y) (make-interval (* x-lo y-hi) (* x-hi y-lo)))
                      ((neg? y) (make-interval (* x-hi y-hi) (* x-lo y-lo)))
                      (else     (make-interval (* x-lo y-hi) (* x-lo y-lo)))))
             (else
                (cond ((pos? y) (make-interval (* x-lo y-hi) (* x-hi y-hi)))
                      ((neg? y) (make-interval (* x-hi y-lo) (* x-lo y-lo)))
                      (else    (orig-mul-interval x y)))))))

(define (orig-mul-interval x y)
   (let ((p1 (* (lower-bound x) (lower-bound y)))
         (p2 (* (lower-bound x) (upper-bound y)))
         (p3 (* (upper-bound x) (lower-bound y)))
         (p4 (* (upper-bound x) (upper-bound y))))
        (make-interval (min p1 p2 p3 p4)
                       (max p1 p2 p3 p4))))

; 2.12 Center-width and center-percent intervals

(define (make-center-width c w)
   (make-interval (- c w) (+ c w)))
(define (center i)
   (/ (+ (lower-bound i) (upper-bound i)) 2))
(define (width i)
   (/ (- (upper-bound i) (lower-bound i)) 2))

(define (make-center-percent c p)
   (make-center-width c (* c p 0.01)))
(define (percent i)
   (* (/ (width i) (center i)) 100))

; 2.13 A simple formula for the tolerance of a product, assuming small tolerances

; 2.14 Inconsistent results given two different representations of data

; 2.15 Choosing between the two different representations of data

; 2.15 Why can equivalent algebraic expressions lead to different answers?
;      Can an interval-arithmetic package without this shortcoming be designed or not? 

;representing sequences

(define (last-pair l)
   (if (null? (cdr l)) (car l) (last-pair (cdr l))))

(define (reversal l)
   (define (helper n)
       (if (= n (length l)) (cons (list-ref l 0) nil)
                                 (cons (list-ref l (- (length l) n)) (helper (+ n 1)))))
   (helper 1))
      
(define (same-parity x . l)
   (cond ((null? l) nil)
         ((= (remainder x 2) (remainder (car l) 2)) (cons (car l) (apply same-parity x (cdr l))))
         (else (apply same-parity x (cdr l)))))

(define (count-leaves x)
   (cond ((null? x) 0)
         ((not (pair? x)) 1)
         (else (+ (count-leaves (car x))
                  (count-leaves (cdr x))))))

(define (deep-reversal l)
   (define (helper n)
      (define (reversed-n)
         (- (length l) n 1))
      (define (cons-next)
         (cons (deep-reversal (list-ref l (reversed-n))) (helper (+ n 1))))
      (if (= n (length l)) nil (cons-next)))
   (if (pair? l) (helper 0) l))

(define (fringe t) 
   (cond ((not (list? t)) (list t))
         ((not (null? (cdr t))) (append (fringe (car t)) (fringe (cdr t))))
         (else (fringe (car t)))))

(define (make-mobile left right)
   (list left right))

(define (make-branch length structure)
   (list length structure))
 
(define (left-branch mobile)
   (car mobile))
(define (right-branch mobile)
   (car (cdr mobile)))
(define (branch-length branch)
   (car branch))
(define (branch-structure branch)
   (car (cdr branch)))
(define (has-mobile? branch)
   (list? (branch-structure branch)))
(define (branch-weight branch)
   (if (has-mobile? branch) (total-weight (branch-structure branch))
                            (branch-structure branch)))
(define (total-weight mobile)
   (+ (branch-weight (left-branch mobile)) (branch-weight (right-branch mobile))))

(define (branch-torque branch)
   (* (branch-length branch) (branch-weight branch)))

(define (balanced? mobile)
   (= (branch-torque (left-branch mobile)) (branch-torque (right-branch mobile))))

(define (tree-map proc tree)
   (cond ((null? tree) nil)
         ((not (pair? tree)) (proc tree))
         (else (cons (tree-map proc (car tree))
                     (tree-map proc (cdr tree))))))

(define (subsets s)
   (if (null? s)
       (list nil)
       (let ((rest (subsets (cdr s)))) 
         (append rest (map (lambda (x) (cons (car s) x)) rest)))))

;sequences as conventional interfaces

(define (fold-right op initial sequence)
   (if (null? sequence)
       initial
       (op (car sequence) (fold-right op initial (cdr sequence)))))

(define (fold-left op initial sequence)
   (define (iter result rest)
      (if (null? rest)  
         result
         (iter (op result (car rest))
               (cdr rest))))
   (iter initial sequence))

(define (enumerate-interval low high)
   (if (> low high)
       nil
       (cons low (enumerate-interval (+ low 1) high))))

(define (enumerate-tree tree)
   (cond ((null? tree) nil)
         ((not (pair? tree)) (list tree))
         (else (append (enumerate-tree (car tree))
                       (enumerate-tree (cdr tree))))))

(define (sum-odd-squares tree)
   (fold-right +
               0
               (map square
                    (filter odd?
                            (enumerate-tree tree)))))

(define (fold-right-reverse sequence)
   (fold-right (lambda (x y) (append y (list x))) nil sequence))
(define (fold-left-reverse sequence)
   (fold-left (lambda (x y) (append (list y) x )) nil sequence))

(define (flatmap proc seq)
   (fold-right append nil (map proc seq)))
 
(define (prime-sum? pair)
   (prime? (+ (car pair) (cadr pair))))

(define (make-pair-sum pair)
   (list (car pair) (cadr pair) (+ (car pair) (cadr pair))))

(define (prime-sum-pairs n)
   (map make-pair-sum
      (filter prime-sum?
         (unique-pairs n))))

(define (permutations s)
   (if (null? s)
      (list nil)
      (flatmap (lambda (x)
                  (map (lambda (p) (cons x p))
                       (permutations (remove x s))))
               s)))


(define (unique-triplets n)
   (flatmap
      (lambda (i)
         (flatmap 
            (lambda (j) 
               (map (lambda (k) 
                       (list i j k))
                    (enumerate-interval 1 (- j 1))))
            (enumerate-interval 1 (- i 1))))
      (enumerate-interval 1 n)))

(define (sum list)
   (fold-right + 0 list))

(define (triplets-with-sum n s)
   (filter
      (lambda (t) (= s (sum t)))
      (unique-triplets n)))

;8-queens problem

(define (enumerate-zeros n)
   (define (helper i)
      (if (= n i)
          nil
          (cons 0 (helper (+ i 1)))))
   (helper 0))
 
(define (enumerate-single k n)
   (define (helper i)
      (cond ((= n i) nil)
            ((= k i) (cons 1 (helper (+ i 1))))
            (else (cons 0 (helper (+ i 1))))))
   (helper 0))

(define (enumerate-zero-square-matrix n)
   (define (helper i)
      (if (= n i)
          nil
          (cons (enumerate-zeros n) (helper (+ i 1)))))
   (helper 0))

(define (index-of-one row)
   (define (index current i)
      (cond ((= (car current) 1) i)
            ((null? current) nil)
            (else (index (cdr current) (+ i 1)))))
    (index row 0))

;Queen's problem... pretty tough

(define (queens board-size)

   (define (adjoin-position new-row rest-of-queens)
      (if (empty? rest-of-queens) (list (enumerate-single new-row board-size))
                                  (append rest-of-queens (list (enumerate-single new-row board-size)))))

   (define (empty-board)
      (define (enum-empties n)
         (if (= board-size n) nil
                              (cons (list) (enum-empties (+ n 1)))))
      (enum-empties 0))

   
   (define (safe? k positions)
      (let ([tar (index-of-one (list-ref positions (- k 1)))])
         (define (row-good? row i)
            (let ([cur (index-of-one row)]
                  [diff (- k i 1)])
                  (not (or (= cur tar) (= cur (- tar diff)) (= cur (+ tar diff))))))
         (define (check-board board i)
            (cond  [(= k (+ i 1)) #t]
                   [(not (row-good? (car board) i)) #f]
                   [else (check-board (cdr board) (+ i 1))]))
         (check-board positions 0)))

   (define (queen-cols k)
      (if (= k 0)
        (empty-board)
        (filter
            (lambda (positions) (safe? k positions))
            (flatmap
               (lambda (rest-of-queens)
                  (map (lambda (new-row)
                           (adjoin-position new-row rest-of-queens))
                       (enumerate-interval 0 (- board-size 1))))
               (queen-cols (- k 1))))))
   (queen-cols board-size))

(define (deriv exp var)
   (cond [(number? exp) 0]
         [(variable? exp)
            (if (same-variable? exp var) 1 0)]
         [(sum? exp)
            (make-sum (deriv (addend exp) var)
                      (deriv (augend exp) var))]
         [(product? exp)
            (make-sum
               (make-product (multiplier exp)
                             (deriv (multiplicand exp) var))
               (make-product (deriv (multiplier exp) var)
                             (multiplicand exp)))]
         [(exponent? exp)
            (make-product 
               (make-product (power exp) (make-exponent (base exp) (- (power exp) 1)))
               (deriv (base exp) var))]
               
         [else
           (error "unknown expression type --- DERIV" exp)]))

(define (variable? x) (symbol? x))
(define (same-variable? v1 v2)
   (and (variable? v1) (variable? v2) (eq? v1 v2)))
(define (=number? exp num)
   (and (number? exp) (= exp num)))

(define (make-sum a1 a2) 
   (cond [(=number? a1 0) a2]
         [(=number? a2 0) a1]
         [(and (number? a1) (number? a2)) (+ a1 a2)]
         [else (list '+ a1 a2)]))

(define (make-multi-sum a1 a2)
   (if (empty? (cdr a2)) (make-sum a1 (car a2))
                         (make-sum a1 (make-multi-sum (car a2) (cdr a2)))))
(define (make-multi-product m1 m2)
   (if (empty? (cdr m2)) (make-product m1 (car m2))
                         (make-product m1 (make-multi-product (car m2) (cdr m2)))))
         

(define (make-product m1 m2)
   (cond [(or (=number? m1 0) (=number? m2 0)) 0]
         [(=number? m1 1) m2]
         [(=number? m2 1) m1]
         [(and (number? m1) (number? m2)) (* m1 m2)]
         [else (list '* m1 m2)]))
(define (make-exponent b p)
   (cond [(=number? p 0) 1]
         [(or (=number? p 1) (=number? b 1) (=number? b 0)) b]
         [(and (number? b) (number? m2)) (** b p)]
         [else (list '** b p)]))

(define (** b p) ((repeated (lambda (x) (* b x)) (- p 1)) 1))
(define (sum? x) (and (pair? x) (eq? (car x) '+)))
(define (addend s) (cadr s))
(define (augend s) 
   (if (empty? (cdddr s)) 
      (caddr s)
      (make-multi-sum (caddr s) (cdddr s))))
(define (product? x) (and (pair? x) (eq? (car x) '*)))
(define (multiplier p) (cadr p))
(define (multiplicand s) 
   (if (empty? (cdddr s)) 
      (caddr s)
      (make-multi-product (caddr s) (cdddr s))))
(define (exponent? x) (and (pair? x) (eq? (car x) '**)))
(define (base e) (cadr e))
(define (power e) (caddr e))

(define (element-of-set? x set) 
   (cond [(null? set) false]
         [(equal? x (car set)) true]
         [else (element-of-set? x (cdr set))]))

(define (adjoin-set x set)
   (if (element-of-set? x set)
       set
       (cons x set)))

(define (intersection-set set1 set2)
   (cond [(or (null? set1) (null? set2)) '()]
         [(element-of-set? (car set1) set2)
          (cons (car set1)
                (intersection-set (cdr set1) set2))]
         [else (intersection-set (cdr set1) set2)]))


(define (union-set set1 set2)
   (cond [(null? set1) set2]
         [(null? set2) set1]
         [(not (element-of-set? (car set1) set2))
          (cons (car set1)
                (union-set (cdr set1) set2))]
         [else (union-set (cdr set1) set2)]))

(define (element-of-set-multi? x set) 
   (cond [(null? set) false]
         [(equal? x (car set)) true]
         [else (element-of-set-multi? x (cdr set))]))

(define (adjoin-set-multi x set)
       (cons x set))

(define (intersection-set-multi set1 set2)
   (cond [(or (null? set1) (null? set2)) '()]
         [(element-of-set-multi? (car set1) set2)
          (cons (car set1)
                (intersection-set-multi (cdr set1) set2))]
         [else (intersection-set-multi (cdr set1) set2)]))


(define (union-set-multi set1 set2)
   (cond [(null? set1) set2]
         [(null? set2) set1]
         [(not (element-of-set-multi? (car set1) set2))
          (cons (car set1)
                (union-set-multi (cdr set1) set2))]
         [else (union-set-multi (cdr set1) set2)]))

(define (intersection-set-ordered set1 set2)
   (if (or (null? set1) (null? set2))
       '()
       (let ([x1 (car set1)] [x2 (car set2)])
         (cond [(= x1 x2)
                (cons x1
                      (intersection-set-ordered (cdr set1)
                                                (cdr set2)))]
               [(< x1 x2)
                (intersection-set-ordered (cdr set1) set2)]
               [(> x1 x2)
                (intersection-set-ordered set1 (cdr set2))]))))

(define (adjoin-set-ordered x set)
   (if (null? set)
       x
       (let ([y (car set)])
         (cond [(= x y) (cdr set)]
               [(< x y) (adjoin-set-ordered (cdr set))]
               [(> x y) (cons x (cdr set))]))))

 
(define (element-of-set?-ordered x set)
   (if (null? set)
       false
       (let ([y (car set)])
         (cond [(= x y) true]
               [(< x y) (element-of-set?-ordered (cdr set))]
               [(> x y) false]))))

(define (union-set-ordered set1 set2)
   (cond [(null? set1) set2]
         [(null? set2) set1]
         [else
            (let ([x1 (car set1)] [x2 (car set2)])
             (cond [(= x1 x2)
                      (cons x1
                         (union-set-ordered (cdr set1)
                                                (cdr set2)))]
                   [(< x1 x2)
                     (cons x1 (union-set-ordered (cdr set1) set2))]
                   [(> x1 x2)
                     (cons x2 (union-set-ordered set1 (cdr set2)))]))]))

(define (entry tree) (car tree))
(define (left-branch tree) (cadr tree))
(define (right-branch tree) (caddr tre))
(define (make-tree entry left right) (list entry left right))

(define (element-of-set?-tree x set)
   (cond [(null? set) false]
         [(= x (entry set)) true]
         [(< x (entry set)
            (make-tree (entry set)
                       (adjoin-set x (left-branch set))
                       (right-branch set)))]
         [(> x (entry set))
            (make-tree (entry set)
                       (left-branch set)
                       (adjoin-set x (right-branch set)))]))

(define (tree->list-1 tree)
   (if (null? tree)
      '()
      (append (tree->list-1 (left-branch tree))
              (cons (entry tree)
                    (tree-list-1 (right-branch-tree))))))

(define (tree->list-2 tree)
   (define (copy-to-list tree result-list)
      (if (null? tree)
          result-list
          (copy-to-list (left-branch tree)
                        (cons (entry tree)
                              (copy-to-list (right-branch tree)
                                            result-list)))))
   (copy-to-list tree '()))

(define (list->tree elements)
   (car (partial-tree elements (length elements))))

(define (partial-tree elts n)
   (if (= n 0)
       (cons '() elts)
       (let ([left-size (quotient (- n 1) 2)])
            (let ([left-result (partial-tree elts left-size)])
                 (let ([left-tree (car left-result)]
                          [non-left-elts (cdr left-result)]
                          [right-size (- n (+ left-size 1))])
                      (let ([this-entry (car non-left-elts)]
                            [right-result (partial-tree (cdr non-left-elts)
                                                        right-size)])
                           (let ([right-tree (car right-result)]
                                 [remaining-elts (cdr right-result)])
                                (cons (make-tree this-entry left-tree right-tree)
                                      remaining-elts))))))))


;Huffman encoding & decoding

(define (make-leaf symbol weight)
   (list 'leaf symbol weight))
(define (leaf? object)
   (eq? (car object) 'leaf))
(define (symbol-leaf x) (cadr x))
(define (weight-leaf x) (caddr x))

(define (make-code-tree left  right)
   (list left
         right
         (append (symbols left) (symbols right))
         (+ (weight left) (weight right))))

(define (left-branch tree) (car tree))
(define (right-branch tree) (cadr tree))
(define (symbols tree) 
   (if (leaf? tree)
       (list (symbol-leaf tree))
       (caddr tree)))
(define (weight tree)
   (if (leaf? tree)
       (weight-leaf tree)
       (cadddr tree)))

(define (decode bits tree)
   (define (decode-1 bits current-branch)
      (if (null? bits)
          '()
          (let ([next-branch
                 (choose-branch (car bits) current-branch)])
               (if (leaf? next-branch) 
                   (cons (symbol-leaf next-branch)
                         (decode-1 (cdr bits) tree))
                   (decode-1 (cdr bits) next-branch)))))
   (decode-1 bits tree))

(define (choose-branch bit branch)
   (cond [(= bit 0) (left-branch branch)]
         [(= bit 1) (right-branch branch)]
         [else (error "bad bit --CHOOSE-BRANCH" bit)]))

(define (add x y) (apply-generic 'add x y))
(define (sub x y) (apply-generic 'sub x y))
(define (mul x y) (apply-generic 'mul x y))
(define (div x y) (apply-generic 'div x y))

(define (install-scheme-number-package)
   (define (tag x)
      (attach-tag 'scheme-number x))
   (put 'add '(scheme-number scheme-number)
        (lambda (x y) (tag (+ x y))))
   (put 'mul '(scheme-number scheme-number)
        (lambda (x y) (tag (* x y))))
   (put 'div '(scheme-number scheme-number)
        (lambda (x y) (tag (/ x y))))
   (put 'sub '(scheme-number scheme-number)
        (lambda (x y) (tag (- x y))))
   (put 'make 'scheme-number
        (lambda (x) (tag x)))
   'done)
