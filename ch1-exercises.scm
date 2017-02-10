; CHAPTER ONE: BUILDING ABSTRACTIONS WITH PROCEDURES

; Revisit later: 13-15

; SECTION 1.1: The Elements of Programming

; 1. Just a bit of reading of scheme expressions, nothing special and
;    meaningless out of context, so not included here.

; 2. Conversion of a mathematical expression to a Scheme expression: 

(/ (+ 5 4 (- 2 (- 3 (+ 6 (/ 4 5))))) (* 3 (- 6 2) (- 2 7))) 

; 3. A procedure that takes three numbers as arguments and returns the sum
;    of the squares of the two larger numbers 

(define (square x) (* x x))

(define (sum-of-squares x y) (+ (square x) (square y)))

(define (sum-of-squares-of-two-largest x y z) 
  (if (>= x y) 
      (if (>= y z)
          (sum-of-squares x y)
          (sum-of-squares x z))
      (if (>= x z)
          (sum-of-squares x y)
          (sum-of-squares y z))))

; 4. An example of a combination whose operator is a compound expression:

(define (a-plus-abs-b a b)
  ((if (> b 0) + -) a b))

; 5.

(define (p) (p)) ; (p) doesn't halt

(define (test x y)
  (if (= x 0)
      0
      y))

; (test 0 (p)) will enter the (p) if the implementation of combinations follows
; application order. If written in normal order, the same combination will simply
; evaluate to 0.

; 6. The problem with defining 'if' in terms of 'cond':

(define (new-if predicate then-clause else-clause)
  (cond (predicate then-clause)
        (else clause)))

(define (new-if-sqrt-iter x)
  (new-if (good-enough? guess x)
          guess
          (sqrt-iter (improve guess x)
                     x)))

; 'new-if' uses applicative order. That is to say the predicate, the 'then' clause, and the 'else' clause will 
; all be evaluated before choosing which clause is the value of the application. 
; This early evaluation of the 'else' clause results in infinite recursion through 'else' clauses.
; This problem is avoided by the evaluation rules of the special form 'if', which first evaluates the predicate,
; then only evaluates the 'then' or 'else' clause based on the predicate's truth value.

; 7. Improving 'good-enough' metric:
; I simply changed 'good-enough' to be a function of the previous guess and the current guess, instead of just the current guess.

(define (improved-sqrt-iter guess x)
  (define (iter guess last-guess)
    (if (improved-good-enough? guess last-guess)
        guess
        (iter (improve guess x)
                   guess)))
  (iter 0.5 1.0))

(define (improved-sqrt x)
  (improved-sqrt-iter 1.0 x))

(define fractional-target 0.000001) 

(define (improved-good-enough? guess last-guess)
  (< (unsigned-fractional-diff guess last-guess) fractional-target))

(define (unsigned-fractional-diff x y)
  (abs (/ (- x y) x)))

(define (improve guess x)
  (average guess (/ x guess)))

(define (average x y)
  (/ (+ x y) 2))
        
; 8. An analogous cube root procedure:

(define (cube-root-iter guess x)
  (define (iter guess last-guess)
    (if (improved-good-enough? guess last-guess)
        guess
        (iter (cube-improve guess x)
                   guess)))
  (iter 0.5 1.0))

(define (cube-improve guess x)
  (/ (+ (/ x (square guess)) (* 2 guess)) 3))

(define (square x) (* x x))

(define (cube-root x)
  (cube-root-iter 1.0 x))

; SECTION 1.2: Procedures and the Processes They Generate

; 9. Two different process 'shapes':

; Both are recursive procedures

; This procedure details a recursive process. It builds a stack of deferred 'inc' calls.
; (define (+ a b)
;   (if (= 0 a)
;       b
;       (inc (+ (dec a) b))))

; This procedure details an iterative process, all of the process's state is held in the arguments to '+',
; and it will be optimized by tail recursion

; (define (+ a b)
;   (if (= 0 a)
;       b
;       (+ (dec a) (inc b))))

; 10. Ackermann's function:

(define (A x y)
  (cond ((= y 0) 0)
        ((= x 0) (* 2 y))
        ((= y 1) 2)
        (else (A (- x 1)
                 (A x (- y 1))))))

; (A 1 10) is 1024, 2 to the 10th power

;    (A 2 4)
; -> (A 1 (A 2 3))
; -> (A 1 (A 1 (A 2 2)))
; -> (A 1 (A 1 (A 1 (A 2 1))))
; -> (A 1 (A 1 (A 1 2)))
; (A 1 N) is 2^N, so, this can be written as
; -> 2^(2^(2^2)) = 2^16 = 65536

;    (A 3 3)
; -> (A 2 (A 3 2))
; -> (A 2 (A 2 (A 3 1)))
; -> (A 2 (A 2 2)
; Earlier, I saw that (A 2 2) was (A 1 2), which is 4, so
; -> (A 2 4)
; -> 65536

(define (f n) (A 0 n)) ; f(n) = 2*n
(define (g n) (A 1 n)) ; g(n) = 2^n
(define (h n) (A 2 n)) ; h(n) = 2^2^2^...^2, with n operations. I just looked up the name of this operation: 'tetration'.

; (A 2 n) [n > 1] = (A 1 (A 2 (- 1 n))
; So h(n) = 2^(h(n-1))
; Since h(1) = 2, h(n) is a chain of n nested 2^2's

; 11. f(n) = n if n < 3, f(n) = f(n-1) + 2f(n-2) + 3f(n-3) if n>=3

(define (recursive-f n)
  (if (< n 3)
      n
      (+ (recursive-f (- n 1))
         (* 2 (recursive-f (- n 2)))
         (* 3 (recursive-f (- n 3)))))) ; Pretty easy to reason about and write,
                                        ; but lots of duplicated work, even with somewhat small arguments

(define (iterative-f n)
  (define (iter fi fi-1 fi-2 i)
    (if (= n i) 
        fi
        (iter (+ fi (* 2 fi-1) (* 3 fi-2)) ; A bit harder to reason about and write
              fi                           ; much faster at any input size, due to tail recursion
              fi-1
              (+ i 1))))
  (if (< n 3) 
      n
      (iter 4 2 1 3))) ; since f(3) = f(2) + 2f(1) = 3f(0) = 2 + 2 = 4

; 12. Pascal's Triangle recursive process:
; Align the triangle on the left, and find a value as a function of its row and column numbers

; 1
; 1 1
; 1 2 1
; 1 3 3 1           
; 1 4 6 4 1
; 1 5 10 10 5 1
; 1 6 15 20 15 6 1

(define (pascal row col)
  (cond ((or (< row 0) (< col 0) (> col row)) (error "ERROR --- INVALID INPUT" row col))
        ((or (= 0 row) (= row col) (= 0 col)) 1)
        (else (+ (pascal (- row 1) col)
                 (pascal (- row 1) (- col 1))))))

; 13-15. Math exercises, to be revisited when I have pen and paper

; 16. An iterative exponentiation process that uses successive squaring to achieve a logarithmic number of steps

(define (iterative-exponent b n)
  (define (iter current exp)
    (cond ((= n exp) current)
          ((> n (* 2 exp)) (iter (square current) (* 2 exp)))
          (else (iter (* b current) (+ 1 exp)))))
  (iter b 1))

; 17 & 18. If our language had no well-implemented multiplication, but had addition, double, and halve,
; the iterative-multiplication would be almost identical to the above:

(define (iterative-multiply a b)
  (define (iter current num)
    (cond ((= b num) current)
          ((> b (double num)) (iter (double current) (double num)))
          (else (iter (+ a current) (+ 1 exp)))))
  (iter b 1))

; 19. Iterative process that calculates a value in the fibonacci sequence in logarithmic time:

(define (fib n)
  (define (fib-iter a b p q count)
    (cond ((= count 0) b)
          ((even? count) (fib-iter a b (next-p p q) (next-q p q) (/ count 2)))
          (else (fib-iter (+ (* b q) (* a q) (* a p))
                          (+ (* b p) (* a q))
                          p
                          q
			  (- count 1)))))
  (define (next-p p q)
    (+ (* p p) (* q q)))
  (define (next-q p q)
    (+ (* 2 p q) (* q q)))
  (fib-iter 1 0 0 1 n))

; The challenge in the above problem is finding a way to map the pair (p,q) to a new pair (p',q') representing two consecutive transformations.

; Here're the initial mappings:
; a <- bq + a(q+p)
; b <- bp + aq

; Transforming b twice:
; b <- (bp + aq)p + (bq + a(q+p))q

; Collecting 'b's and 'a's:
; b(pp + qq) + a(2pq + qq)

; Transforming a twice:
; a <- (bp + aq)q + (bq + a(q+p))(q+p)

; Collecting 'b's and 'a's:
; a <- b(2pq + qq) + a(qq + qq + pp + 2pq)

; Since the last term is the sum of (2pq + qq) and (pp + qq), this is confirmation that a mapping from
; (p,q) to (pp + qq, 2pq + qq) is a mapping from the base operation to a 'squared' operation

; 20. Differences in process shape between normal-order and applicative-order evaluation:

; Applicative order:
; (gcd 206 40) -> (gcd 40 (remainder 206 40)) -> (gcd 40 6) -> (gcd 6 (remainder 40 6)) -> (gcd 6 4) -> (gcd 4 (remainder 6 4))
; -> (gcd 4 2) -> (gcd 2 (remainder 4 2)) ->  (gcd 2 0) -> 2
; This order uses 4 remainder operations

; Normal order is a bit tricker:

(gcd 206 40)

(if (= 40 0)
    206
    (gcd 40 (remainder 206 40)))

(if (= 6 0) ; FIRST REMAINDER
    40
    (gcd (remainder 206 40) (remainder 40 (remainder 206 40))))

; Remainder calls inside gcd calls tend to get more and more nested, as their application is delayed.
; Those inside predicates can be immediately applied.

(if (= 4 0) ; SECOND AND THIRD
    (remainder 206 40)
    (gcd (remainder 40 (remainder 206 40)) (remainder (remainder 206 40) (remainder 40 (remainder 206 40)))))

(if (= 0 2) ; FOURTH THROUGH SEVENTH
    (remainder 40 (remainder 206 40))
    (gcd (remainder (remainder 206 40) (remainder 40 (remainder 206 40))) 
	 (remainder (remainder 40 (remainder 206 40)) (remainder (remainder 206 40) (remainder 40 (remainder 206 40)))))

(if (= 0 2) ; EIGHTH THROUGH FOURTEENTH
    2 ; FIFTEENTH THROUGH EIGHTEENTH, (gcd 206 40) evaluates to 2 after EIGHTEEN remainder operations in normal order
    (gcd (remainder (remainder 40 (remainder 206 40)) (remainder (remainder 206 40) (remainder 40 (remainder 206 40))))
         (remainder (remainder (remainder 206 40) (remainder 40 (remainder 206 40)))
                    (remainder (remainder 40 (remainder 206 40)) (remainder (remainder 206 40) (remainder 40 (remainder 206 40)))))))

; 21. Tracing through an algorithm to find the smallest divisors of a few numbers. Not worth the time to type here.

; 22. Timed prime tests:

(define (timed-prime-test n)
    (newline)
    (display n)
    (start-prime-test n (runtime)))

(define (start-prime-test n start-time)
    (if (prime? n)
        (report-prime (- (runtime) start-time))))

(define (report-prime elapsed-time)
    (display " *** ")
    (display elapsed-time))

(define (search-for-primes lower upper) 
  (define (iter n) 
    (if (<= n upper)
        (begin (timed-prime-test n)
               (iter (+ n 1)))
        (display "End of testing")))
  (iter lower))

; Since the testing algorithm has order of growth THETA(sqrt(N)), the book suggests that testing for primes around 10000 should take
; around sqrt(10) times as long as testing for primes around 1000. However, my elapsed-time only evaluates to a non-zero value
; once the tested number starts to reach around 10^6. I just found this fascinating, just a little example of how much computing power
; has grown since this text was published.

; 23. Optimizing find-divisor by making it skip testing even numbers other than two

(define (smallest-divisor-skip-evens n)
    (find-divisor-skip-evens n 2))

(define (find-divisor-skip-evens n test-divisor)
    (cond ((> (square test-divisor) n) n)
                  ((divides? test-divisor n) test-divisor)
                          (else (find-divisor-skip-evens n (next-divisor test-divisor)))))

(define (next-divisor test-divisor)
    (if (= 2 test-divisor)
        3
        (+ test-divisor 2)))

(define (divides? a b)
    (= (remainder b a) 0))

(define (prime-skip-evens? n)
    (= n (smallest-divisor-skip-evens n)))

(define (smallest-divisor n)
    (find-divisor n 2))

(define (find-divisor n test-divisor)
    (cond ((> (square test-divisor) n) n)
                  ((divides? test-divisor n) test-divisor)
                          (else (find-divisor n (+ test-divisor 1)))))

(define (prime? n)
    (= n (smallest-divisor n)))

(define (prime-tester-time num)
    (define (start-test test? start-time)
        (test? num)
        (display "***")
        (display  (- (runtime) start-time)))
    (start-test prime-skip-evens? (runtime)) 
    (start-test prime? (runtime)))
   
; The algorithm isn't twice as fast as the original, as you might guess. Here're a couple data points:
;       Number        |     Improved Speed    |    Original Speed   |   Ratio 
; 48 millionth prime  |         50ms          |         90ms        |   1:1.8
; 49 millionth prime  |         50ms          |         80ms        |   1:1.6
; 49 millionth prime  |         50ms          |         80ms        |   1:1.6
; 49 millionth+1 prime|         60ms          |         80ms        |   1:1.33
; 50 millionth prime  |         50ms          |         90ms        |   1:1.8 

; I'm not sure what to make of these numbers. They're pretty consistent. I assume that (runtime) only has a resolution of 10ms,
; but I'm not sure I can reconcile that with the consistency.

; I do have an idea as to why the ratio isn't closer to 1:2, though. The replacement of the primitive operation (+ test-divisor 1)
; by (next-divisor test-divisor) is a significant increase in resource use. 
; This call builds a new environment pane, and in turn tests a conditional and then evaluates the appropriate branch.
; The result is a bit of a drop in performance compared to the primitive operation.

; 24.  prime tests:

; In this exercise, I rewrite the above timed prime tests to use fast-prime?, which is an implementation of Fermat's little theorem.
; The Fermat test has an order of growth of THETA(log N), so I'd expect the time to test primes near 10^6 to be around twice those needed
; to test primes near 10^3


(define (timed-fermat-prime-test n)
    (newline)
    (display n)
    (start-fermat-prime-test n (runtime)))

(define (start-fermat-prime-test n start-time)
    (if (fast-prime? n 100)
        (report-prime (- (runtime) start-time))))

(define (fermat-search-for-primes lower upper) 
  (define (iter n) 
    (if (<= n upper)
        (begin (timed-fermat-prime-test n)
               (iter (+ n 1)))
        (display "End of testing")))
  (iter lower))

; I sort of arbitrarily chose 100 as the number of repetitions. As expected, the order of growth seems logarithmic. Specifically, primes around 10^6 were detected in around 10ms, while those around 10^12 were detected in around 20ms. I also looked at some Carmichael numbers and saw that they were, as expected, falsly reported as prime.

;
