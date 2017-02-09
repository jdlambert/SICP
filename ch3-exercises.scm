;CHAPTER THREE : MODULARITY, OBJECTS, AND STATE

;3.1
(define (make-accumulator total)
   (lambda (amount)
      (begin (set! total (+ amount total)))
             total))

;3.2
(define (make-monitored f)
   (let ((count 0))
      (define (how-many-calls?) count)
      (define (reset-count) (set! count 0))
      (define (dispatch m)
         (cond ((eq? m 'how-many-calls?) (how-many-calls?))
               ((eq? m 'reset-count) (reset-count))
               (else (begin (set! count (+ 1 count)) (f m)))))
      dispatch))

;3.3 & 3.4
(define (make-account balance password)
   (let ((error-count 0))
      (define (withdraw amount)
         (if (>= balance amount)
             (begin (set! balance (- balance amount))
                     balance)
             "Insufficient Funds"))
      (define (deposit amount)
         (begin (set! balance (+ balance amount))
                balance))
      (define (reset-error-count)
         (set! error-count 0))
      (define (test-error-count)
         (begin (set! error-count (+ error-count 1)) 
                (if (> error-count 7)
                    "Cops alerted"
                    "Incorrect Password")))
      (define (dispatch pw m)
         (if (not (eq? pw password)) (begin (test-error-count) false)
             (begin (reset-error-count)
                    (cond ((eq? m 'withdraw) withdraw)
                          ((eq? m 'deposit) deposit)
                          ((eq? m 'password?) true)
                          (else (error "Unknown request -- MAKE-ACCOUNT"
                                       m))))))
      dispatch))

;3.5
(define (rand-0-to-1) (/ (random 100000000) 100000000.0))
(define (rand-interval a b) (+ a (* (- b a) (rand-0-to-1))))

(define (average-over-trials function trials)
   (define (iter trials-remaining total)
      (if (= trials-remaining 0)
          (/ total trials)
          (iter (- trials-remaining 1) (+ total (function)))))
   (iter trials 0))
   

(define (monte-carlo trials experiment)
   (define (iter trials-remaining trials-passed)
      (cond ((= trials-remaining 0) (/ trials-passed trials))
            ((experiment) (iter (- trials-remaining 1) (+ trials-passed 1)))
            (else (iter (- trials-remaining 1) trials-passed))))
   (iter trials 0))

(define (estimate-integral-test x1 y1 x2 y2 predicate)
   (lambda () (predicate (rand-interval x1 x2) (rand-interval y1 y2))))

(define (estimate-integral x1 y1 x2 y2 predicate trials)
   (monte-carlo trials (estimate-integral-test x1 y1 x2 y2 predicate)))

(define (in-unit-circle? x y)
   (<= (sqrt (+ (* x x) (* y y))) 1))

(define (estimate-pi trials)
   (* 4.0 (estimate-integral -1.0 -1.0 1.0 1.0 in-unit-circle? trials)))

;3.7 
(define (make-joint original orig-pw new-pw)
   (define (test-pw test m)
     (if (eq? new-pw test) (original orig-pw m)
                           "Wrong Password"))
   (if (original orig-pw 'password?) test-pw
                                       "Bad Password"))

;SECTION 3.2 THE ENVIRONMENT MODEL OF EVALUATION

;The many omitted problems here were mostly about drawing environment frames. I found most of them pretty trivial
;and not worth the effort to write down.

;3.18
(define (count-pairs x) 
  (let ((encountered nil))
    (define (iter x)
      (if (or (not (pair? x)) (memq x encountered))
        0
        (begin
          (set! encountered (cons x encountered))
          (+ (iter (car x))
             (iter (cdr x))
             1)
      )
    )
  )
  (iter x)
)

;3.19
(define (cycle? x)
  (let ((encountered nil))
    (define (iter x)
      (set! encountered  (cons x encountered))
      (cond (or (not (pair? x)) (null? (cdr x)) false)
            ((memq (cdr x) visited) true)
            (else (iter cdr x)))
    )
  )
  (iter x)
)

;3.28
(define (or-gate a1 a2 output)
  (define (or-action-procedure)
    (let ((new-value (logical-or (get-signal a1) (get-signal a2))))
      (after-delay or-gate-delay
                   (lambda ()
                      set-signal! output new-value)
      )
    )
  )
  (define (logical-or s1 s2)
    (cond ((or (= s1 1) (= s2 1)) 1) 
          ((and (= s1 0) (= s2 0)) 0)
          (else (error "Invalid signal" s)))
  (add-action! a1 or-action-procedure)
  (add-action! a2 or-action-procedure)
  'ok
)

;3.29
(define (compound-or-gate a1 a2 output)
  (let ((a1-invert make-wire)
        (a2-invert make-wire)
        (and-out make-wire))
    (inverter a1 a1-invert)
    (inverter a2 a2-invert)
    (and-gate a1-invert a2-invert and-out)
    (inverter and-out output)
    'ok
  )
)

;3.33
(define (averager a1 a2 mean)
  (let ((total (make-connector))
        (half (make-connector)))
    (adder a1 a2 total)
    (multiplier total half mean)
    (constant 0.5 half)
    'ok)
)

;3.34 Louis's 'squarer' constraint device has two problems: The lesser problem is that square does not have an inverse. 
;That is, the constraint device would have to make a choice between the positive and negative square roots. The major problem
;is that, on propagating from an input square to the root, both roots would be unfilled, and thus appear indeterminate


;3.35
(define (squarer a b)
  (define (process-new-value)
    (if (has-value? b)
        (if (< (get-value b) 0)
            (error "square less than 0 -- SQUARER" (get-value b))
            (set-value! a sqrt(b) me))
        (if (has-value? a) 
          (set-value! b (* a a) me)
          'done)
    )
  )
  (define (process-forget-value) 
    (forget-value! a me)
    (forget-value! b me)
    (process-new-value)
  )
  (define (me request)
    (cond ((eq? request 'I-have-a-value)
           (process-new-value))
          ((eq? request 'I-lost-my-value)
           (process-forget-value))
          (else (error "Unknonw request -- SQUARER" request))
    ) 
  )
  (connect a me)
  (connect b me)
  me
)

;;3.37 Constraint device operations

(define (cv x) 
  (define connector (make-connector))
  (constant x connector)
  connector
)

(define (c* x y)
  (let ((z (make-connector)))
    (multiplier x y z)
    z))


