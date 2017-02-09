#lang racket

(require (planet dyoo/simply-scheme))
(provide (all-defined-out))

;;Begin Project 1
(require "adjectives.rkt") 

;;Below is some procedures to help you out. Dont worry about what it says or does.
;;Questions are Below.

(define (want-exit? line)
  (or (member? 'exit line) (member? 'quit line) (member? 'bye line)))

(define (print-sentence sent)
  (for-each (lambda (x) (display x) (display " "))
            sent)
  (newline))

(define (interact bot)
  (define (helper)
    (display "> ") (flush-output)
    (let ([line (read-line)])
      (unless (want-exit? line)
        (print-sentence (bot line))
        (helper))))
  (helper))

(define (chatter bot1 bot2 start iterations)
  (define (helper b1 b2 sent i)
    (when (< i iterations)
          (display "bot ") (display (add1 (remainder i 2))) (display ": ")
          (let ((out (b1 sent)))
            (print-sentence out)
            (helper b2 b1 out (add1 i)))))
  (display "start: ") (print-sentence start)
  (helper bot1 bot2 start 0))

;;; Checks if a given word is an adjective or not
;;; Requires adjectives.scm to be loaded beforehand
(define adjective?
  (let ((hash (make-hash)))
    (for-each (lambda (adj)
		(hash-set! hash adj #t))
	      adjectives)
    (lambda (wd) (hash-ref hash wd #f))))


;; Begin Questions:
;;Q1 - babybot
  (define (babybot sent) sent)

;;Q2 - stupidbot-creator
  (define (stupidbot-creator motto)
    (lambda (line) motto))

;;Q3 - matcherbot-creator
  (define (matcherbot-creator pattern)
    (define (after-match temp-pattern sentence)
      (cond [(null? temp-pattern) sentence]
            [(null? sentence) '(#f)]
            [(equal? (car temp-pattern) (car sentence))
                (after-match (cdr temp-pattern) (cdr sentence))]
            [else (after-match pattern (cdr sentence))]))
    (lambda (line) (after-match pattern line))
  )  

  (define (index-of element list)
    (define (iter sublist n)
      (cond [(null? sublist) #f]
            [(equal? element (car sublist)) n]
            [else (iter (cdr sublist) (+ n 1))]))
    (iter list 0))

;;Q4 - substitutebot-creator
  (define (substitutebot-creator from to)
    (define (sub-proc element)
      (let ([i (index-of element from)])
        (if (number? i)
            (list-ref to i)
            element)))
    (lambda (line) (map sub-proc line)) 
  )

;;Q5 - switcherbot
  (define (switcherbot sent)
    (let* ([from '(You you me I am was my yours are were your mine)]
           [to '(I me you you are were your mine am was my yours)]
           [sub (substitutebot-creator from to)])
           (sub sent))
  )


;;Q6 - inquisitivebot
  (define (inquisitivebot sent)
    (let* ([from '(I me am was mine my)]
           [to '(you you are were yours your)]
           [sub (substitutebot-creator from to)])
      (if (empty? sent) '() (append (sub sent) '(?))))
  )
  
;;Q7 - eliza
  (define (eliza sent)
    (cond [(empty? sent) '(how can I help you ?)]
          [(equal? (first sent) 'hello) '(hello there !)]
          [(equal? (last sent) '?) '(I can not answer that question)]
          [(let ([match ((matcherbot-creator '(I am)) sent)])
                (if (not (equal? '(#f) match)) (append '(Why are you) (switcherbot match) '(?))
                                               (switcherbot sent)))])
  )

;;Q8 - reactorbot-creator
  (define (reactorbot-creator bot pat out)
     (lambda (line)
        (if (equal? ((matcherbot-creator pat) line) '(#f))
            (bot line)
            out))
  )

;;Q9 - replacerbot-creator
  (define (replacerbot-creator bot pat before after)
     (lambda (line)
        (let ([match ((matcherbot-creator pat) line)])
          (if (equal? match '(#f))
             (bot line)
             (append before match after))))
  )

;;Q10 - exagerate
  (define (exaggerate bot n)  
      (lambda (line)
        (define (exag-proc current)
          (cond [(null? current) null]
                [(adjective? (car current)) (cons 'very (cons (car current) (exag-proc (cdr current))))]
                [else (cons (car current) (exag-proc (cdr current)))]))
        ((repeated exag-proc n) (bot line)))
  )

;;REMEMBER TO ADD YOUR OWN TESTS TO GRADER.RKT!
;;END OF PROJECT 1
