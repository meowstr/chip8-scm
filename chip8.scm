(import scheme.base)
(import miscmacros)
(import chicken.number-vector)
(import chicken.bitwise)
(import chicken.random)
(import chicken.memory)
(import chicken.io)
(import srfi-1)
(import srfi-18)
(import deterministic-threads)
(import chicken.process-context)

(import raylib)

(deterministic-threads #t)

(define (file->u8vector path)
  (with-input-from-file path read-bytevector #:binary))

(define program (file->u8vector (first (command-line-arguments))))

(define font 
  #u8(#xF0 #x90 #x90 #x90 #xF0   ;; 0
      #x20 #x60 #x20 #x20 #x70   ;; 1
      #xF0 #x10 #xF0 #x80 #xF0   ;; 2
      #xF0 #x10 #xF0 #x10 #xF0   ;; 3
      #x90 #x90 #xF0 #x10 #x10   ;; 4
      #xF0 #x80 #xF0 #x10 #xF0   ;; 5
      #xF0 #x80 #xF0 #x90 #xF0   ;; 6
      #xF0 #x10 #x20 #x40 #x40   ;; 7
      #xF0 #x90 #xF0 #x90 #xF0   ;; 8
      #xF0 #x90 #xF0 #x10 #xF0   ;; 9
      #xF0 #x90 #xF0 #x90 #x90   ;; A
      #xE0 #x90 #xE0 #x90 #xE0   ;; B
      #xF0 #x80 #x80 #x80 #xF0   ;; C
      #xE0 #x90 #x90 #x90 #xE0   ;; D
      #xF0 #x80 #xF0 #x80 #xF0   ;; E
      #xF0 #x80 #xF0 #x80 #x80)) ;; F

(define memory (make-u8vector 4096 0))

(define reg (make-u8vector 16 0))
(define reg-i 0)
;; 64 x 32 screen
(define screen (make-u8vector (* 8 32) 0))
(define stack (list))
(define reg-delay 0)

;; copy font into memory
(move-memory! font memory)

;; copy program in memory
(move-memory! program memory (u8vector-length program) 0 #x200)

(define ip #x200)

(define (word->octals word)
  (list
    (bitwise-and #xF (arithmetic-shift word -12))
    (bitwise-and #xF (arithmetic-shift word -8))
    (bitwise-and #xF (arithmetic-shift word -4))
    (bitwise-and #xF (arithmetic-shift word -0))
    ))

(define (log-instr x)
  ;(print x)
  #f)

(define (draw-bit lx ly b)
  (define x (modulo lx 64))
  (define y (modulo ly 32))
  (define i (+ (* y 64) x))
  (modify! 
    (u8vector-ref screen (quotient i 8))
    (lambda (s)
      (define mask (arithmetic-shift b (modulo i 8)))
      (unless (= 0 (bitwise-and s mask))
        (u8vector-set! reg #xf 1))
      (bitwise-xor s mask))))

(define (draw-byte x y b)
  (for-each
    (lambda (k)
      (draw-bit (+ x k) y (bitwise-and 1 (arithmetic-shift b (- k 7)))))
    (iota 8)))

(define (sprite-op x y n)
  (for-each
    (lambda (row)
      (define b (u8vector-ref memory (+ reg-i row)))
      (draw-byte x (+ y row) b))
    (iota n)))

(define chip8-keys 
  (list KEY_X KEY_ONE KEY_TWO KEY_THREE ; 0 1 2 3
        KEY_Q KEY_W KEY_E KEY_A         ; 4 5 6 7
        KEY_S KEY_D KEY_Z KEY_C         ; 8 9 A B
        KEY_FOUR KEY_R KEY_F KEY_V))    ; C D E F

(define steps-per-frame 400)
(define fuel 0)

(define (chip8-loop)
  (define hex (string->vector "0123456789ABCDEF"))
  (define instr 
    (+ (arithmetic-shift (u8vector-ref memory ip) 8)
       (u8vector-ref memory (add1 ip))))
  (define octals (word->octals instr))
  (define nnn (+ (* (second octals) 256)
                 (* (third octals) 16)
                 (fourth octals)))
  (define nn (+ (* (third octals) 16)
                (fourth octals)))
  (define n (fourth octals))
  (define x (second octals))
  (define y (third octals))
  (define reg-x (u8vector-ref reg x))
  (define reg-y (u8vector-ref reg y))
  ;(display (number->string ip 16))
  ;(display " ")
  ;(display (list->string (map (cut vector-ref hex <>) octals)))
  ;(display " ")
  (inc! ip 2)
  (cond
    ((= instr #x00E0) 
     (log-instr "clear")
     (set! screen (make-u8vector (* 8 32) 0)))
    ((= instr #x00EE) 
     (log-instr "return")
     (set! ip (pop! stack)))
    ((= (first octals) #x1) 
     (log-instr "jump NNN")
     (set! ip nnn))
    ((= (first octals) #x2) 
     (log-instr "call NNN")
     (push! ip stack)
     (set! ip nnn))
    ((= (first octals) #x3) 
     (log-instr "if vx != NN then")
     (when (= reg-x nn) (inc! ip 2)))
    ((= (first octals) #x4) 
     (log-instr "if vx == NN then")
     (unless (= reg-x nn) (inc! ip 2)))
    ((and (= (first octals) #x5) (= (fourth octals) #x0)) 
     (log-instr "if vx != vy then")
     (when (= reg-x reg-y) (inc! ip 2)))
    ((= (first octals) #x6) 
     (log-instr "vx := NN")
     (u8vector-set! reg x nn))
    ((= (first octals) #x7) 
     (log-instr "vx += NN")
     (modify! (u8vector-ref reg x) (o (cut bitwise-and #xff <>) (cut + <> nn))))
    ((and (= (first octals) #x8) (= (fourth octals) #x0)) 
     (log-instr "vx := vy")
     (set! (u8vector-ref reg x) reg-y))
    ((and (= (first octals) #x8) (= (fourth octals) #x1)) 
     (log-instr "vx |= vy")
     (modify! (u8vector-ref reg x) (lambda (z) (bitwise-ior z reg-y))))
    ((and (= (first octals) #x8) (= (fourth octals) #x2)) 
     (log-instr "vx &= vy")
     (modify! (u8vector-ref reg x) (lambda (z) (bitwise-and z reg-y))))
    ((and (= (first octals) #x8) (= (fourth octals) #x3)) 
     (log-instr "vx ^= vy")
     (modify! (u8vector-ref reg x) (lambda (z) (bitwise-xor z reg-y))))
    ((and (= (first octals) #x8) (= (fourth octals) #x4)) 
     (log-instr "vx += vy")
     (modify! (u8vector-ref reg x) (o (cut bitwise-and #xff <>) (cut + <> reg-y)))
     (if (> (+ reg-x reg-y) 255) 
       (u8vector-set! reg #xf 1)
       (u8vector-set! reg #xf 0)))
    ((and (= (first octals) #x8) (= (fourth octals) #x5)) 
     (log-instr "vx -= vy")
     (dec! (u8vector-ref reg x) reg-y)
     (if (>= reg-x reg-y) 
       (u8vector-set! reg #xf 1)
       (u8vector-set! reg #xf 0)))
    ((and (= (first octals) #x8) (= (fourth octals) #x6)) 
     (log-instr "vx >>= vy")
     (modify! (u8vector-ref reg x) (cut quotient <> 2))
     (u8vector-set! reg #xf (bitwise-and 1 reg-x)))
    ((and (= (first octals) #x8) (= (fourth octals) #x7)) 
     (log-instr "vx =- vy")
     (modify! (u8vector-ref reg x) (cut - reg-y <>))
     (if (>= reg-y reg-x) 
       (u8vector-set! reg #xf 1)
       (u8vector-set! reg #xf 0)))
    ((and (= (first octals) #x8) (= (fourth octals) #xE)) 
     (log-instr "vx <<= vy")
     (modify! (u8vector-ref reg x) (o (cut bitwise-and #xff <>) (cut * <> 2)))
     (u8vector-set! reg #xf (arithmetic-shift reg-x -7)))
    ((and (= (first octals) #x9) (= (fourth octals) #x0)) 
     (log-instr "if vx == vy then")
     (unless (= reg-x reg-y) (inc! ip 2)))
    ((= (first octals) #xA) 
     (log-instr "i := NNN")
     (set! reg-i nnn))
    ((= (first octals) #xB) 
     (log-instr "jump0 NNN")
     (set! ip (+ (u8vector-ref reg 0) nnn)))
    ((= (first octals) #xC) 
     (log-instr "vx := random NN")
     (u8vector-set! reg x (bitwise-and nn (pseudo-random-integer 256))))
    ((= (first octals) #xD) 
     (log-instr "sprite vx vy N")
     (u8vector-set! reg #xf 0)
     (sprite-op reg-x reg-y n))
    ((and (= (first octals) #xE) (= (third octals) #x9) (= (fourth octals) #xE)) 
     (log-instr "if vx -key then")
     (when (is-key-down (list-ref chip8-keys reg-x)) (inc! ip 2)))
    ((and (= (first octals) #xE) (= (third octals) #xA) (= (fourth octals) #x1)) 
     (log-instr "if vx key then")
     (unless (is-key-down (list-ref chip8-keys reg-x)) (inc! ip 2)))
    ((and (= (first octals) #xF) (= (third octals) #x0) (= (fourth octals) #x7)) 
     (log-instr "vx := delay")
     (u8vector-set! reg x reg-delay))
    ((and (= (first octals) #xF) (= (third octals) #x0) (= (fourth octals) #xA)) 
     (log-instr "vx := key")
     (let loop ()
       (define k (get-key-pressed))
       (define kk (list-index (cut = k <>) chip8-keys))
       (if kk
         (u8vector-set! reg x (bitwise-and #xff kk))
         (begin 
           (thread-yield!)
           (loop)))))
    ((and (= (first octals) #xF) (= (third octals) #x1) (= (fourth octals) #x5)) 
     (log-instr "delay := vx")
     (set! reg-delay reg-x))
    ((and (= (first octals) #xF) (= (third octals) #x1) (= (fourth octals) #x8)) 
     (log-instr "buzzer := vx"))
    ((and (= (first octals) #xF) (= (third octals) #x1) (= (fourth octals) #xE)) 
     (log-instr "i += vx")
     (modify! reg-i (o (cut bitwise-and #xfff <>) (cut + <> (u8vector-ref reg x)))))
    ((and (= (first octals) #xF) (= (third octals) #x2) (= (fourth octals) #x9)) 
     (log-instr "i := hex vx")
     (set! reg-i (* 5 (u8vector-ref reg x))))
    ((and (= (first octals) #xF) (= (third octals) #x3) (= (fourth octals) #x3)) 
     (log-instr "bcd vx")
     (u8vector-set! memory (+ reg-i 0) (modulo (quotient reg-x 100) 10))
     (u8vector-set! memory (+ reg-i 1) (modulo (quotient reg-x  10) 10))
     (u8vector-set! memory (+ reg-i 2) (modulo (quotient reg-x   1) 10)))
    ((and (= (first octals) #xF) (= (third octals) #x5) (= (fourth octals) #x5)) 
     (log-instr "save vx")
     (for-each 
       (lambda (k)
         (u8vector-set! memory (+ reg-i k) (u8vector-ref reg k))) 
       (iota (add1 x))))
    ((and (= (first octals) #xF) (= (third octals) #x6) (= (fourth octals) #x5)) 
     (log-instr "load vx")
     (for-each
       (lambda (k)
         (u8vector-set! reg k (u8vector-ref memory (+ reg-i k))))
       (iota (add1 x))))
    (else (error "invalid opcode" (list->string (map (cut vector-ref hex <>) octals)))))
  (when (= fuel 0)
    (thread-yield!)
    (set! fuel steps-per-frame))
  (dec! fuel)
  (chip8-loop))

(thread-start! chip8-loop)

(init-window 640 320 "chip8")

(set-target-fps 60)

(define (draw-cell i)
  (define x (modulo i 64))
  (define y (quotient i 64))
  (define byte (u8vector-ref screen (quotient i 8)))
  (define b 
    (bitwise-and 1 (arithmetic-shift byte (- (modulo i 8)))))
  (when (= b 1)
    (draw-rectangle (* 10 x) (* 10 y) 10 10 BEIGE)))

(until 
  (window-should-close)
  (begin-drawing)
  (clear-background BROWN)
  (for-each 
    draw-cell
    (iota (* 32 64)))
  (draw-fps 2 2)
  (end-drawing)
  (unless (= reg-delay 0) 
    (dec! reg-delay))
  (thread-yield!))

(close-window)
