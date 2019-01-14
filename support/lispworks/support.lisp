;;;; -*- Mode: Lisp; Syntax: ANSI-Common-Lisp; indent-tabs-mode: nil; external-format: utf-8; -*-

(cl:defpackage #:blodwen-rts
  (:use #:cl)

  (:export
   #:blodwen-read-args

   #:b+
   #:b-
   #:b*
   #:b/

   #:cast-string-int
   #:cast-string-double

   #:string-cons
   #:string-append
   #:string-reverse
   #:string-substr

   #:get-tag

   #:delay
   #:force

   #:box
   #:unbox
   #:set-box

   #:blodwen-new-buffer
   #:blodwen-buffer-size
   #:blodwen-buffer-setbyte
   #:blodwen-buffer-getbyte
   #:blodwen-buffer-setint
   #:blodwen-buffer-getint
   #:blodwen-buffer-setdouble
   #:blodwen-buffer-getdouble
   #:blodwen-buffer-setstring
   #:blodwen-buffer-getstring
   #:blodwen-readbuffer
   #:blodwen-writebuffer

   #:blodwen-file-op
   #:blodwen-open-stream
   #:blodwen-close-stream
   #:blodwen-putstring
   #:blodwen-get-line
   #:blodwen-eof

   #:blodwen-thread
   #:blodwen-get-thread-data
   #:blodwen-set-thread-data
   #:blodwen-mutex
   #:blodwen-lock
   #:blodwen-unlock
   #:blodwen-thisthread
   #:blodwen-condition
   #:blodwen-condition-wait
   #:blodwen-condition-wait-timeout
   #:blodwen-condition-signal
   #:blodwen-condition-broadcast
   #:blodwen-sleep))

(in-package #:blodwen-rts)

(declaim (optimize speed (safety 1) (debug 1)))

(setq *read-default-float-format* 'double-float)

(defun blodwen-read-args (desc)
  (case (svref desc 0)
    ((0) '())
    ((1) (cons (svref desc 2)
               (blodwen-read-args (svref desc 3))))))

(defun b+ (x y bits)
  (mod (+ x y) (expt 2 bits)))

(defun b- (x y bits)
  (mod (- x y) (expt 2 bits)))

(defun b* (x y bits)
  (mod (* x y) (expt 2 bits)))

(defun b/ (x y bits)
  (mod (/ x y) (expt 2 bits)))

(defun cast-string-int (x)
  (handler-case
      (parse-integer x)
    (parse-error ()
      0)))

(defun cast-string-double (x)
  (handler-case
      (hcl:parse-float x)
    (parse-error ()
      0.0d0)))

(defun string-cons (x y)
  (lw:string-append x y))

(defun string-append (x y)
  (lw:string-append x y))

(defun get-tag (x)
  (svref x 0))

(defun string-reverse (x)
  (reverse x))

(defun string-substr (off len s)
  (let* ((l (length s))
         (b (max 0 off))
         (x (max 0 len))
         (end (min l (+ b x))))
    (subseq s b end)))

(defun either-left (x)
  (vector 0 nil nil x))

(defun either-right (x)
  (vector 1 nil nil x))

;;; Delay/Force

(defmacro delay (expr)
  `#'(lambda () ,expr))

(defun force (thunk)
  (funcall thunk))

;;; Box

(declaim (ftype (function (t) simple-vector) box))
(defun box (v)
  (declare (optimize speed (safety 0) (debug 1)))
  (make-array 1
              :element-type t
              :initial-element v
              :allocation :static))

(declaim (ftype (function (simple-vector) t) unbox))
(defun unbox (box)
  (declare (optimize speed (safety 0) (debug 1))
           (type simple-vector box))
  (aref box 0))

(declaim (ftype (function (simple-vector t) t) set-box))
(defun set-box (box v)
  (declare (optimize speed (safety 0) (debug 1))
           (type simple-vector box))
  (setf (aref box 0) v))

;;; Buffers

(deftype byte-vector (&optional size)
  `(simple-array (unsigned-byte 8) (,size)))

(declaim (ftype (function (fixnum) byte-vector) blodwen-new-buffer))
(defun blodwen-new-buffer (size)
  (declare (optimize speed (safety 0) (debug 1))
           (type fixnum size))
  (make-array size
              :element-type '(unsigned-byte 8)
              :initial-element 0
              :allocation :static))

(declaim (ftype (function (byte-vector) fixnum) blodwen-buffer-size))
(defun blodwen-buffer-size (buf)
  (declare (optimize speed (safety 0) (debug 1))
           (type byte-vector buf))
  (length buf))

(declaim (ftype (function (byte-vector fixnum (unsigned-byte 8)) (unsigned-byte 8)) blodwen-buffer-setbyte))
(defun blodwen-buffer-setbyte (buf loc val)
  (declare (optimize speed (safety 0) (debug 1))
           (type byte-vector buf)
           (type fixnum loc)
           (type (unsigned-byte 8) val))
  (setf (aref buf loc) val))

(declaim (ftype (function (byte-vector fixnum) (unsigned-byte 8)) blodwen-buffer-getbyte))
(defun blodwen-buffer-getbyte (buf loc)
  (declare (optimize speed (safety 0) (debug 1))
           (type byte-vector buf)
           (type fixnum loc))
  (aref buf loc))

(declaim (inline write-8-bytes)
         (ftype (function (byte-vector (unsigned-byte 64))) write-8-bytes))
(defun write-8-bytes (buf start integer)
  (declare (optimize speed (safety 0) (debug 1))
           (type byte-vector buf)
           (type fixnum start)
           (type (unsigned-byte 64) integer))
  (setf (aref buf start) (ldb (byte 8 56) integer))
  (setf (aref buf (the fixnum (+ start 1))) (ldb (byte 8 48) integer))
  (setf (aref buf (the fixnum (+ start 2))) (ldb (byte 8 40) integer))
  (setf (aref buf (the fixnum (+ start 3))) (ldb (byte 8 32) integer))
  (setf (aref buf (the fixnum (+ start 4))) (ldb (byte 8 24) integer))
  (setf (aref buf (the fixnum (+ start 5))) (ldb (byte 8 16) integer))
  (setf (aref buf (the fixnum (+ start 6))) (ldb (byte 8 8) integer))
  (setf (aref buf (the fixnum (+ start 7))) (ldb (byte 8 0) integer)))

(declaim (ftype (function (byte-vector fixnum (signed-byte 64)) (signed-byte 64)) blodwen-buffer-setint))
(defun blodwen-buffer-setint (buf loc val)
  (declare (optimize speed (safety 0) (debug 1))
           (type byte-vector buf)
           (type fixnum loc)
           (type (signed-byte 64) val))
  (write-8-bytes buf loc
                 (ldb (byte 64 0) val))
  val)

(declaim (inline read-4-bytes)
         (ftype (function (byte-vector fixnum) (unsigned-byte 32)) read-4-bytes))
(defun read-4-bytes (buf start)
  (declare (optimize speed (safety 0) (debug 1))
           (type byte-vector buf)
           (type fixnum start))
  (let ((1-byte (aref buf start))
        (2-byte (aref buf (the fixnum (+ start 1))))
        (3-byte (aref buf (the fixnum (+ start 2))))
        (4-byte (aref buf (the fixnum (+ start 3)))))
    (declare (type (unsigned-byte 8) 1-byte 2-byte 3-byte 4-byte))
    (logior (the (unsigned-byte 32) (ash 1-byte 24))
            (the (unsigned-byte 24) (ash 2-byte 16))
            (the (unsigned-byte 16) (ash 3-byte 8))
            4-byte)))

(declaim (inline read-8-bytes)
         (ftype (function (byte-vector fixnum) (unsigned-byte 64)) read-8-bytes))
(defun read-8-bytes (buf start)
  (declare (optimize speed (safety 0) (debug 1))
           (type byte-vector buf)
           (type fixnum start))
  (logior (ash (read-4-bytes buf start) 32)
          (read-4-bytes buf (the fixnum (+ start 4)))))

(declaim (ftype (function (byte-vector fixnum) (signed-byte 64)) blodwen-buffer-getint))
(defun blodwen-buffer-getint (buf loc)
  (declare (optimize speed (safety 0) (debug 1))
           (type byte-vector buf)
           (type fixnum loc))
  (let ((byte
          (read-8-bytes buf loc)))
    (declare (type (unsigned-byte 64) byte))
    (logior byte (- (mask-field (byte 1 63) byte)))))

(declaim (ftype (function (double-float) (unsigned-byte 64)) encode-float64))
(defun encode-float64 (float)
  (declare (optimize speed (safety 0) (debug 1) (float 0))
           (type double-float float))
  (multiple-value-bind (sign significand exponent)
      (multiple-value-bind (significand exponent sign)
          (decode-float float)
        (let ((exponent
                (if (= 0 significand)
                    exponent
                    (+ (1- exponent) 1023)))
              (sign (if (= sign 1.0) 0 1)))
          (unless (< exponent 2048)
            (error "Floating point overflow when encoding ~S." float))
          (if (<= exponent 0)
              (values sign
                      (ash (round (* 4503599627370496
                                     significand))
                           exponent)
                      0)
              (values sign
                      (round (* 4503599627370496
                                (1- (* significand 2))))
                      exponent))))
    (let ((bits 0))
      (declare (type (unsigned-byte 64) bits))
      (setf (ldb (byte 1 63) bits) sign
            (ldb (byte 11 52) bits) exponent
            (ldb (byte 52 0) bits) significand)
      bits)))

(declaim (ftype (function ((unsigned-byte 64)) double-float) decode-float64))
(defun decode-float64 (bits)
  (declare (optimize speed (safety 0) (debug 1) (float 0))
           (type (unsigned-byte 64) bits))
  (let ((sign (ldb (byte 1 63) bits))
        (exponent (ldb (byte 11 52) bits))
        (significand (ldb (byte 52 0) bits)))
    (if (zerop exponent)
        (setf exponent 1)
        (setf (ldb (byte 1 52) significand) 1))
    (let ((float-significand (float significand 1.0d0)))
      (scale-float (if (zerop sign)
                       float-significand
                       (- float-significand))
                   (- exponent 1075)))))

(declaim (ftype (function (byte-vector fixnum double-float) double-float) blodwen-buffer-setdouble))
(defun blodwen-buffer-setdouble (buf loc val)
  (declare (optimize speed (safety 0) (debug 1))
           (type byte-vector buf)
           (type fixnum loc)
           (type double-float val))
  (write-8-bytes buf loc (encode-float64 val))
  val)

(declaim (ftype (function (byte-vector fixnum) double-float) blodwen-buffer-getdouble))
(defun blodwen-buffer-getdouble (buf loc)
  (declare (optimize speed (safety 0) (debug 1))
           (type byte-vector buf)
           (type fixnum loc))
  (decode-float64 (read-8-bytes buf loc)))

(declaim (ftype (function (byte-vector fixnum string) string) blodwen-buffer-setstring))
(defun blodwen-buffer-setstring (buf loc val)
  (declare (optimize speed (safety 0) (debug 1))
           (type byte-vector buf)
           (type fixnum loc)
           (type string val))
  (let ((vec (ef:encode-lisp-string val :utf-8)))
    (replace buf vec :start1 loc :end2 (length vec))
    val))

(declaim (ftype (function (byte-vector fixnum fixnum) string) blodwen-buffer-getstring))
(defun blodwen-buffer-getstring (buf loc len)
  (declare (optimize speed (safety 0) (debug 1))
           (type byte-vector buf)
           (type fixnum loc len))
  (ef:decode-external-string buf :utf-8
                             :start loc
                             :end (the fixnum (+ loc len))))

(declaim (ftype (function (stream byte-vector fixnum fixnum) byte-vector) blodwen-readbuffer))
(defun blodwen-readbuffer (h buf loc max)
  (declare (optimize speed (safety 0) (debug 1))
           (type byte-vector buf)
           (type fixnum loc max))
  (read-sequence buf h :start loc :end (the fixnum (+ loc max)))
  buf)

(declaim (ftype (function (stream byte-vector fixnum fixnum) string) blodwen-writebuffer))
(defun blodwen-writebuffer (h buf loc max)
  (declare (optimize speed (safety 0) (debug 1))
           (type byte-vector buf)
           (type fixnum loc max))
  (write-sequence buf h :start loc :end (the fixnum (+ loc max))))

;;; I/O

(define-condition file-op-error (file-error)
  ((error-type :reader file-op-error-type
               :initarg :type
               :initform nil)))

(defun file-op-error (type)
  (error 'file-op-error :type type))

(defun blodwen-error-code (c)
  (case (file-op-error-type c)
    (read-error 1)
    (write-error 2)
    (file-does-not-exist-error 3)
    (file-protection-error 4)
    (otherwise 5)))

;; If the file operation raises an error, catch it and return an appropriate error code
(defun blodwen-file-op (op)
  (handler-case
      (either-right (funcall op))
    (error (c)
      (either-left (blodwen-error-code c)))))

(defun blodwen-open-stream (filename mode bin)
  (let ((args
          (if (= bin 1)
              (list :element-type '(unsigned-byte 8))
              (list :element-type 'character
                    :external-format :utf-8))))
    (cond ((string= "r" mode)
           (setq args
                 (append args
                         (list :direction :input))))
          ((string= "w" mode)
           (setq args
                 (append args
                         (list :direction :output
                               :if-exists :supersede
                               :if-does-not-exist :create))))
          ((string= "wx" mode)
           (setq args
                 (append args
                         (list :direction :output
                               :if-exists :supersede
                               :if-does-not-exist :create))))
          ((string= "a" mode)
           (setq args
                 (append args
                         (list :direction :output
                               :if-exists :append
                               :if-does-not-exist :create))))
          ((string= "r+" mode)
           (setq args
                 (append args
                         (list :direction :io))))
          ((string= "w+" mode)
           (setq args
                 (append args
                         (list :direction :io
                               :if-exists :supersede
                               :if-does-not-exist :create))))
          ((string= "w+x" mode)
           (setq args
                 (append args
                         (list :direction :io
                               :if-exists :supersede
                               :if-does-not-exist :create))))
          ((string= "a+" mode)
           (setq args
                 (append args
                         (list :direction :io
                               :if-exists :append
                               :if-does-not-exist :create))))
          (t
           (file-op-error 'unsupported-error)))
    (handler-case
        (apply #'open filename args)
      (file-error ()
        (if (member mode '("r" "r+") :test #'string=)
            (file-op-error 'file-does-not-exist-error)
            (file-op-error 'file-protection-error)))
      (error ()
        (file-op-error 'other-error)))))

(defun blodwen-close-stream (s)
  (when (streamp s)
    (close s)))

(defun blodwen-putstring (s str)
  (when (streamp s)
    (handler-case
        (write-string str s)
      (error ()
        (file-op-error 'write-error))))
  0)

(defun blodwen-get-line (s)
  (if (streamp s)
      (handler-case
          (let ((str (read-line s nil 'eof)))
            (if (eq 'eof str)
                ""
                str))
        (error ()
          (file-op-error 'read-error)))
      ""))

(defun blodwen-eof (s)
  (if (eq 'eof (peek-char nil s nil 'eof)) 1 0))

;;; Threads

(defun blodwen-thread (p)
  (mp:process-run-function (format nil "Blodwen ~A" p) () p (vector 0)))

(defun blodwen-get-thread-data ()
  (mp:process-private-property :blodwen-thread-data))

(defun blodwen-set-thread-data (a)
  (setf (mp:process-private-property :blodwen-thread-data) a))

(defun blodwen-mutex ()
  (mp:make-lock))

(defun blodwen-lock (m)
  (mp:process-lock m))

(defun blodwen-unlock (m)
  (mp:process-unlock m))

(defun blodwen-thisthread ()
  (sys:current-thread-unique-id))

(defun blodwen-condition ()
  (mp:make-condition-variable))

(defun blodwen-condition-wait (c m)
  (mp:condition-variable-wait c m))

(defun blodwen-condition-wait-timeout (c m tm)
  (mp:condition-variable-wait c m :timeout tm))

(defun blodwen-condition-signal (c)
  (mp:condition-variable-signal c))

(defun blodwen-condition-broadcast (c)
  (mp:condition-variable-broadcast c))

(defun blodwen-sleep (s)
  (sleep s))