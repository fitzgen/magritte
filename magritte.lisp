;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; IDEAS
;;
;; * expose environment + methods for getting/setting
;; * generic functions via pattern matching and guards
;;   - for all coercion: (defn (to-bool obj :where (is-foo? obj)) ...)
;;   - operator overloading
;;   - pretty printing
;;   - etc. sort of like Python's __iter__, __str__, __nonzero__, etc
;; * Algebraic Data Types
;; * Keyword arguments (maybe)
;; * Automatically curry functions?
;; * After a working interpreter, compile to CL and rewrite Magritte in Magritte
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Globals
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *parent-environment-key* (gensym))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Utilities
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Simple macros to make the appearance more similar to what I like.

(defmacro fn (lambda-list &body body)
  `(lambda ,lambda-list
     ,@body))

(defmacro defn ((name &rest args) &body body)
  `(defun ,name ,args ,@body))

(defmacro def (name val)
  `(progn
     (defparameter ,name ,val)
     ,val))

(defmacro if-let (bindings then-form &optional (else-form nil))
  (let ((let-vars (cons 'list (mapcar #'car bindings))))
    `(let ,bindings
       (if (every #'I ,let-vars)
           ,then-form
         ,else-form))))

(defn (I obj)
  obj)

(defconstant else t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Variables and environments
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: default, global environment

(define-condition no-such-binding ()
  ((var-name :initarg :var-name :reader var-name)))

(define-condition binding-exists ()
  ((var-name :initarg :var-name :reader var-name)))

(defn (lookup-variable name env)
  (multiple-value-bind (binding exists?) (gethash name env)
    (if exists?
        binding
      (if-let ((parent-env (gethash *parent-environment-key* env)))
        (lookup-variable name parent-env)
        (error 'no-such-binding :var-name name)))))

(defn (set-variable! name val env)
  (multiple-value-bind (binding exists?) (gethash name env)
    (if exists?
        (setf (gethash name env) val)
      (error 'no-such-binding :var-name name))))

(defn (define-variable name val env)
  (multiple-value-bind (binding exists?) (gethash name env)
    (if exists?
        (error 'binding-exists :var-name name)
      (setf (gethash name env) val))))

(defn (extend-env env params values)
  (let ((new-env (make-hash-table)))
    (setf (gethash *parent-environment-key* new-env) env)
    (mapcar (fn (param val)
              (setf (gethash param new-env) val))
            params
            values)
    new-env))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Functions
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn (evaluate-progn forms env)
  (if-let ((result (last (mapcar (fn (form) (evaluate form env))
                                 forms))))
    (car result)))

(defn (make-fn args body env)
  (fn (values)
    (evaluate-progn body (extend-env env args values))))

(defn (invoke fn arguments)
  (funcall fn arguments))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Evaluation
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Booleans

(defn (print-bool bool stream k)
  (format stream (if (bool-val bool)
                     "True"
                   "False")))

(defstruct (bool (:constructor make-bool)
                 (:predicate bool?)
                 (:print-function print-bool))
  val)

;; Self evaluating structures

(defn (char? e)
  (typep e 'character))

(defn (self-evaluating? e)
  (or (numberp e)
      (stringp e)
      (null e)
      (bool? e)
      (char? e)))

(defn (atom? e)
  (not (or (null e)
           (listp e))))

(define-condition bad-input ()
  ((expr :initarg :expr :reader expr)))

(defn (evaluate-list list env)
  (mapcar (fn (arg) (evaluate arg env))
          list))

;; *The* evaluator

(defn (evaluate expr env)
  (cond ((atom? expr) (cond ((symbolp expr) (lookup-variable expr env))
                            ((self-evaluating? expr) expr)
                            (else (error 'bad-input :expr expr))))
        ((listp expr) (case (car expr)
                        (quote (cadr expr))
                        (def (define-variable (cadr expr)
                                              (evaluate (caddr expr) env)
                                              env))
                        (def* (define-variable (evaluate (cadr expr) env)
                                               (evaluate (caddr expr) env)
                                               env))
                        (set! (set-variable! (cadr expr)
                                             (evaluate (caddr expr) env)
                                             env))
                        (set*! (set-variable! (evaluate (cadr expr) env)
                                              (evaluate (caddr expr) env)
                                              env))
                        (fn (make-fn (cadr expr) (cddr expr) env))
                        (defn (define-variable (caadr expr)
                                               (make-fn (cdadr expr) (cddr expr) env)
                                               env))
                        (otherwise (invoke (evaluate (car expr) env)
                                           (evaluate-list (cdr expr) env)))))
        (else (error 'bad-input :expr expr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Initial environment
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *global-env* (make-hash-table))

(defmacro definitial (name val)
  `(setf (gethash ',name *global-env*) ,val))

(defmacro defprimitive (name primitive-fn)
  `(setf (gethash ',name *global-env*)
         (fn (values)
             (apply #',primitive-fn values))))

(definitial True (make-bool :val t))
(definitial False (make-bool :val nil))
(definitial nil nil)

(defprimitive + +)
(defprimitive - -)
(defprimitive * *)
(defprimitive / /)
(defprimitive car car)
(defprimitive cdr cdr)
(defprimitive evaluate evaluate)
(defprimitive read read)
(defprimitive print print)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; REPL
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn (magritte-repl)
  (format t "magritte> ")
  (let ((expr (read)))
    (format t "~S" (evaluate expr *global-env*)))
  (format t "~&")
  (magritte-repl))