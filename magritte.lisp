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
;; * Macros that expand as late as possible
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

(defn (lookup-or-nil name env)
  (handler-case
   (lookup-variable name env)
   (no-such-binding (e) nil)))

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
  (fn (values &key (bindings nil))
    (evaluate-progn body (extend-env env
                                     (append (mapcar #'car bindings) args)
                                     (append (mapcar #'cdr bindings) values)))))

(define-condition no-matching-function ()
  ((args :initarg :args :reader args)))

(defn (special-symbol? sym)
  (or (eq sym 'true)
      (eq sym 'false)
      (eq sym 'nil)))

(defn (variable? pattern)
  (and (symbolp pattern)
       (not (special-symbol? pattern))))

(defn (match-variable var input bindings)
  (if-let ((binding (assoc var bindings)))
    (if (equal input (cdr binding))
        bindings
      nil)
    (cons (cons var input) bindings)))

(defparameter no-bindings '((True . True)))

(defn (match? pattern input &optional (bindings no-bindings))
  (cond ((equal bindings nil) nil)
        ((variable? pattern) (match-variable pattern input bindings))
        ((eql pattern input) bindings)
        ((and (consp pattern) (consp input)) (match? (cdr pattern)
                                                     (cdr input)
                                                     (match? (car pattern)
                                                             (car input)
                                                             bindings)))
        (t nil)))

(defn (invoke fn-list arguments)
  (if (functionp fn-list)
      (funcall fn-list arguments)
    (if-let ((func (last (mapcan (fn (fn-binding)
                                     (if-let ((bindings (match? (car fn-binding)
                                                                arguments)))
                                         (list (cons bindings (cdr fn-binding)))))
                                 fn-list))))
        (funcall (cdar func) arguments :bindings (caar func))
      (error 'no-matching-function :args arguments))))

(defn (define-function name args body env)
  (if-let ((fn-bindings (lookup-or-nil name env)))
      (set-variable! name
                     (cons (cons args (make-fn args body env))
                           fn-bindings)
                     env)
    (define-variable name (list (cons args (make-fn args body env))) env)))

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

(def *the-false-value* (make-bool :val nil))
(def *the-true-value* (make-bool :val t))

;; TODO: allow generic versions via pattern-matching/guards
(defn (to-bool obj)
  (if (or (equal obj nil)
          (equal obj *the-false-value*))
      *the-false-value*
    *the-true-value*))

;; *The* evaluator

(defn (evaluate expr env)
  (cond ((null expr) nil)
        ((atom? expr) (cond ((symbolp expr) (lookup-variable expr env))
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
                        (defn (define-function (caadr expr)
                                               (cdadr expr)
                                               (cddr expr)
                                               env))
                        (if (if (not (equal (to-bool (evaluate (cadr expr) env))
                                            *the-false-value*))
                                (evaluate (caddr expr) env)
                              (if (not (null (cdddr expr)))
                                  (evaluate (cadddr expr) env)
                                *the-false-value*)))
                        (otherwise (invoke (evaluate (car expr) env)
                                           (evaluate-list (cdr expr) env)))))
        (else (error 'bad-input :expr expr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Initial environment
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def *global-env* (make-hash-table :test 'equal))
(defmacro definitial (name val)
  `(setf (gethash ',name *global-env*) ,val))

(defmacro defprimitive (name primitive-fn)
  `(setf (gethash ',name *global-env*)
         (fn (values)
             (apply #',primitive-fn values))))

(definitial True *the-true-value*)
(definitial False *the-false-value*)
(definitial nil nil)

(defprimitive + +)
(defprimitive - -)
(defprimitive * *)
(defprimitive / /)
(defprimitive car car)
(defprimitive cdr cdr)
(defprimitive cons cons)
(defprimitive evaluate evaluate)
(defprimitive read read)
(defprimitive print print)
(defprimitive eq? equal)
(defprimitive not not)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; REPL
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn (magritte-repl &optional (in *standard-input*) (out *standard-output*))
  (format out "magritte> ")
  (let ((expr (read in)))
    (format out "~S" (evaluate expr *global-env*)))
  (format out "~&")
  (magritte-repl in out))