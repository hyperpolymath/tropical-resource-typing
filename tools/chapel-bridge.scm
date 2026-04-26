;;; SPDX-License-Identifier: PMPL-1.0-or-later
;;; Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
;;;
;;; chapel-bridge.scm — lazy Chapel inclusion gate.
;;;
;;; ## Purpose
;;;
;;; Chapel is OPTIONAL for tropical-resource-typing (cap:chapel-2 is
;;; declared optional in coordination.k9). Only proofs in
;;; proofs/parallel-tropical/ depend on Chapel-backed mechanical
;;; helpers. The standard Isabelle build of Tropical_Semirings must
;;; succeed whether Chapel is present or absent.
;;;
;;; This file is the discovery + gating layer. It exposes:
;;;
;;;   (chapel-available?)         -> #t | #f
;;;   (chapel-version)            -> string | 'absent
;;;   (with-chapel body ...)      -> evaluates body when present, else
;;;                                  warns and returns 'chapel-unavailable
;;;
;;; ## Today's state (2026-04-26)
;;;
;;; - `which chpl` empty on this host.
;;; - `guix install chapel` returns 'unknown package'.
;;; - `dnf search chapel` only finds python3-sphinxcontrib-chapeldomain.
;;; - Chapel DOES ship official Fedora 42/43 RPMs upstream
;;;   (chapel-lang.org/install.html); rpm-ostree layering deferred
;;;   for now because Chapel is not on this session's critical path.
;;; - Guile is NOT currently installed on the build host either.
;;;   The canonical bridge logic lives here in Scheme; the runtime
;;;   capability check that the standard build actually consults is
;;;   the sibling `tools/check-chapel-bridge.sh` (Bash) — it implements
;;;   the same chpl-on-PATH detection without a Guile dependency.
;;;   Once Guile lands, this file becomes the executable canonical
;;;   loader and the Bash sibling becomes its mirror.
;;; - No proofs/parallel-tropical/ subdirectory exists yet.

(define-module (tools chapel-bridge)
  #:use-module (ice-9 popen)
  #:use-module (ice-9 rdelim)
  #:export (chapel-available?
            chapel-version
            with-chapel))

(define (run-and-capture cmd)
  "Run CMD via the shell, return its stdout as a string (newline-stripped),
   or #f on non-zero exit."
  (let* ((port (open-input-pipe cmd))
         (out  (read-line port)))
    (let ((status (close-pipe port)))
      (if (and (zero? status) (string? out))
          out
          #f))))

(define (chapel-available?)
  "Return #t iff the `chpl` compiler is on PATH and reports a version."
  (let ((v (run-and-capture "command -v chpl >/dev/null 2>&1 && \
                             chpl --version 2>/dev/null | head -1")))
    (and v (not (string-null? v)))))

(define (chapel-version)
  "Return the Chapel version string, or 'absent if not present."
  (let ((v (run-and-capture "chpl --version 2>/dev/null | head -1")))
    (if (and v (not (string-null? v))) v 'absent)))

(define-syntax with-chapel
  (syntax-rules ()
    "Evaluate BODY only if Chapel is available. If absent, print a one-line
     warning to (current-error-port) and return the symbol
     'chapel-unavailable. Callers SHOULD branch on the return value rather
     than treat it as success."
    ((_ body ...)
     (if (chapel-available?)
         (begin body ...)
         (begin
           (display "[chapel-bridge] chapel disabled — `chpl` not on PATH; \
proof family deferred. (cap:chapel-2 is optional per coordination.k9)\n"
                    (current-error-port))
           'chapel-unavailable)))))

;;; Smoke check — invoke this file directly to print the gate's view of
;;; the world:
;;;   guile -L tools -e '((@ (tools chapel-bridge) main))' tools/chapel-bridge.scm
(define (main . _)
  (format #t "chapel-available? ~a~%" (chapel-available?))
  (format #t "chapel-version    ~a~%" (chapel-version))
  (with-chapel
    (format #t "(would dispatch parallel-tropical proofs here)~%")))
