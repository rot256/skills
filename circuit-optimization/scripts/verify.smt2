(set-option :incremental true)
(set-logic QF_FF)
(define-sort F () (_ FiniteField 21888242871839275222246405745257275088548364400416034343698204186575808495617))
;; BN254 scalar field. Swap in your circuit's prime to get a theorem about THAT field.
;;
;; PROVE a candidate single-constraint gadget forces o = target on the boolean cube,
;; AND that the premise is non-vacuous. Run directly:  cvc5 scripts/verify.smt2
;;
;;   forces:   unsat of (bits & row & o != target)  =>  the row pins o to target
;;   non-vac:  sat   of (bits & row & o  = target)   =>  the honest o actually satisfies
;;             the row (so the unsat above is a real proof, not an empty one)
;;
;; Over QF_FF this is a genuine F_p statement: the multiplier R need not be argued a
;; unit "over the reals" -- cvc5 reasons in the field directly. (The encodings below
;; happen to keep R in {+-1..+-4}, so they also hold in any field of char > 3.)

(declare-const a F)
(declare-const b F)
(declare-const c F)
(declare-const o F)

; inputs are bits (shared by every query below)
(assert (or (= a (as ff0 F)) (= a (as ff1 F))))
(assert (or (= b (as ff0 F)) (= b (as ff1 F))))
(assert (or (= c (as ff0 F)) (= c (as ff1 F))))

;; ===== XOR3 =====================================================================
;; row:    (o + 2a + 2b + 7c)(a + b - 4c + 1) = 6a + 6b - 24c
;; target: o = parity(a,b,c) = a + b + c - 2ab - 2bc - 2ca + 4abc
(echo "XOR3 forces o=parity       (expect unsat):")
(push 1)
  (assert (= (ff.add
               (ff.mul (ff.add o (ff.mul (as ff2 F) a) (ff.mul (as ff2 F) b) (ff.mul (as ff7 F) c))
                       (ff.add a b (as ff1 F) (ff.mul (as ff-4 F) c)))
               (ff.mul (as ff-6 F) a) (ff.mul (as ff-6 F) b) (ff.mul (as ff24 F) c))
             (as ff0 F)))
  (assert (not (= o (ff.add a b c
                       (ff.mul (as ff-2 F) a b) (ff.mul (as ff-2 F) b c) (ff.mul (as ff-2 F) a c)
                       (ff.mul (as ff4 F) a b c)))))
  (check-sat)
(pop 1)
(echo "XOR3 premise non-vacuous   (expect sat):")
(push 1)
  (assert (= (ff.add
               (ff.mul (ff.add o (ff.mul (as ff2 F) a) (ff.mul (as ff2 F) b) (ff.mul (as ff7 F) c))
                       (ff.add a b (as ff1 F) (ff.mul (as ff-4 F) c)))
               (ff.mul (as ff-6 F) a) (ff.mul (as ff-6 F) b) (ff.mul (as ff24 F) c))
             (as ff0 F)))
  (assert (= o (ff.add a b c
                       (ff.mul (as ff-2 F) a b) (ff.mul (as ff-2 F) b c) (ff.mul (as ff-2 F) a c)
                       (ff.mul (as ff4 F) a b c))))
  (check-sat)
(pop 1)

;; ===== Maj ======================================================================
;; row:    (o + a + b - 9c + 3)(a + b + 6c - 4) + 12 = 0
;; target: o = maj(a,b,c) = ab + bc + ca - 2abc
(echo "Maj  forces o=maj          (expect unsat):")
(push 1)
  (assert (= (ff.add
               (ff.mul (ff.add o a b (ff.mul (as ff-9 F) c) (as ff3 F))
                       (ff.add a b (ff.mul (as ff6 F) c) (as ff-4 F)))
               (as ff12 F))
             (as ff0 F)))
  (assert (not (= o (ff.add (ff.mul a b) (ff.mul b c) (ff.mul a c) (ff.mul (as ff-2 F) a b c)))))
  (check-sat)
(pop 1)
(echo "Maj  premise non-vacuous   (expect sat):")
(push 1)
  (assert (= (ff.add
               (ff.mul (ff.add o a b (ff.mul (as ff-9 F) c) (as ff3 F))
                       (ff.add a b (ff.mul (as ff6 F) c) (as ff-4 F)))
               (as ff12 F))
             (as ff0 F)))
  (assert (= o (ff.add (ff.mul a b) (ff.mul b c) (ff.mul a c) (ff.mul (as ff-2 F) a b c))))
  (check-sat)
(pop 1)
