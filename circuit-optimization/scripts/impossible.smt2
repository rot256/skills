(set-option :incremental true)
(set-logic QF_FF)
(define-sort F () (_ FiniteField 21888242871839275222246405745257275088548364400416034343698204186575808495617))
;; BN254 scalar field. Swap in your circuit's prime for a theorem about THAT field.
;;
;; Claim: NO single rank-1 row of the shape  (o + A)*R = O  -- A,R,O affine in the
;; input bits, R a UNIT on the cube -- computes AND3 or OR3. Unknowns are the 12
;; coefficients; the 8 cube points are constants with o := f(point) plugged in.
;; unsat  =>  no such encoding exists over THIS field (a real F_p theorem, not a
;; characteristic-0 / reals argument).

(declare-const a0 F)(declare-const a1 F)(declare-const a2 F)(declare-const ac F) ; A(x)=a0 x0+a1 x1+a2 x2+ac
(declare-const b0 F)(declare-const b1 F)(declare-const b2 F)(declare-const bc F) ; R(x), the o-multiplier
(declare-const c0 F)(declare-const c1 F)(declare-const c2 F)(declare-const cc F) ; O(x)

(echo "AND3 has no single-constraint (o+A)*R=O encoding  (expect unsat):")
(push 1)
  (assert (= (ff.mul (ff.add (as ff0 F) (ff.add (ff.mul a0 (as ff0 F)) (ff.mul a1 (as ff0 F)) (ff.mul a2 (as ff0 F)) ac)) (ff.add (ff.mul b0 (as ff0 F)) (ff.mul b1 (as ff0 F)) (ff.mul b2 (as ff0 F)) bc)) (ff.add (ff.mul c0 (as ff0 F)) (ff.mul c1 (as ff0 F)) (ff.mul c2 (as ff0 F)) cc)))   ; point (0,0,0), o=0
  (assert (not (= (ff.add (ff.mul b0 (as ff0 F)) (ff.mul b1 (as ff0 F)) (ff.mul b2 (as ff0 F)) bc) (as ff0 F))))                      ; R a unit here
  (assert (= (ff.mul (ff.add (as ff0 F) (ff.add (ff.mul a0 (as ff0 F)) (ff.mul a1 (as ff0 F)) (ff.mul a2 (as ff1 F)) ac)) (ff.add (ff.mul b0 (as ff0 F)) (ff.mul b1 (as ff0 F)) (ff.mul b2 (as ff1 F)) bc)) (ff.add (ff.mul c0 (as ff0 F)) (ff.mul c1 (as ff0 F)) (ff.mul c2 (as ff1 F)) cc)))   ; point (0,0,1), o=0
  (assert (not (= (ff.add (ff.mul b0 (as ff0 F)) (ff.mul b1 (as ff0 F)) (ff.mul b2 (as ff1 F)) bc) (as ff0 F))))                      ; R a unit here
  (assert (= (ff.mul (ff.add (as ff0 F) (ff.add (ff.mul a0 (as ff0 F)) (ff.mul a1 (as ff1 F)) (ff.mul a2 (as ff0 F)) ac)) (ff.add (ff.mul b0 (as ff0 F)) (ff.mul b1 (as ff1 F)) (ff.mul b2 (as ff0 F)) bc)) (ff.add (ff.mul c0 (as ff0 F)) (ff.mul c1 (as ff1 F)) (ff.mul c2 (as ff0 F)) cc)))   ; point (0,1,0), o=0
  (assert (not (= (ff.add (ff.mul b0 (as ff0 F)) (ff.mul b1 (as ff1 F)) (ff.mul b2 (as ff0 F)) bc) (as ff0 F))))                      ; R a unit here
  (assert (= (ff.mul (ff.add (as ff0 F) (ff.add (ff.mul a0 (as ff0 F)) (ff.mul a1 (as ff1 F)) (ff.mul a2 (as ff1 F)) ac)) (ff.add (ff.mul b0 (as ff0 F)) (ff.mul b1 (as ff1 F)) (ff.mul b2 (as ff1 F)) bc)) (ff.add (ff.mul c0 (as ff0 F)) (ff.mul c1 (as ff1 F)) (ff.mul c2 (as ff1 F)) cc)))   ; point (0,1,1), o=0
  (assert (not (= (ff.add (ff.mul b0 (as ff0 F)) (ff.mul b1 (as ff1 F)) (ff.mul b2 (as ff1 F)) bc) (as ff0 F))))                      ; R a unit here
  (assert (= (ff.mul (ff.add (as ff0 F) (ff.add (ff.mul a0 (as ff1 F)) (ff.mul a1 (as ff0 F)) (ff.mul a2 (as ff0 F)) ac)) (ff.add (ff.mul b0 (as ff1 F)) (ff.mul b1 (as ff0 F)) (ff.mul b2 (as ff0 F)) bc)) (ff.add (ff.mul c0 (as ff1 F)) (ff.mul c1 (as ff0 F)) (ff.mul c2 (as ff0 F)) cc)))   ; point (1,0,0), o=0
  (assert (not (= (ff.add (ff.mul b0 (as ff1 F)) (ff.mul b1 (as ff0 F)) (ff.mul b2 (as ff0 F)) bc) (as ff0 F))))                      ; R a unit here
  (assert (= (ff.mul (ff.add (as ff0 F) (ff.add (ff.mul a0 (as ff1 F)) (ff.mul a1 (as ff0 F)) (ff.mul a2 (as ff1 F)) ac)) (ff.add (ff.mul b0 (as ff1 F)) (ff.mul b1 (as ff0 F)) (ff.mul b2 (as ff1 F)) bc)) (ff.add (ff.mul c0 (as ff1 F)) (ff.mul c1 (as ff0 F)) (ff.mul c2 (as ff1 F)) cc)))   ; point (1,0,1), o=0
  (assert (not (= (ff.add (ff.mul b0 (as ff1 F)) (ff.mul b1 (as ff0 F)) (ff.mul b2 (as ff1 F)) bc) (as ff0 F))))                      ; R a unit here
  (assert (= (ff.mul (ff.add (as ff0 F) (ff.add (ff.mul a0 (as ff1 F)) (ff.mul a1 (as ff1 F)) (ff.mul a2 (as ff0 F)) ac)) (ff.add (ff.mul b0 (as ff1 F)) (ff.mul b1 (as ff1 F)) (ff.mul b2 (as ff0 F)) bc)) (ff.add (ff.mul c0 (as ff1 F)) (ff.mul c1 (as ff1 F)) (ff.mul c2 (as ff0 F)) cc)))   ; point (1,1,0), o=0
  (assert (not (= (ff.add (ff.mul b0 (as ff1 F)) (ff.mul b1 (as ff1 F)) (ff.mul b2 (as ff0 F)) bc) (as ff0 F))))                      ; R a unit here
  (assert (= (ff.mul (ff.add (as ff1 F) (ff.add (ff.mul a0 (as ff1 F)) (ff.mul a1 (as ff1 F)) (ff.mul a2 (as ff1 F)) ac)) (ff.add (ff.mul b0 (as ff1 F)) (ff.mul b1 (as ff1 F)) (ff.mul b2 (as ff1 F)) bc)) (ff.add (ff.mul c0 (as ff1 F)) (ff.mul c1 (as ff1 F)) (ff.mul c2 (as ff1 F)) cc)))   ; point (1,1,1), o=1
  (assert (not (= (ff.add (ff.mul b0 (as ff1 F)) (ff.mul b1 (as ff1 F)) (ff.mul b2 (as ff1 F)) bc) (as ff0 F))))                      ; R a unit here
  (check-sat)
(pop 1)

(echo "OR3 has no single-constraint (o+A)*R=O encoding  (expect unsat):")
(push 1)
  (assert (= (ff.mul (ff.add (as ff0 F) (ff.add (ff.mul a0 (as ff0 F)) (ff.mul a1 (as ff0 F)) (ff.mul a2 (as ff0 F)) ac)) (ff.add (ff.mul b0 (as ff0 F)) (ff.mul b1 (as ff0 F)) (ff.mul b2 (as ff0 F)) bc)) (ff.add (ff.mul c0 (as ff0 F)) (ff.mul c1 (as ff0 F)) (ff.mul c2 (as ff0 F)) cc)))   ; point (0,0,0), o=0
  (assert (not (= (ff.add (ff.mul b0 (as ff0 F)) (ff.mul b1 (as ff0 F)) (ff.mul b2 (as ff0 F)) bc) (as ff0 F))))                      ; R a unit here
  (assert (= (ff.mul (ff.add (as ff1 F) (ff.add (ff.mul a0 (as ff0 F)) (ff.mul a1 (as ff0 F)) (ff.mul a2 (as ff1 F)) ac)) (ff.add (ff.mul b0 (as ff0 F)) (ff.mul b1 (as ff0 F)) (ff.mul b2 (as ff1 F)) bc)) (ff.add (ff.mul c0 (as ff0 F)) (ff.mul c1 (as ff0 F)) (ff.mul c2 (as ff1 F)) cc)))   ; point (0,0,1), o=1
  (assert (not (= (ff.add (ff.mul b0 (as ff0 F)) (ff.mul b1 (as ff0 F)) (ff.mul b2 (as ff1 F)) bc) (as ff0 F))))                      ; R a unit here
  (assert (= (ff.mul (ff.add (as ff1 F) (ff.add (ff.mul a0 (as ff0 F)) (ff.mul a1 (as ff1 F)) (ff.mul a2 (as ff0 F)) ac)) (ff.add (ff.mul b0 (as ff0 F)) (ff.mul b1 (as ff1 F)) (ff.mul b2 (as ff0 F)) bc)) (ff.add (ff.mul c0 (as ff0 F)) (ff.mul c1 (as ff1 F)) (ff.mul c2 (as ff0 F)) cc)))   ; point (0,1,0), o=1
  (assert (not (= (ff.add (ff.mul b0 (as ff0 F)) (ff.mul b1 (as ff1 F)) (ff.mul b2 (as ff0 F)) bc) (as ff0 F))))                      ; R a unit here
  (assert (= (ff.mul (ff.add (as ff1 F) (ff.add (ff.mul a0 (as ff0 F)) (ff.mul a1 (as ff1 F)) (ff.mul a2 (as ff1 F)) ac)) (ff.add (ff.mul b0 (as ff0 F)) (ff.mul b1 (as ff1 F)) (ff.mul b2 (as ff1 F)) bc)) (ff.add (ff.mul c0 (as ff0 F)) (ff.mul c1 (as ff1 F)) (ff.mul c2 (as ff1 F)) cc)))   ; point (0,1,1), o=1
  (assert (not (= (ff.add (ff.mul b0 (as ff0 F)) (ff.mul b1 (as ff1 F)) (ff.mul b2 (as ff1 F)) bc) (as ff0 F))))                      ; R a unit here
  (assert (= (ff.mul (ff.add (as ff1 F) (ff.add (ff.mul a0 (as ff1 F)) (ff.mul a1 (as ff0 F)) (ff.mul a2 (as ff0 F)) ac)) (ff.add (ff.mul b0 (as ff1 F)) (ff.mul b1 (as ff0 F)) (ff.mul b2 (as ff0 F)) bc)) (ff.add (ff.mul c0 (as ff1 F)) (ff.mul c1 (as ff0 F)) (ff.mul c2 (as ff0 F)) cc)))   ; point (1,0,0), o=1
  (assert (not (= (ff.add (ff.mul b0 (as ff1 F)) (ff.mul b1 (as ff0 F)) (ff.mul b2 (as ff0 F)) bc) (as ff0 F))))                      ; R a unit here
  (assert (= (ff.mul (ff.add (as ff1 F) (ff.add (ff.mul a0 (as ff1 F)) (ff.mul a1 (as ff0 F)) (ff.mul a2 (as ff1 F)) ac)) (ff.add (ff.mul b0 (as ff1 F)) (ff.mul b1 (as ff0 F)) (ff.mul b2 (as ff1 F)) bc)) (ff.add (ff.mul c0 (as ff1 F)) (ff.mul c1 (as ff0 F)) (ff.mul c2 (as ff1 F)) cc)))   ; point (1,0,1), o=1
  (assert (not (= (ff.add (ff.mul b0 (as ff1 F)) (ff.mul b1 (as ff0 F)) (ff.mul b2 (as ff1 F)) bc) (as ff0 F))))                      ; R a unit here
  (assert (= (ff.mul (ff.add (as ff1 F) (ff.add (ff.mul a0 (as ff1 F)) (ff.mul a1 (as ff1 F)) (ff.mul a2 (as ff0 F)) ac)) (ff.add (ff.mul b0 (as ff1 F)) (ff.mul b1 (as ff1 F)) (ff.mul b2 (as ff0 F)) bc)) (ff.add (ff.mul c0 (as ff1 F)) (ff.mul c1 (as ff1 F)) (ff.mul c2 (as ff0 F)) cc)))   ; point (1,1,0), o=1
  (assert (not (= (ff.add (ff.mul b0 (as ff1 F)) (ff.mul b1 (as ff1 F)) (ff.mul b2 (as ff0 F)) bc) (as ff0 F))))                      ; R a unit here
  (assert (= (ff.mul (ff.add (as ff1 F) (ff.add (ff.mul a0 (as ff1 F)) (ff.mul a1 (as ff1 F)) (ff.mul a2 (as ff1 F)) ac)) (ff.add (ff.mul b0 (as ff1 F)) (ff.mul b1 (as ff1 F)) (ff.mul b2 (as ff1 F)) bc)) (ff.add (ff.mul c0 (as ff1 F)) (ff.mul c1 (as ff1 F)) (ff.mul c2 (as ff1 F)) cc)))   ; point (1,1,1), o=1
  (assert (not (= (ff.add (ff.mul b0 (as ff1 F)) (ff.mul b1 (as ff1 F)) (ff.mul b2 (as ff1 F)) bc) (as ff0 F))))                      ; R a unit here
  (check-sat)
(pop 1)
