#!/usr/bin/env sage
# Gröbner-basis tools for single-constraint gadgets.
#
#  1. PROVE a constraint forces o = target on the boolean cube (ideal membership).
#  2. FIND the cofactors for a Lean `linear_combination` / Coq `ring` soundness proof
#     (ideal "lift").  The cofactors below reproduce Clean/Gadgets/SHA256/CarrySave.lean.
#
# Why it works: over the cube, the boolean relations x_i^2 = x_i hold, i.e. we work
# modulo the ideal B = <x_i^2 - x_i>.  If  (o - target) * R - constraint  lies in B,
# then constraint = 0 (and R != 0) forces o = target.  `lift` expresses that element
# as  sum_i cofactor_i * (x_i^2 - x_i)  -- exactly the terms a `linear_combination`
# proof needs.  Run over QQ (integer cofactors lift to any field of char > small).

# --- concrete, tested instances (match CarrySave.lean exactly) -----------------
R.<o,a,b,c> = PolynomialRing(QQ, order='lex')
B = R.ideal(a^2 - a, b^2 - b, c^2 - c)

cube = [(av, bv, cv) for av in (0,1) for bv in (0,1) for cv in (0,1)]

def run(name, constraint, target, multiplier):
    GB = B.groebner_basis()
    # --- multiplier must be a UNIT on the cube; report excluded characteristics ----
    vals = sorted({ZZ(multiplier.subs(a=av, b=bv, c=cv)) for (av, bv, cv) in cube})
    assert 0 not in vals, f"{name}: multiplier vanishes on the cube at some point"
    excluded = sorted({p for v in vals if v != 0 for p in v.abs().prime_factors()})
    # --- soundness: (o - target)*mult - constraint in <x_i^2 - x_i> ----------------
    P = (o - target) * multiplier
    s_diff = P - constraint
    assert s_diff.reduce(GB) == 0, f"{name}: constraint does NOT force o = target"
    s_cof = s_diff.lift(B)
    assert constraint + sum(g*gn for g, gn in zip(s_cof, B.gens())) == P
    # --- completeness: constraint with o := target reduces to 0 on the cube --------
    comp = constraint.subs(o=target)
    assert comp.reduce(GB) == 0, f"{name}: target does NOT satisfy the constraint"
    c_cof = comp.lift(B)
    print(f"[{name}] proven over char NOT in {excluded}: "
          f"constraint=0 forces o=target (mult values on cube: {vals})")
    print("  soundness cofactors (for a^2-a, b^2-b, c^2-c):")
    for g, gn in zip(s_cof, B.gens()):
        print(f"      {gn}:  {g}")
    print("  completeness cofactors:")
    for g, gn in zip(c_cof, B.gens()):
        print(f"      {gn}:  {g}")
    print()
    return s_cof, c_cof

# Maj : (o + a + b - 9c + 3)(a + b + 6c - 4) + 12 = 0  ==>  o = maj
maj = a*b + c*(a + b - 2*a*b)
run("maj3", (o + a + b - 9*c + 3)*(a + b + 6*c - 4) + 12, maj, a + b + 6*c - 4)

# XOR3: (o + 2a + 2b + 7c)(a + b - 4c + 1) - (6a + 6b - 24c) = 0  ==>  o = parity
xor = a + b - 2*a*b + c - 2*(a + b - 2*a*b)*c
run("xor3", (o + 2*a + 2*b + 7*c)*(a + b - 4*c + 1) - (6*a + 6*b - 24*c), xor, a + b - 4*c + 1)
