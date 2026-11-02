# Arbitrary-field anticanonical Hilbert numerics

For an actual closed embedding `j : C → P_k`, let `L = j*O(1)`.
`cmCurve_hyperplanePower_h0_finrank` assumes the existing closed-stalk
CM-parameter condition, `h0(O_C)=1`, `H1(O_C)=0`, `H0(L∨)=0`, and
`h1(L∨)=1`. It derives `h0(L^r)=2r+1` for every natural r over the original
arbitrary field k.

The algebraically closed intermediate in `AnticanonicalHilbert/Geometric` derives nonemptiness from h0 of the
structure sheaf. It chooses one genuine closed rational point and applies
the existing regular-hyperplane theorem. That theorem does not assume three
global sections; its exclusion of the point from associated primes comes
from the closed-stalk parameter hypothesis. The resulting Cartier ideal is
the zero ideal of the same pulled polynomial section, identified with L∨ by
the existing original zero-ideal map. The numerical Cartier theorem applies
to this full finite divisor, including its nilpotents.

Over arbitrary k the proof uses precisely the existing projective Cartesian
base-change model over an algebraic closure. The original ordinary cohomology
scalar-extension map preserves every cohomology dimension, and its isomorphism
preserves vanishing. The original tensor-pullback and unit maps compare the
pulled inverse line with the dual of the new O(1). The actual power-pullback
comparison then transports the result back to k. The variable-field comparison proof is in `AnticanonicalHilbert/ScalarExtension`;
this leaf retains only the final algebraic-closure specialization.

No curve is reduced, no residue field is declared perfect or unchanged, and
no canonical-module gluing over the algebraic closure is assumed. The inverse-
line cohomology still needs its actual canonical origin, for instance a
proved identification with the coefficient canonical sheaf followed by the
existing Serre trace. This is not a proof of that identification or of
Gorenstein preservation. The surface consumer must retain its literal
exceptional-line and original associated-graded comparisons.

## Arbitrary-field first-power variant

`cmCurve_hyperplanePower_h0_finrank_of_firstPower` assumes only the same actual
closed projective embedding and closed-stalk CM parameters, `h0(O)=1`,
`H1(O)=0`, and `h0(j*O(1))=3`. It gives all original-field ranks `2r+1` by the
proved first-power scalar-extension theorem with `K=AlgebraicClosure k`.
No inverse-line cohomology or canonical-module base-change input remains in
this variant. The original inverse-cohomology endpoint is preserved unchanged.
