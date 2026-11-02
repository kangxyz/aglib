# Finite Cartier Hilbert numerics

`finiteCartier_dualIdealPower_cohomology_of_divisor_rank` is the single
power-induction implementation. For an actual closed immersion with finite
composite to the field and invertible ideal, it assumes unit H0 dimension one,
unit H1 vanishing, and dimension two for the full finite divisor's H0. It
concludes `H1(C,L^r) = 0` and `dim H0(C,L^r) = 2r + 1` for the actual dual
ideal line in every natural degree. Properness or Cohen–Macaulay hypotheses
are not needed once the actual finite Cartier divisor is supplied.

`finiteCartier_h0_finrank_of_ideal_cohomology` computes the H0 dimension of
the full finite Cartier divisor `i : D → C` from its actual ideal sequence.
It needs H0 of the structure sheaf to have dimension one, H1 of the structure
sheaf and H0 of the ideal sheaf to vanish, and H1 of the ideal sheaf to have
dimension one. It concludes `dim H0(i_* O_D) = 2`.

`finiteCartier_dualIdealPower_cohomology` retains its original statement and
uses that ideal-cohomology supplier in the shared induction.

`finiteCartier_h0_finrank_of_dualIdeal_h0` instead derives divisor dimension
two from three actual sections of the dual ideal line and the same unit
cohomology. The original positive Cartier row gives a surjection on H0;
quotient finiteness is established before the dimension calculation.
`finiteCartier_dualIdealPower_cohomology_of_firstPower` uses this producer in
the same induction. Neither inverse-line cohomology, H1 of the positive line,
nor a canonical identification is a premise of this first-power route.
All scalar actions are those of the original `FScheme k`.

The proof tensors the original ideal row and uses the original Cartier
coefficient sequence, not a replacement quotient. Lines on the full finite
scheme `D` are trivial, so all these quotient section dimensions equal two.
Only numerical equalities use that noncanonical trivialization. The original
section, quotient adjunction unit, and structural field action are retained.
Finite closed support kills quotient H1, and exactness gives both the
inductive H1 vanishing and section-dimension recurrence.

No reducedness, smoothness, geometric integrality, perfection, infinite-field
hypothesis, Hilbert polynomial, or degree identity is used. This is the
finite-Cartier proof of the slope-two numerical step in the rational-double-
point argument; compare Stacks 53.5, Tag 0B5B, and 54.12, Tag 0BGB. The proof
is not an implementation of their entire Riemann–Roch or resolution results.

An actual coefficient canonical identification with the ideal sheaf can
supply the old endpoint's two ideal-cohomology hypotheses through coefficient
Serre duality. The first-power endpoint does not require it.
Existence of a finite Cartier representative of the positive line
over the original field is also not asserted. For an arbitrary-field
application, ordinary flat cohomology base change and a genuine regular
hyperplane over an infinite extension can supply the numerical comparison;
canonical-module gluing over that extension is not needed for this route.

The intended consumer is the full exceptional scheme of an ordinary rational
surface blowup. Its native power-section equivalence must still be used to
identify these dimensions with the original associated graded components.
This leaf alone does not prove the required canonical identification,
Gorenstein preservation, or rational-double-point resolution.
