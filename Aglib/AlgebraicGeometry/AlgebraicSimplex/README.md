# Affine algebraic simplices

The native namespace is `AlgebraicGeometry.AlgebraicSimplex`.
[Basic](Basic.lean) constructs the literal quotient
`CoordinateRing R n = R[t₀,…,tₙ]/(∑ tᵢ - 1)` over any commutative ring.
A vertex-set map pulls coordinates back by summing over its fibres.
`pullback_id`, `pullback_comp`, the face identities and coefficient-change
naturality concern these constructed algebra maps. `polynomialEquiv` is the
explicit eliminated-coordinate chart. `ker_face` and `faceQuotientEquiv`
identify each actual face with its principal coordinate quotient.

[Zero](Zero.lean) identifies the literal zero-simplex ring with its coefficient
ring, with scalar, coordinate and vertex-evaluation formulas. The general
statements require only a commutative ring; the separate `zeroField` needs a
field. [Endpoints](Endpoints.lean) retains the source field specialization of
the zero-face parameter identity.

[Units](Units.lean) proves `coordinateRingOne_isPrincipalIdealRing`,
`unit_constant` and `unit_specialization` over a field. Its `constantUnit` and
`pullback_constantUnit` work over any commutative ring.
[FieldBaseChange](FieldBaseChange.lean) proves the actual coefficient map is
flat for any field homomorphism in the stated universe. The proof intertwines
the polynomial chart with that map before transporting polynomial flatness.

[CoefficientEquiv](CoefficientEquiv.lean) constructs the actual coefficient
ring automorphisms over any commutative ring and their inverses. Its Laurent
extension fixes the two ordered integer exponents. [FiniteCoefficients](FiniteCoefficients.lean)
proves that an individual simplex or Laurent element depends on finitely many
scalars of the chosen algebraic closure: automorphisms fixing that set fix the
original element. It does not choose a finite field model or a geometric cover.

[CommutingAutomorphisms](CommutingAutomorphisms.lean) specializes the native
`Module.CommutingAutomorphisms.LaurentSupport` constructions to simplex rings
over a field, including finite support, actual field base change, minimal
components, local multiplicities and actual face scalar cokernels. Lengths
remain in `ENat`. The integer identity at an arbitrary target prime uses
`toNat`; a finite-length interpretation retains the separate Noetherian-target
and minimal-support hypotheses. No cycle or K-group construction is imported.

These are general coordinate-ring and simplicial-algebra interfaces for
algebraic geometry and operator consumers. No motivic complex or homotopy
invariance conclusion is asserted. Source hashes refer to the frozen R5 packet
at `f8a3314ddecffcada2ec721d26d56a937bed9690`; the historical K-theory
namespaces are provenance rather than native ownership.
