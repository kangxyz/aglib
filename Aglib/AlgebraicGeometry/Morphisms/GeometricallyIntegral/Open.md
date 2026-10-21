# Generic integral fibres of smooth proper relative curves

[Open.lean](Open.lean) addresses the curve scope of `R-GEOMINTEGRAL-OPEN`.
For a proper morphism `f : X ⟶ Y` smooth of relative dimension one, with
`Y` integral and locally Noetherian, a geometrically integral actual generic
fibre yields an open `U` containing `genericPoint Y`, with `U ≠ ⊥` and
`GeometricallyIntegral (f ∣_ U)`. The theorem also retains geometric integrality
of every original `f.fiberToSpecResidueField y` for `y ∈ U`.

The open is the locus where the original point-fibre cohomology of the
ordinary pullback of `O_X` has dimension less than two. The explicit
`pointFiberUnitH0SectionsEquiv` identifies this module with the actual global
sections of the same fibre, preserving the structural residue-field action.
Properness and nonemptiness of the generic fibre make `f` surjective. Hence
every fibre is nonempty, its field-to-sections map is injective, and its finite
H0 dimension is positive. On `U` that dimension is one. The resulting actual
constants isomorphism gives an isomorphism of the whole structure-sheaf map
over the residue-field spectrum. Proper connected-fibre theory gives geometric
connectedness, and smooth relative dimension one gives geometric integrality.

The providers are the existing proper fibre semicontinuity and finiteness
theorems in `Cohomology/Proper`,
`Scheme.constants_bijective_of_proper_geometricallyIntegral`,
`Scheme.geometricallyConnected_of_isProper_of_isIso_c`, and
`Scheme.geometricallyIntegral_of_smoothOfRelativeDimension_one_of_geometricallyConnected`.
No geometric-connectedness, H0 base-change, or desired-family theorem is a
new input to the generic-open theorem.

`geometricallyIntegral_of_smoothProper_of_fieldBaseChange` also detects
geometric integrality of a proper smooth relative curve after any field
extension. The proof uses the existing canonical degree-zero tensor
comparison and the actual structural constants on both field schemes;
neither algebraicity nor an algebraically closed extension is required.

This is the smooth proper relative-curve scope. It does not assert the
unrestricted openness theorem for arbitrary proper flat finitely presented
families. [SpreadingOut.lean](../SpreadingOut.lean) retains literal pullback
comparisons when the specified original field point factors through `U`.

Assignment basis: `AGLIB_PROOF_TASKS.json`, task `R-GEOMINTEGRAL-OPEN`, from
`aglib-full-independent-agent-20261021.zip`; implementation base Aglib
`3a4d549981ced306d89d3ed55418c9e6a25f86c4`, pinned Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` and Lean 4.34.1. Compilation evidence
is reported separately with its actual source hash.
