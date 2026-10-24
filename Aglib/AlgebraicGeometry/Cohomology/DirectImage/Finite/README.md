# Actual finite derived direct images

[Coherent](Coherent.lean), imported as
`Aglib.AlgebraicGeometry.Cohomology.DirectImage.Finite.Coherent`, uses the
original installed `Scheme.Modules.derivedPushforwardPlus`. No replacement
derived category, representative complex or higher-image object is defined.

For a finite morphism `f : X ⟶ Y` and a finite-type quasicoherent module
`M`, `finite_higherDirectImage_coherent` proves every original native
`((Modules.pushforward f).rightDerived q).obj M` coherent when `Y` is
locally Noetherian. Its degree-zero proof is the original
`rightDerivedZeroIsoSelf` and actual finite pushforward. Positive degrees
are zero by quasicoherent affine acyclicity. Exactness of `f_*` on all
module sheaves is not used.

`finite_derivedSingle_zero_coherent` instead directly consumes the actual
[affine acyclic-single comparison](../Affine/Single.lean), whose original
derived unit and coefficient maps are preserved. The shared native
single/homology property and original shift comparison give
`finite_derivedSingle_coherent f M hM i` in every integer degree.
`finite_derived_coherent` applies the sole finite Postnikov theorem to
cohomologically bounded objects with coherent original homology on locally
Noetherian source and target. There is no termwise coherence premise.

The amplitude statements `finite_derivedSingle_isLE`,
`finite_derived_isLE` and `finite_derived_bounds` require no Noetherianity
or finite-type coefficient. They retain quasicoherence of the original
homology layers in the specified source interval. A finite image preserves
the same interval `[l,b]`; the lower bound is the shared native lower-bound
theorem and the upper bound uses coefficient-specific affine acyclicity.
`finite_derived_bounded_coherent` combines the coherent and interval
conclusions. Actual projective finite-product comparisons, finite
factorizations of modifications, and proper closed-support induction
consume these interfaces.

The exact source passed with receipt `1792119248720598000-99386` in
3.4 seconds at the default budget. The independent arbitrary-scheme-universe
`FiniteDerivedCoherentConsumer.lean` passed with receipt
`1792119295558849000-99943`. It checks actual native singles, bounded
objects, the finite identity case, and the exported Noetherian-free
amplitude interface. All eight inspected declarations use only
`propext`, `Classical.choice`, and `Quot.sound`.

[Trace](Trace.md) proves `finiteTraceCohomology_length_le` on an actual finite
birational-base diagram over a finite faithful local algebra. Normality of
the lower base and model, the original function-field identifications and
scalar towers are retained. In every degree the upper cohomology length is
bounded by discriminant-torsion length times the actual residue degree plus
field degree times lower cohomology length. The trace-coordinate map is only
base-linear; finite flatness and residue separability are not assumed.
The uniform separable surface bound consumes this actual-diagram inequality.
