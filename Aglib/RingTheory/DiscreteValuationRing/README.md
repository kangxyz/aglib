# DVR localization, norm and length interfaces

[DeterminantLength](DeterminantLength.lean),
[FiniteNorm](FiniteNorm.lean) and [OrderTransport](OrderTransport.lean) use
`IsDiscreteValuationRing.FiniteNorm`. Determinant valuations equal actual
cokernel lengths for injective endomorphisms of finite free modules over a
DVR. Multiplication specializes this to principal-quotient lengths and
`Algebra.norm`, without perfectness or separability assumptions.

`FiniteNorm` first compares fraction-field norms with localized determinant
norms for finite free domain algebras and their compatible fraction maps.
Artinian principal quotients decompose over every supporting prime, with
actual local lengths and residue degrees. Finiteness is proved before the
`ENat.toNat` conversions. Under the final DVR base, finite domain algebra and
DVR maximal-localization assumptions, `fieldNorm_order_eq_sum_all_maximal`
gives the formula for every unit of the actual fraction field. The finite free
property is derived from the displayed finite-domain/fraction-map data.

The scheme realization of the entire inverse image and all its branches is
[Finite.LocalNormAlgebra](../../AlgebraicGeometry/Morphisms/Finite/LocalNormAlgebra.lean).
The ring theorem alone does not identify arbitrary algebras with scheme stalks.
`OrderTransport.ordFrac_eq_of_ringEquiv` requires an actual DVR ring equivalence
whose scalar triangle commutes in the same supplied fraction field.

Existing [FractionAway](FractionAway.lean) supplies localization at any nonzero
nonunit; [FractionBaseChange](FractionBaseChange.lean) supplies the compatible
fraction pushout and tensor equivalence, including ramified local DVR maps.
These native providers are reused. Incoming norm/length hashes are recorded in
the leaves against R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.

## Parameter DVRs and completed-source modifications

[ParameterCompletionStability](ParameterCompletionStability.lean) proves that
`AdicCompletion.HasGeometricallyReducedFractionCompletion` passes from a
domain DVR to its actual parameter DVR localization, for any finite parameter
type in an independent universe and a chosen uniformizer. The coefficient,
fraction and residue actions are the constructed ones. The
[separating-coordinate construction](SourceSeparatingCoordinates.lean) uses
the original centre residue field and fraction-field degree; the projected
chart retains the same source generators, selected relations and coordinate
matrix when transporting Fitting ideals.

[CompletedGlobalTermination](CompletedGlobalTermination.lean) iterates the
actual global Néron modifications under that intrinsic coefficient condition,
retaining the original polynomial action and common fraction field.
[CompletedGlobalImageSmooth](CompletedGlobalImageSmooth.lean) specializes this
to an injective finite-type algebra point in multivariate power series over
the actual completion: it constructs a finite-type enlargement embedded in
the same power-series ring and smooth at its actual uniformizer centre.
This smooth-image theorem uses `Fin n` parameters and coefficient/source
rings in one universe. Characteristic zero supplies a separate wrapper. The
[geometric-local DVR approximation construction](../Henselian/DVRArtinApproximation.md)
uses this enlargement inside its finite local model; it does not require the
original finite-type algebra to be a domain or flat.

## Dimension-one criteria and arbitrary residue extensions

[DimensionOne](DimensionOne.md) gives the normal local dimension-one DVR
criterion and actual prime-localization consumers for nonzero principal
quotients. Its regular-ambient alternative retains the original minimal-prime
condition and ambient localization.
[MonogenicResidueExtension](MonogenicResidueExtension.md) and
[ResidueExtension](ResidueExtension.md) construct actual marked residue
extensions while retaining the same natural prime as uniformizer.
[FilteredColimit](FilteredColimit.md) proves the DVR and maximal-kernel
properties for the original compatible filtered diagram. These feed the
[arbitrary-residue Cohen construction](../LocalRing/CohenRing.md).
