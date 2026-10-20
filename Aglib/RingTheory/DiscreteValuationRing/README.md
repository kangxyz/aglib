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
