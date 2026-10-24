# Ext concentration for normal local quotients

`NormalQuotientExt.lean` concerns an actual surjective local map `f : S → B`.
The source is a regular local ring of arbitrary finite dimension `d`. The
target is a normal Noetherian local domain of dimension `r ≤ 2`. For the
module structure induced by this same map, it proves

`Ext^j_S(B,S) = 0` whenever `j + r ≠ d`.

The public endpoint does not assume Cohen--Macaulayness, Gorensteinness,
finite projective dimension, or a supplied regular parameter list. It does
not require the ambient dimension to be two.

The parameter list is constructed in the target. Dimension zero uses the
empty parameter set. Dimension one uses an actual maximal-primary principal
parameter and the domain hypothesis. Dimension two uses
`IsLocalRing.exists_parameter_pair_containing` and
`IsIntegrallyClosed.isRegular_pair_of_radical_eq_maximalIdeal` from
`FiniteNormalAlgebra.lean`. The latter proves regularity on the original
successive quotients by height-one divisibility.

Surjectivity lifts the list to `S`. Native
`isWeaklyRegular_map_algebraMap_iff` transfers its regularity to the actual
restricted scalar action. `Ideal.smul_top_eq_map`, `Ideal.map_ofList` and
`Submodule.Quotient.restrictScalarsEquiv` identify the scalar-list quotient
with the target parameter quotient. Its annihilator has radical the actual
maximal ideal of `S`, by `Module.comap_annihilator` and
`IsLocalRing.maximalIdeal_comap`. Native maximal-support finite length then
applies over `S`.

For finite-length sources, the existing arbitrary-dimensional lower Ext
vanishing and `projectiveDimension_le_dimension` give concentration in
degree `d`. The scalar-source short exact row induces multiplication by
the same scalar on Ext. Vanishing one degree higher for its source quotient
makes that multiplication surjective; finite Ext and Nakayama give zero.
`Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner` identifies the actual
successive quotients needed to iterate this argument.

The native finite-Ext and lower-vanishing suppliers use `ModuleCat.{u} S`
and `Ext.{u}` for `S B : Type u`. The endpoint states that boundary explicitly.
The `_chgUniv` endpoint transports it to a specified `Ext.{w}` using the
actual native `Ext.chgUniv` equivalence under `HasExt.{w}`. The native
`Ext.homEquiv_chgUniv` law retains the same derived-category morphism.

The current consumer is local algebra at the original stalk quotient of a
chosen projective embedding of a normal integral surface. This module does
not assemble sheaf concentration, codimension, a canonical sheaf or trace
compatibility. Its authoring basis is the arbitrary-ambient-dimension
argument in the chosen-embedding concentration paper
`e9dd8fb58ebc9cc80e327b39767491af71e5e7292902c3e1f0c388874fcd521f`.
