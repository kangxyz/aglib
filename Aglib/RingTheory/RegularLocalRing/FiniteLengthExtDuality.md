# Exact and faithful Ext-two over a regular local surface ring

Let `R` be a commutative regular local ring with `ringKrullDim R = 2`.
For an actual `ModuleCat R` object `M`, `IsRegularLocalRing.extDualTwo R M`
is the native group `Ext M (ModuleCat.of R R) 2`, with its original
`R`-module structure. `extDualTwoMap` is Yoneda precomposition with
`Ext.mk₀ f` for the given morphism `f`; `extDualTwoMapLinear` records
linearity in that same morphism.

`subsingleton_ext_of_isFiniteLength_ne_two` combines the existing lower
Ext vanishing theorem with the regular-local projective-dimension bound.
It proves vanishing in every natural degree other than two for each
finite-length source. No vanishing or resolution is assumed as an input.

For an original short exact row `M₁ → M₂ → M₃`, `extDualTwo_exact`
proves injectivity, exactness, and surjectivity of the reversed row of
native Ext-two precomposition maps. Its only module-length assumptions
are finite length of the two outer modules. The proof applies the actual
contravariant long exact sequence and the just-proved endpoint vanishing.

The residue-field comparison
`nonempty_residueField_extDualTwo_linearEquiv` uses the original Koszul
`ChainComplex.Koszul.topExtRingQuotientLinearEquiv` for a regular system
of two parameters. Its quotient-source action is restricted back to the
original `R`-action using the native annihilated-module scalar tower.
The degree equality and the canonical quotient equivalence are transported
explicitly, with Ext-source transport given by original precomposition.
The comparison is therefore an actual linear equivalence, rather than
a numerical dimension assumption.

Finite-length induction, with this residue-field computation at each
simple factor, proves `length_extDualTwo`. It gives equality of the
original `R`-lengths. `isFiniteLength_extDualTwo` and
`subsingleton_extDualTwo_iff` then prove finite length and zero detection.
Finally `extDualTwoMap_eq_zero_iff` factors the original morphism through
its actual image, applies exactness to its kernel and quotient rows, and
uses zero detection on that image. `extDualTwoMap_injective` is the
resulting faithfulness statement on each original Hom module.

No exactness, faithfulness, or length-preservation predicate is supplied
as a hypothesis. The file constructs no injective hull, bidual evaluation,
derived anti-equivalence, extra algebra action, or trace. Comparisons with
an intrinsic dualizing module for a finite algebra, annihilator transport,
and residue-degree conversion of lengths belong to their separate owners.

This implements the smaller finite-length route in section 5 of
`tmp/output/aglib-general-comparison-20261023/general-surface-research/duality/regular-base-duality-route-v1.md`,
SHA-256 `4e231c9f47c14ad38ad1f97c8777d43c1f9b0c9a39ec6c60fb406a0c0c43b0c9`.
The fixed smaller derivation has independent ordinary review acceptance.
Native completion and any broader established-status decision are separate.
Input basis: Aglib `8b93cc5940dc93f39a2eaf05e6985af28250a578`,
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean `4.34.1`.
