# Reflexive modules

This family extends the native `Module.IsReflexive` predicate, defined by bijectivity of the original double-dual evaluation map.

[Localization](Localization.lean), imported as `Aglib.RingTheory.Reflexive.Localization`, proves `Module.IsReflexive.of_isLocalizedModule` for a specified module localization map. The original module and its dual must be finitely presented; these conditions hold for a finite module over a Noetherian ring. The proof compares the actual evaluation maps using finite-presentation Hom localization. No normality or freeness premise is imposed.

The separate interfaces below supply reflexivity of finite normalizations and Hom modules, codimension-one reconstruction, and Auslander's freeness criterion. The [purity guide](../../../docs/ZARISKI_NAGATA_PURITY.md) describes their assembly. Tests for localization are in `AglibTest.ReflexiveLocalization`.

[SecondSyzygy](SecondSyzygy.lean) realizes a finite reflexive module over a Noetherian commutative ring as a second syzygy: an injective map into a finite free module has image the kernel of a map to another finite free module. The proof uses the actual double-dual evaluation and a finite presentation of the dual. This does not by itself bound projective dimension without further regular-local hypotheses.

[HeightOneLattice](HeightOneLattice.lean) proves actual generic-vector membership in a reflexive module from codimension-one denominator conditions over a normal Noetherian domain. [HeightOneReconstruction](HeightOneReconstruction.lean) applies this to an actual linear map: a reflexive finitely presented source (with finitely presented dual), torsionfree target, actual generic bijectivity and actual height-one local surjectivity imply surjectivity. Reflexivity of the target is not required. The generic and localized maps are the native module-localization maps, not supplied replacement equivalences.

[DoubleDualFraction](DoubleDualFraction.lean) identifies the actual double dual inside a finite-dimensional generic vector space, without assuming the original module reflexive. [Algebra](Algebra.lean) proves multiplication closure of that image for an algebra. These feed the actual [finite integral-closure reflexivity theorem](../IntegralClosure/Reflexive.lean). [Pi](Pi.lean) supplies finite products of native reflexive modules.

[Dual](Dual.lean) proves reflexivity of finite duals over a Noetherian domain. [Hom](Hom.lean) proves the needed finite Hom reflexivity with reflexive target; original-source reflexivity is not imposed. [DualPi](DualPi.lean) gives finite-product dual and bidual comparisons, including compatibility with the original evaluation map. These supply the actual endomorphism and finite-product objects used in the Auslander proof.

[AuslanderLengthBound](AuslanderLengthBound.lean) supplies the self-Ext length upper bound in dimension three, with explicit finite-defect map hypotheses. [AuslanderDimensionThree](AuslanderDimensionThree.lean) discharges the canonical evaluation defects, rank relation and Ext-length premises from punctured freeness and the original endomorphism-module equivalence, concluding freeness for a finite reflexive module over a three-dimensional regular local ring. This endpoint retains punctured freeness and is not the all-dimensional criterion or the full purity theorem.

[QuotientEndomorphismComparison](QuotientEndomorphismComparison.lean) and
[QuotientEndomorphismPi](QuotientEndomorphismPi.lean) derive the actual
endomorphism decomposition of the quotient bidual from the original
decomposition. They retain regularity on the scalar, explicit regularity and
dimension of the quotient ring, and punctured freeness; they do not assume
arbitrary global Hom base change. Original action and evaluation compatibility
are part of the interface.

[BidualPuncturedFree](BidualPuncturedFree.lean) proves both finite-length
evaluation defects and punctured freeness of the actual bidual.
[QuotientBidualFree](QuotientBidualFree.lean) lifts freeness from the quotient
bidual using first-Ext comparison in quotient dimension at least three.
[Auslander](Auslander.lean) assembles the all-dimensional punctured-free local
criterion. [AuslanderRegularRing](AuslanderRegularRing.lean) removes the
punctured-freeness input for a local ring carrying native `IsRegularRing`, using
strict dimension drop and actual localization comparisons.
[AuslanderFlat](AuslanderFlat.lean) gives global flatness over `IsRegularRing`;
it does not assert global freeness over a nonlocal base.
