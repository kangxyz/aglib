# Coherent sheaves on locally Noetherian schemes

[Basic](Basic.lean) defines the native guarded abbreviation `AlgebraicGeometry.Scheme.CoherentSheaf X` for `[IsLocallyNoetherian X]`. It identifies coherent objects with the actual [affine-locally finite-type quasicoherent category](../QuasiCoherent/FiniteType/README.md). The lower category exists on every scheme; local Noetherianity guards the coherent interpretation and supplies its abelian structure.

[Exact](Exact.lean), imported as `Aglib.AlgebraicGeometry.Modules.Coherent.Exact`, supplies `Scheme.Modules.Coherent.coherentExactStructure`, `coherentInclusion` and `coherent_shortExact_iff`. Selected coherent conflations are exactly actual short exact sheaf sequences under the inclusion. The essential-smallness bound is the lower sheaf-object universe `u+1`. [Restriction](Restriction.lean) gives exact coherent open restriction and supported coherent objects. [Pullback](Pullback.lean) specializes the lower finite-type pullback to the guarded coherent categories on locally Noetherian source and target schemes, with actual identity/composition/restriction comparisons; [FlatPullback](FlatPullback.lean) gives `coherentExactPullback` under flatness of the scheme morphism.

[FinitePresentation](FinitePresentation.lean) uses the lower [Noetherian finite-presentation constructions](../FinitePresentation/Noetherian.lean) to give the coherent-category finite-type/finite-presentation comparison under local Noetherianity. General finite-presentation transport/locality remains below this category. [Homology](Homology.lean) preserves the actual finite-type/coherent property under homology on locally Noetherian schemes; [AffineDetection](AffineDetection.lean) detects a zero coherent object on the specified actual affine restrictions.

[Affine coherent comparison](Affine/README.md) and [coherent direct image](Pushforward/README.md) retain their Noetherian/exact-structure hypotheses. [Finite locally free sheaves](../LocallyFree/README.md) has an exact coherent inclusion under local Noetherianity. General module cohomology consumes the underlying actual module and finite-presentation witness.

[Subobjects](Subobjects.lean) proves finite type of quasicoherent subobjects of coherent
objects under the stated Noetherian hypotheses; [Gluing](Gluing.lean) retains the specified
open-cover and overlap equations. [Extension](Extension/README.md),
[localization](Localization/README.md) and [support](Support/README.md) separate geometric
extension, the ordinary Serre quotient and its chosen small presentations. Local
Noetherianity supplies coherent subobject extension and quotient fullness; the proved
essential-surjectivity/localization specialization assumes `IsNoetherian X`.

[StalkFinite](StalkFinite.lean) proves finite generation for the actual coherent
stalk module and its original structure-sheaf action. Its global coherent-stalk
statement retains `IsNoetherian X`; the affine and tilde statements retain their
displayed ring and module hypotheses.

Focused interface guides: [Coherent presentations from an actual projective embedding](Projective/README.md).

[FiniteCoverGluing](FiniteCoverGluing.lean) glues compatible coherent
subobjects inside an arbitrary ambient module over a finite open-immersion
cover of a locally Noetherian scheme. The kernel of the original finite product
of cokernel obstructions retains every local inclusion equation. The ambient
module need not be coherent or flat.

For a coherent ambient module, [FiniteCoverQuotients](FiniteCoverQuotients.lean)
takes the cokernel of the glued relation subobject and retains every local
quotient map. [FiniteCoverQuotientDescent](FiniteCoverQuotientDescent.lean)
obtains the relation-overlap comparisons from compatible local epimorphisms
onto coherent quotients. Their quotient equations force relation compatibility
without a separately chosen relation cocycle or global realization.
[QuotientRestrictionComparison](QuotientRestrictionComparison.lean) transports
these quotient equations to smaller charts and uses epimorphism cancellation
to make the comparison independent of the covering chart.

[Algebra/Sections](Algebra/Sections.lean) equips the original sections of a
native commutative monoid in `X.Modules` with scoped ring and section-algebra
structures. [SectionLaws](Algebra/SectionLaws.lean) detects the internal monoid
laws on original pure section tensors. [Tensor](Algebra/Tensor.lean) proves
closure of finite-type quasicoherent modules under the actual ambient tensor
without Noetherianity; local Noetherianity gives coherent tensor closure.
No additional monoidal structure on the coherent category is installed.

[Algebra/DirectImage](Algebra/DirectImage.lean) gives the actual `f_*𝒪` its
native commutative algebra structure for any scheme map; a finite map makes
its underlying module affine-locally finite type. [DirectImageMaps](Algebra/DirectImageMaps.lean)
retains the original contravariant structure-module maps, and
[DirectImageSections](Algebra/DirectImageSections.lean) identifies its section
algebra with the original structure sections on the inverse-image open.
[AffineRestriction](Algebra/AffineRestriction.lean) and
[ScalarExtension](Algebra/ScalarExtension.lean) retain the canonical algebra
base-change map and its original unit-tensor equation. Quasicoherence guards
the affine restriction equivalence; these lower algebra constructions do not
impose a locally Noetherian coherent interpretation on arbitrary modules.

The [proper algebraization of operations](../../Cohomology/GrothendieckExistence/Algebraization/Operations.lean)
uses coherent tensor sources to lift unit and multiplication. The
[finite-etale adic family](../../Morphisms/FiniteEtale/Adic/README.md) uses the
original direct-image algebras and their section restrictions to reconstruct
actual covers.
