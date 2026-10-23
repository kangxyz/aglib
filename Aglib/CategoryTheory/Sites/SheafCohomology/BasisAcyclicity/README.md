# Basis Čech acyclicity

This family proves the basis criterion of
[Stacks 03F9](https://stacks.math.columbia.edu/tag/03F9), using the original
representable-family tuple complexes and original Ext/cohomology groups.

## Interfaces

- [Covers](Covers.lean) defines `CoverBasis`: specified objects, selected covering families,
  refinement of every covering sieve on those objects, and closure under all
  nonempty finite Čech intersections. Its fields contain no cohomology or
  section-surjectivity conclusion. `familyMap_locallySurjective` connects the
  covering sieve with the original map of set-valued presheaves.
- [AllCovers](AllCovers.lean) constructs the cofinal basis of all small covering families by
  taking every arrow in a covering sieve. No quasi-compactness or finite-cover
  premise is used.
- [CoverAugmentation](CoverAugmentation.lean) extends the existing free Čech augmentation to an
  independent value universe, with explicit sheafification and local-bijectivity
  requirements. It uses the existing free complexes and augmentation, unchanged.
- [LocalLifting](LocalLifting.lean) refines the actual image sieve of a quotient section. It then
  uses the existing degree-one primitive/correction and augmentation-cokernel
  mechanisms to lift that section. Only selected covers need Čech H¹ exactness.
- [Quotient](Quotient.lean) defines `CechAcyclic` using positive exactness of the original
  `Presheaf.Cech.additiveHomComplex`. It proves short exactness of these Hom
  complexes using basiswise section lifting at their representing intersections.
  It does not claim that a sheaf epimorphism is sectionwise surjective on every
  object. The Čech-acyclic class is closed under injective quotients; quotients
  need not be quasi-coherent.
- [Basic](Basic.lean) dimension-shifts the original represented-object Ext. When a terminal
  object belongs to the basis, it proves vanishing of the original `Sheaf.H`,
  retaining the original constant-integer source and independent Ext universe.
- [SmallCovers](SmallCovers.lean) raises the index universe through explicit equivalences with
  original small indexing types. This retains a proved `Small` bound and permits
  arbitrary small open covers rather than only finite covers.
- [ValueLift](ValueLift.lean) is the native composition with `AddCommGrpCat.uliftFunctor`.
  Exactness uses kernel preservation and transport of local lifts. It does not
  assert preservation of injective objects.
- [ValueLiftZero](ValueLiftZero.lean) fixes the original constant-integer comparison by its universal
  section at a terminal object. It defines the actual all-degree Ext map and
  proves the degree-zero comparison bijective.
- [TupleProducts](TupleProducts.lean) identifies the original tuple-Hom complex with the native
  product Čech complex, evaluating on the universal tuple and identifying every
  signed restriction differential. [CechReindex](CechReindex.lean) preserves all cosimplicial maps
  under equivalences of possibly differently sized index types.
- [CoproductCover](CoproductCover.lean) gives the canonical all-simplex comparison from a coproduct
  cover to a finite family. Its structural premises are invertibility of the
  actual geometric distribution map and preservation of finite section products,
  not an assumed cohomology comparison. The lower `Limits.FiniteCoproductPowers`
  supplier proves that geometric premise from finite pre-extensivity, including
  empty covers and powers.
- [CechValueLift](CechValueLift.lean) reuses the existing product Čech coefficient comparison for
  arbitrary small covers, with every original alternating coface retained.

- [LiftedInjectives](LiftedInjectives.lean) transports small-injective Čech exactness through the actual
  tuple/product, coefficient-lift and index-reindexing isomorphisms. The basis
  criterion then proves acyclicity for original larger-valued `Sheaf.H`.
- [ValueComparison](ValueComparison.lean) applies native exact-functor Ext comparison to obtain
  `valueLiftCohomologyAddEquiv` in all degrees. Its forward map is the original
  `Ext.mapExactFunctor`, precomposed with the normalized constant-integer map.
  The source and target Ext universes are independent.
- [ValueNaturality](ValueNaturality.lean) proves that this original value-lift Ext map commutes with
  every additive coefficient morphism, not only linear morphisms of modules.
- [CoverEffacement](CoverEffacement.lean) proves that an individual positive original Ext class with
  free representable source vanishes after every arrow in an actual covering
  sieve. It uses an injective-resolution cocycle and local lifting of the
  boundary epimorphism, not a cohomology-vanishing premise.
- [LowDegree](LowDegree.lean) constructs the two kernel short exact sequences of the original
  quasi-isomorphic augmentation. A degree-two original Ext class killed on its
  degree-zero term, with Ext¹ vanishing on the degree-one term, produces a literal
  degree-two Čech cocycle. Any primitive kills the original class. No projective
  resolution terms or full overlap acyclicity are assumed.

## Universe and application boundaries

Site-object and site-morphism sizes are independent. The tuple-family interface
uses coefficients in `max(index, hom)`; `CoverBasis.raise` allows a larger
coefficient universe while retaining only the original small covers. The
sheafification, local-bijectivity, finite-product and enough-injectives
requirements are explicit. No noetherianity, coefficient flatness, or finite
cover-index hypothesis enters the generic criterion.

The all-degree value-universe comparison uses coefficients in `max(c,h,w)`
and their lift to `max(c,h,w,t)`, with covers originally indexed in `max(c,w)`.
The basis acyclicity criterion itself permits site-object size independent of
coefficient size. [AllCovers](AllCovers.lean) supplies a genuine arbitrary-small-cover basis;
[SmallCovers](SmallCovers.lean) raises its index universe without adding larger covers. The
comparison does not assert that universe lifting preserves injectives.

Affine étale applications must supply actual cofinal affine covers and a
literal augmented Amitsur-to-tuple-cochain comparison. This family does not
assume or independently supply quasi-coherent affine vanishing.

## Concrete geometric consumers

The new lower `Limits.OverExtensive` transfers native finite extensivity to
slices using the original forgetful functor. `QuasiCoherent.CoproductSections`
proves finite-product preservation for arbitrary coefficient sheaves on the
original big étale slice via actual Zariski coproduct covers.
`QuasiCoherent.AffineCoverAlgebra` extracts the faithfully flat global-section
ring map of a finite affine étale covering family. Its coproduct is used for
Amitsur descent only, not as a claimed refinement inside the original sieve.

[CechChange](CechChange.lean) proves the finite-product change-of-category comparison without
a thin-target restriction, by the original product projection identities.
[CechNerveIso](CechNerveIso.lean) transports an actual product nerve and its evaluated alternating
complex along an isomorphism of covering objects.
`QuasiCoherent.AffineGeometry` applies this geometry to the canonical affine
scheme isomorphism and the original maps on global sections; no affine model
or geometry hypothesis is supplied by a caller.

[CechNerveIso](CechNerveIso.lean) also transports the original nerve through a finite-product-
preserving functor. `QuasiCoherent.EtaleSliceProducts` applies this to the
original small étale inclusion and iterated-slice equivalence, retaining all
original coefficient restrictions. The lower `Limits.OverCoproducts` identifies
the actual slice coproduct with the original coproduct structure arrow.

The lower `Abelian.Injective.MappedResolution` bundles a supplied mapped complex
as an actual injective resolution using only left exactness, preservation of
injectives and coefficient-specific positive exactness. Its augmentation and
maps of resolutions are the original mapped arrows. In particular, the
étale-to-Zariski restriction functor is not assumed exact on all sheaves.

## Restricted resolutions and canonical comparison

[ResolutionSections](ResolutionSections.lean) converts vanishing of original represented Ext into
literal section primitives and positive exactness of every supplied injective
resolution. [SectionExactness](SectionExactness.lean) detects exactness on an arbitrary site from
sectionwise exactness on an actual covering object basis, with independent
index and value universes. [RestrictionResolution](RestrictionResolution.lean) combines these to make the
original continuous restriction of a supplied resolution an actual resolution.

The lower `DerivedCategory.Ext.AdjunctionAcyclic` proves bijectivity of the
original exact-left-adjoint Ext map followed by the actual counit whenever the
right adjoint carries this particular resolution to an exact resolution. Its
cycle formula is the original Hom adjunction; its naturality covers every
additive coefficient map. The right adjoint is not required to be exact on
other coefficients. These statements use ordinary supplied injective
resolutions and do not introduce another cohomology theory.

The lower `Hypercohomology.ContinuousPullback` identifies inverse images of
original free representable sheaves by the actual section adjunction. At a
terminal object it identifies the original constant-integer source, retaining
its section normalization. `Functor.FlatKanExtension` proves finite-limit
preservation of the native left Kan extension from its actual filtered
costructured-arrow colimits, with independent category and value universes.
This avoids imposing a false same-universe small-category hypothesis on the
opens-to-small-étale functor.

`QuasiCoherent.ZariskiBasis` supplies actual affine-subopen covering families
for every open of every scheme, including non-quasi-compact opens. Thus the
restricted-resolution criterion does not silently replace arbitrary small
open covers by finite covers.

[ContinuousComparison](ContinuousComparison.lean) assembles the canonical map on original sheaf
cohomology from these native source isomorphisms and the adjunction counit.
It proves naturality for every additive coefficient morphism and all-degree
bijectivity from actual basis acyclicity of the supplied coefficient. It does
not assume exactness of restriction on unrelated sheaves.

`QuasiCoherent.ZariskiAdjunction` applies the mixed-universe Kan result to the
actual opens-to-small-étale inclusion. It supplies exact native inverse image
at the larger abelian-group universe, left exact restriction, and preservation
of injectives by restriction. Its raised sheafification instance uses the
original small-model construction; it does not assert that universe lifting
preserves injectives. This is independent of quasi-coherent affine vanishing.

The concrete `QuasiCoherent.AffineAcyclicity` now proves positive exactness for
actual finite affine étale families from faithfully flat Amitsur exactness for
arbitrary modules. `QuasiCoherent.AffineVanishing` applies the original tuple
criterion to the genuine cofinal affine-family basis, obtaining positive
represented Ext and original `Sheaf.H` vanishing. Neither coefficient flatness,
finite generation nor noetherianity is assumed. A generic slice-to-tuple
exactness transport is completed before specializing the concrete coefficient.

Finally `QuasiCoherent.ZariskiComparison` applies the canonical comparison to
every scheme and arbitrary quasi-coherent modules. Its forward map is the
original exact-inverse-image/counit map, is natural for arbitrary additive
coefficient arrows, and is bijective in every degree. The proof uses actual
affine represented vanishing and arbitrary small affine-open covers, not a
separatedness, quasi-compactness, or noetherianity hypothesis. Identifying the
restricted coefficient with a chosen native Zariski module coefficient belongs
to the quasi-coherent coefficient family, not to this generic criterion.

`QuasiCoherent.ModuleCohomologyComparison` finishes the native-source statement:
the original Zariski `moduleAddSheaf` cohomology of every quasi-coherent module
is additively equivalent to original étale cohomology in every degree, with
independent Ext universes. It combines the proved value comparison, the actual
module restriction iso and `ZariskiComparison`. Naturality holds for native
module morphisms and, more generally, arbitrary additive coefficient arrows
whose actual restriction-isomorphism square commutes.
