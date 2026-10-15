/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.Finite.GeneralPushforward
public import Aglib.Algebra.Category.ModuleCat.IdealClosedSupport
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Comparison
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
/-!
# Actual coherent pushforward from an arbitrary affine closed subscheme

For every ideal `I`, pushforward along `Spec(R/I) → Spec(R)` restricts to
an exact fully faithful functor on coherent sheaves. Its essential image is
exactly the coherent sheaves whose global sections are annihilated by `I`.
The retained comparison squares use actual quotient-ring restriction and
actual global sections.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open CategoryTheory.ExactCategory
open ModuleCat
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal

open ModuleCat.FiniteLocalization.IdealClosedSupport

variable (R : CommRingCat.{u}) (I : Ideal R)

/-- The closed subscheme's affine coordinate ring. -/
abbrev closedRing : CommRingCat.{u} := CommRingCat.of (ClosedRing I)

/-- The actual closed immersion induced by the quotient map. -/
def closedMap : Spec (closedRing R I) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I)))

instance closedMap_isClosedImmersion : IsClosedImmersion (closedMap R I) := by
  unfold closedMap
  infer_instance

/-- Actual sheaf pushforward preserves the affine coherence property. -/
theorem affineFiniteSheaf_pushforward {M : (Spec (closedRing R I)).Modules}
    (hM : affineFiniteSheaf (closedRing R I) M) :
    affineFiniteSheaf R ((Scheme.Modules.pushforward (closedMap R I)).obj M) := by
  have : M.IsQuasicoherent := hM.1
  refine ⟨Scheme.Modules.isQuasicoherent_pushforward _ M, ?_⟩
  let N : FGModuleCat (ClosedRing I) := ⟨moduleSpecΓFunctor.obj M, hM.2⟩
  have : Module.Finite R ((moduleSpecΓFunctor ⋙
      ModuleCat.restrictScalars (CommRingCat.ofHom (Ideal.Quotient.mk (I))).hom).obj M) :=
    ((closedRestriction I).obj N).property
  exact Module.Finite.equiv
    ((Scheme.Modules.pushforwardGlobalSectionsIso
      (CommRingCat.ofHom (Ideal.Quotient.mk (I)))).app M).symm.toLinearEquiv

/-- Actual closed pushforward preserves the all-affine-chart finite-type quasicoherent predicate. -/
theorem affineLocallyFiniteType_pushforward {M : (Spec (closedRing R I)).Modules}
    (hM : affineLocallyFiniteType (Spec (closedRing R I)) M) :
    affineLocallyFiniteType (Spec R) ((Scheme.Modules.pushforward (closedMap R I)).obj M) :=
  (affineLocallyFiniteType_spec_iff R _).mpr
    (affineFiniteSheaf_pushforward R I ((affineLocallyFiniteType_spec_iff (closedRing R I) M).mp
      hM))

variable [IsNoetherianRing R]

/-- Quotient-coordinate specialization of canonical finite direct image. -/
abbrev coherentPushforward : Scheme.CoherentSheaf (Spec (closedRing R I)) ⥤
    Scheme.CoherentSheaf (Spec R) :=
  Pushforward.Finite.coherentPushforward (closedMap R I)

/-- The finite-type sheaf inclusion gives the actual sheaf pushforward, definitionally. -/
theorem coherentPushforward_comp_inclusion :
    coherentPushforward R I ⋙ finiteTypeSheavesToModules (Spec R) =
      finiteTypeSheavesToModules (Spec (closedRing R I)) ⋙
        Scheme.Modules.pushforward (closedMap R I) := rfl

/-- The actual geometric pushforward/global-sections comparison square. -/
def coherentPushforwardSquare :
    coherentPushforward R I ⋙ (finiteTypeSheavesSpecModuleEquivalence R).functor ≅
      (finiteTypeSheavesSpecModuleEquivalence (closedRing R I)).functor ⋙ closedRestriction I :=
  ((finiteModule R).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules (Spec (closedRing R I)))
      (Scheme.Modules.pushforwardGlobalSectionsIso
        (CommRingCat.ofHom (Ideal.Quotient.mk (I)))))

instance coherentPushforward_full : (coherentPushforward R I).Full :=
  Functor.Full.of_comp_faithful_iso (coherentPushforwardSquare R I)

instance coherentPushforward_faithful : (coherentPushforward R I).Faithful :=
  Functor.Faithful.of_comp_iso (coherentPushforwardSquare R I)

/-- The exact quotient-coordinate specialization of finite direct image. -/
abbrev coherentPushforwardExact :
    ExactFunctor (coherentExactStructure (Spec (closedRing R I)))
      (coherentExactStructure (Spec R)) :=
  Pushforward.Finite.coherentPushforwardExact (closedMap R I)

open ModuleCat.FiniteLocalization.IdealClosedSupport
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R)

/-- Annihilation by I on actual affine coherent sheaves, tested on the
actual global-section module. This is stronger than power-torsion support. -/
def finiteTypeSheavesKilledBy : ObjectProperty (FiniteTypeSheaves (Spec R)) :=
  (killedBy I).inverseImage (finiteTypeSheavesSpecModuleEquivalence R).functor

instance finiteTypeSheavesKilledBy_isoClosed : (finiteTypeSheavesKilledBy R
  I).IsClosedUnderIsomorphisms := by
  dsimp [finiteTypeSheavesKilledBy]
  infer_instance

/-- The affine global-section equivalence restricts to annihilated objects. -/
def killedModuleEquivalence :
    (finiteTypeSheavesKilledBy R I).FullSubcategory ≌ (killedBy I).FullSubcategory :=
  (finiteTypeSheavesSpecModuleEquivalence R).congrFullSubcategory rfl

/-- The actual closed pushforward is annihilated by every element of the defining ideal. -/
theorem coherentPushforward_killed (M : FiniteTypeSheaves (Spec (closedRing R I))) :
    finiteTypeSheavesKilledBy R I ((coherentPushforward R I).obj M) := by
  let e := (coherentPushforwardSquare R I).app M
  intro r hr m
  apply (FGModuleCat.isoToLinearEquiv e).injective
  rw [_root_.map_smul, map_zero]
  exact closedRestriction_killed I
    ((finiteTypeSheavesSpecModuleEquivalence (closedRing R I)).functor.obj M) r hr _

/-- Actual sheaf pushforward, with its codomain restricted to annihilated
objects rather than the larger supported category. -/
def coherentPushforwardToKilled :
    FiniteTypeSheaves (Spec (closedRing R I)) ⥤ (finiteTypeSheavesKilledBy R I).FullSubcategory :=
  ObjectProperty.lift _ (coherentPushforward R I) (coherentPushforward_killed R I)

/-- Forgetting the annihilation proof recovers actual finite-type sheaf pushforward. -/
theorem coherentPushforwardToKilled_comp_inclusion :
    coherentPushforwardToKilled R I ⋙ (finiteTypeSheavesKilledBy R I).ι =
      coherentPushforward R I := rfl

/-- The comparison square restricts to the actual annihilated full subcategories. -/
def coherentPushforwardToKilledSquare :
    coherentPushforwardToKilled R I ⋙ (killedModuleEquivalence R I).functor ≅
      (finiteTypeSheavesSpecModuleEquivalence (closedRing R I)).functor ⋙ closedToKilled I :=
  ((killedBy I).fullyFaithfulι.whiskeringRight _).preimageIso (coherentPushforwardSquare R I)

instance coherentPushforwardToKilled_full : (coherentPushforwardToKilled R I).Full :=
  Functor.Full.of_comp_faithful_iso (coherentPushforwardToKilledSquare R I)

instance coherentPushforwardToKilled_faithful : (coherentPushforwardToKilled R I).Faithful :=
  Functor.Faithful.of_comp_iso (coherentPushforwardToKilledSquare R I)

instance coherentPushforwardToKilled_essSurj : (coherentPushforwardToKilled R I).EssSurj := by
  have : (coherentPushforwardToKilled R I ⋙ (killedModuleEquivalence R I).functor).EssSurj :=
    Functor.essSurj_of_iso (coherentPushforwardToKilledSquare R I).symm
  exact Functor.essSurj_of_comp_fully_faithful (coherentPushforwardToKilled R I)
    (killedModuleEquivalence R I).functor

instance coherentPushforwardToKilled_isEquivalence :
    (coherentPushforwardToKilled R I).IsEquivalence := {}

/-- The equivalence onto exactly the I-annihilated coherent objects, induced
by the actual geometric closed pushforward. -/
def coherentClosedEquivalence :
    FiniteTypeSheaves (Spec (closedRing R I)) ≌ (finiteTypeSheavesKilledBy R I).FullSubcategory :=
  (coherentPushforwardToKilled R I).asEquivalence

instance coherentKilled_hasFiniteProducts :
    HasFiniteProducts (finiteTypeSheavesKilledBy R I).FullSubcategory where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence (coherentClosedEquivalence R I).inverse

/-- The annihilated category is abelian via its proved actual closed-sheaf
equivalence, without claiming that it is a Serre subcategory. -/
instance instAbelianCoherentKilledBy : Abelian (finiteTypeSheavesKilledBy R I).FullSubcategory :=
  abelianOfEquivalence (coherentClosedEquivalence R I).inverse

instance coherentPushforwardToKilled_additive : (coherentPushforwardToKilled R I).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (coherentPushforwardToKilled R I)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Actual closed pushforward is exact as an equivalence onto the annihilated
coherent category equipped with its standard abelian exact structure. -/
def coherentPushforwardToKilledExact :
    ExactFunctor (coherentExactStructure (Spec (closedRing R I)))
      (abelianExactStructure (finiteTypeSheavesKilledBy R I).FullSubcategory) where
  toFunctor := coherentPushforwardToKilled R I
  map_conflation _ h := h.map_of_exact _

/-- The equivalence is induced by actual geometric pushforward. -/
theorem coherentClosedEquivalence_comp_inclusion :
    (coherentClosedEquivalence R I).functor ⋙ (finiteTypeSheavesKilledBy R I).ι =
      coherentPushforward R I := rfl

/-- The annihilated finite-type sheaf inclusion is the actual pushforward composed
with the inverse of its proved equivalence. -/
def coherentKilledInclusionComparison :
    (coherentClosedEquivalence R I).inverse ⋙ coherentPushforward R I ≅
      (finiteTypeSheavesKilledBy R I).ι := by
  change (coherentClosedEquivalence R I).inverse ⋙
      ((coherentClosedEquivalence R I).functor ⋙ (finiteTypeSheavesKilledBy R I).ι) ≅ _
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (coherentClosedEquivalence R I).counitIso _ ≪≫
      Functor.leftUnitor _

instance coherentKilledInclusion_preservesFiniteLimits :
    PreservesFiniteLimits (finiteTypeSheavesKilledBy R I).ι :=
  preservesFiniteLimits_of_natIso (coherentKilledInclusionComparison R I)

instance coherentKilledInclusion_preservesFiniteColimits :
    PreservesFiniteColimits (finiteTypeSheavesKilledBy R I).ι :=
  preservesFiniteColimits_of_natIso (coherentKilledInclusionComparison R I)

/-- Inclusion of the annihilated coherent subcategory is exact. -/
def coherentKilledInclusionExact :
    ExactFunctor (abelianExactStructure (finiteTypeSheavesKilledBy R I).FullSubcategory)
      (coherentExactStructure (Spec R)) where
  toFunctor := (finiteTypeSheavesKilledBy R I).ι
  map_conflation _ h := h.map_of_exact _

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal
