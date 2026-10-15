/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.ModuleCat.Finite
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.CategoryTheory.Abelian.Transfer
/-!
# Finite modules on an arbitrary closed subscheme

Restriction of scalars along R → R/I is an actual exact fully faithful functor.
Its essential image consists precisely of finite R-modules annihilated by I.
Comparing this category with modules annihilated by a power of I requires
dévissage, rather than a categorical equivalence.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ExactCategory
open ModuleCat
attribute [local instance] Abelian.hasFiniteBiproducts
namespace ModuleCat.FiniteLocalization.IdealClosedSupport
variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The coordinate ring of the closed subscheme V(I). -/
abbrev ClosedRing := R ⧸ I

/-- Finite modules annihilated by every element of I. -/
def killedBy : ObjectProperty (FGModuleCat.{u} R) := fun M ↦ ∀ r ∈ I, ∀ m : M, r • m = 0

/-- Annihilation by I is equivalent to containment in the module annihilator. -/
theorem killedBy_iff_le_annihilator (M : FGModuleCat.{u} R) :
    killedBy I M ↔ I ≤ Module.annihilator R M := by
  simp only [killedBy, SetLike.le_def, Module.mem_annihilator]

/-- The ideal-annihilation condition has the standard quotient-module API. -/
theorem killedBy_iff_isTorsionBySet (M : FGModuleCat.{u} R) :
    killedBy I M ↔ Module.IsTorsionBySet R M I := by
  constructor
  · exact fun h {m} {r} ↦ h r r.property m
  · exact fun h r hr m ↦ @h m ⟨r, hr⟩

/-- Annihilation is unchanged by an isomorphism of finite modules. -/
instance killedBy_isoClosed : (killedBy I).IsClosedUnderIsomorphisms where
  of_iso e h := by
    intro r hr n
    obtain ⟨m, rfl⟩ := (FGModuleCat.isoToLinearEquiv e).surjective n
    rw [← map_smul, h r hr m, map_zero]

/-- Actual restriction of scalars along the quotient ring map. -/
def closedRestriction : FGModuleCat.{u} (ClosedRing I) ⥤ FGModuleCat.{u} R :=
  ObjectProperty.lift _
    (forget₂ (FGModuleCat (ClosedRing I)) (ModuleCat (ClosedRing I)) ⋙
      ModuleCat.restrictScalars (Ideal.Quotient.mk I)) (fun M ↦ by
    change Module.Finite R ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M.obj)
    let N := (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M.obj
    have : Module.Finite (ClosedRing I) N := M.property
    have : IsScalarTower R (ClosedRing I) N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    exact Module.Finite.trans (ClosedRing I) N)

@[simp] theorem closedRestriction_obj_obj (M : FGModuleCat.{u} (ClosedRing I)) :
    ((closedRestriction I).obj M).obj =
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M.obj := rfl

@[simp] theorem closedRestriction_map_hom {M N : FGModuleCat.{u} (ClosedRing I)} (g : M ⟶ N) :
    ((closedRestriction I).map g).hom =
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).map g.hom := rfl

/-- Every quotient-ring module is annihilated by every element of the defining ideal. -/
theorem closedRestriction_killed (M : FGModuleCat.{u} (ClosedRing I)) :
    killedBy I ((closedRestriction I).obj M) := by
  intro r hr m
  change M at m
  change (Ideal.Quotient.mk I r) • (m : M) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]

/-- Restriction of scalars, with codomain restricted to the actual annihilated objects. -/
def closedToKilled : FGModuleCat.{u} (ClosedRing I) ⥤ (killedBy I).FullSubcategory :=
  ObjectProperty.lift _ (closedRestriction I) (closedRestriction_killed I)

/-- Surjectivity of R → R/I makes quotient-ring linearity recoverable from R-linearity. -/
def fullyFaithfulClosedRestriction : (closedRestriction I).FullyFaithful where
  preimage {M N} g := FGModuleCat.ofHom
    { toFun := g.hom.hom
      map_add' := g.hom.hom.map_add
      map_smul' := by
        intro a m
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact g.hom.hom.map_smul r m }

instance closedRestriction_full : (closedRestriction I).Full := (fullyFaithfulClosedRestriction
  I).full
instance closedRestriction_faithful : (closedRestriction I).Faithful :=
  (fullyFaithfulClosedRestriction I).faithful

instance closedToKilled_full : (closedToKilled I).Full := by
  constructor
  intro M N g
  obtain ⟨h, hh⟩ := (closedRestriction I).map_surjective g.hom
  exact ⟨h, ObjectProperty.hom_ext _ hh⟩

instance closedToKilled_faithful : (closedToKilled I).Faithful where
  map_injective h := (closedRestriction I).map_injective (congrArg (fun k ↦ k.hom) h)

/-- Every finite annihilated R-module has its genuine quotient-ring module structure. -/
instance closedToKilled_essSurj : (closedToKilled I).EssSurj where
  mem_essImage M := by
    have hM : Module.IsTorsionBySet R M.obj I := fun {m} {r} ↦ M.property r r.property m
    let : Module (ClosedRing I) M.obj := hM.module
    let : IsScalarTower R (ClosedRing I) M.obj :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    let : Module.Finite (ClosedRing I) M.obj :=
      Module.Finite.of_restrictScalars_finite R (ClosedRing I) M.obj
    refine ⟨FGModuleCat.of (ClosedRing I) M.obj, ⟨?_⟩⟩
    apply ObjectProperty.isoMk
    apply ObjectProperty.isoMk
    exact (LinearEquiv.refl R M.obj).toModuleIso

instance closedToKilled_isEquivalence : (closedToKilled I).IsEquivalence := {}

/-- The actual quotient-ring restriction equivalence onto exactly the I-annihilated objects. -/
def closedEquivalence : FGModuleCat.{u} (ClosedRing I) ≌ (killedBy I).FullSubcategory :=
  (closedToKilled I).asEquivalence

/-- This equivalence followed by the full inclusion is the actual restriction of scalars. -/
theorem closedEquivalence_comp_inclusion :
    (closedEquivalence I).functor ⋙ (killedBy I).ι = closedRestriction I := rfl

instance closedRestriction_additive : (closedRestriction I).Additive where
  map_add := by intros; apply FGModuleCat.hom_ext; rfl

instance closedToKilled_additive : (closedToKilled I).Additive where
  map_add := by intros; apply ObjectProperty.hom_ext; apply FGModuleCat.hom_ext; rfl

variable [IsNoetherianRing R]

instance closedRestriction_preservesFiniteLimits : PreservesFiniteLimits (closedRestriction I) := by
  have : PreservesFiniteLimits
      (closedRestriction I ⋙ forget₂ (FGModuleCat R) (ModuleCat R)) := by
    change PreservesFiniteLimits
      (forget₂ (FGModuleCat (ClosedRing I)) (ModuleCat (ClosedRing I)) ⋙
        ModuleCat.restrictScalars (Ideal.Quotient.mk I))
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (closedRestriction I)
    (forget₂ (FGModuleCat R) (ModuleCat R))

instance closedRestriction_preservesFiniteColimits : PreservesFiniteColimits (closedRestriction I)
  := by
  have : PreservesFiniteColimits
      (closedRestriction I ⋙ forget₂ (FGModuleCat R) (ModuleCat R)) := by
    change PreservesFiniteColimits
      (forget₂ (FGModuleCat (ClosedRing I)) (ModuleCat (ClosedRing I)) ⋙
        ModuleCat.restrictScalars (Ideal.Quotient.mk I))
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves (closedRestriction I)
    (forget₂ (FGModuleCat R) (ModuleCat R))

/-- The genuine closed pushforward on finite modules is exact. -/
def closedRestrictionExact :
    ExactFunctor (ModuleCat.finiteModuleExactStructure.{u, u} (ClosedRing I))
      (ModuleCat.finiteModuleExactStructure.{u, u} R) where
  toFunctor := closedRestriction I
  map_conflation _ h := h.map_of_exact _

instance killed_hasFiniteProducts : HasFiniteProducts (killedBy I).FullSubcategory where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence (closedEquivalence I).inverse

/-- The annihilated subcategory is abelian, although it is not generally Serre
inside all finite R-modules: extensions may only be annihilated by I². -/
instance instAbelianKilledBy : Abelian (killedBy I).FullSubcategory :=
  abelianOfEquivalence (closedEquivalence I).inverse

/-- The actual quotient equivalence is an exact functor for standard abelian structures. -/
def closedToKilledExact :
    ExactFunctor (ModuleCat.finiteModuleExactStructure.{u, u} (ClosedRing I))
      (abelianExactStructure (killedBy I).FullSubcategory) where
  toFunctor := closedToKilled I
  map_conflation _ h := h.map_of_exact _

/-- The killed subcategory inclusion is the actual restriction of scalars,
composed with the inverse of the proved quotient equivalence. -/
def killedInclusionComparison :
    (closedEquivalence I).inverse ⋙ closedRestriction I ≅ (killedBy I).ι := by
  change (closedEquivalence I).inverse ⋙ ((closedEquivalence I).functor ⋙ (killedBy I).ι) ≅ _
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (closedEquivalence I).counitIso _ ≪≫ Functor.leftUnitor _

instance killedInclusion_preservesFiniteLimits : PreservesFiniteLimits (killedBy I).ι :=
  preservesFiniteLimits_of_natIso (killedInclusionComparison I)

instance killedInclusion_preservesFiniteColimits : PreservesFiniteColimits (killedBy I).ι :=
  preservesFiniteColimits_of_natIso (killedInclusionComparison I)

/-- The inclusion of the killed subcategory into finite R-modules is genuinely exact. -/
def killedInclusionExact : ExactFunctor (abelianExactStructure (killedBy I).FullSubcategory)
    (ModuleCat.finiteModuleExactStructure.{u, u} R) where
  toFunctor := (killedBy I).ι
  map_conflation _ h := h.map_of_exact _

end ModuleCat.FiniteLocalization.IdealClosedSupport
