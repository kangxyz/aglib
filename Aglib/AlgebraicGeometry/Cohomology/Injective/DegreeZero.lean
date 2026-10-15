/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.InjectiveComplex
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
/-! # Degree-zero section homology of actual injective resolutions

Original sheaf sections identify with degree-zero homology of the section
complex of any actual injective resolution. These identifications commute
with the literal two-open restriction difference.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace AlgebraicGeometry.Scheme.Modules
open TwoOpen

instance sectionsFunctor_preservesFiniteLimits (X : Scheme.{u}) (U : X.Opens) :
    PreservesFiniteLimits (sectionsFunctor X U) := by
  change PreservesFiniteLimits (Scheme.Modules.toPresheaf X ⋙
    (evaluation _ AddCommGrpCat).obj (Opposite.op U))
  let : PreservesFiniteLimits ((evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op U)) :=
    { preservesFiniteLimits _ _ _ := inferInstance }
  exact comp_preservesFiniteLimits (Scheme.Modules.toPresheaf X)
    ((evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op U))

variable {X : Scheme.{u}} (M : X.Modules) (I : InjectiveResolution M)

/-- The original augmentation into zero-th homology after an additive functor. -/
def resolutionHomologyZeroMap (F : X.Modules ⥤ AddCommGrpCat.{u}) [F.Additive] :
    F.obj M ⟶ ((F.mapHomologicalComplex _).obj I.cocomplex).homology 0 :=
  I.toRightDerivedZero' F ≫
    (((F.mapHomologicalComplex _).obj I.cocomplex).homologyπ 0)

lemma resolutionHomologyZeroMap_naturality
    {F G : X.Modules ⥤ AddCommGrpCat.{u}} [F.Additive] [G.Additive] (α : F ⟶ G) :
    α.app M ≫ resolutionHomologyZeroMap M I G =
      resolutionHomologyZeroMap M I F ≫
        homologyMap ((NatTrans.mapHomologicalComplex α _).app I.cocomplex) 0 := by
  have h : α.app M ≫ I.toRightDerivedZero' G =
      I.toRightDerivedZero' F ≫
        cyclesMap ((NatTrans.mapHomologicalComplex α _).app I.cocomplex) 0 := by
    apply (cancel_mono (iCycles ((G.mapHomologicalComplex _).obj I.cocomplex) 0)).mp
    rw [Category.assoc, CategoryTheory.InjectiveResolution.toRightDerivedZero'_comp_iCycles,
      Category.assoc, cyclesMap_i, ← Category.assoc,
      CategoryTheory.InjectiveResolution.toRightDerivedZero'_comp_iCycles]
    exact (α.naturality (I.ι.f 0)).symm
  unfold resolutionHomologyZeroMap
  rw [← Category.assoc, h, Category.assoc, ← homologyπ_naturality, ← Category.assoc]

/-- Degree-zero sections compared using the original resolution augmentation. -/
def sectionsHomologyZeroIso (U : X.Opens) :
    Γ(M, U) ≅
      (((sectionsFunctor X U).mapHomologicalComplex _).obj I.cocomplex).homology 0 :=
  asIso (I.toRightDerivedZero' (sectionsFunctor X U)) ≪≫ CochainComplex.isoHomologyπ₀ _

instance pair_toRightDerivedZero_isIso (U V : X.Opens) :
    IsIso (I.toRightDerivedZero' (pairFunctor X U V)) := by
  dsimp [InjectiveResolution.toRightDerivedZero']
  rw [CochainComplex.isIso_liftCycles_iff]
  have h (W : X.Opens) : ((ShortComplex.mk (I.ι.f 0) (I.cocomplex.d 0 1)
      I.ι_f_zero_comp_complex_d).map (sectionsFunctor X W)).Exact :=
    ShortComplex.exact_of_f_is_kernel _
      (KernelFork.mapIsLimit _ I.isLimitKernelFork (sectionsFunctor X W))
  have hU := h U
  have hV := h V
  constructor
  · rw [ShortComplex.ab_exact_iff]
    rintro ⟨a, b⟩ hab
    obtain ⟨c, hc⟩ := (ShortComplex.ab_exact_iff _).mp hU a (congrArg Prod.fst hab)
    obtain ⟨d, hd⟩ := (ShortComplex.ab_exact_iff _).mp hV b (congrArg Prod.snd hab)
    exact ⟨(c, d), Prod.ext hc hd⟩
  · apply (AddCommGrpCat.mono_iff_injective _).mpr
    intro a b hab
    apply Prod.ext
    · exact (AddCommGrpCat.mono_iff_injective ((sectionsFunctor X U).map (I.ι.f 0))).mp
        inferInstance (congrArg Prod.fst hab)
    · exact (AddCommGrpCat.mono_iff_injective ((sectionsFunctor X V).map (I.ι.f 0))).mp
        inferInstance (congrArg Prod.snd hab)

/-- Degree-zero pairs of sections compared through the original augmentation. -/
def pairHomologyZeroIso (U V : X.Opens) :
    AddCommGrpCat.of (Γ(M, U) × Γ(M, V)) ≅
      (((pairFunctor X U V).mapHomologicalComplex _).obj I.cocomplex).homology 0 :=
  asIso (I.toRightDerivedZero' (pairFunctor X U V)) ≪≫ CochainComplex.isoHomologyπ₀ _

lemma difference_homologyZero_naturality (U V : X.Opens) :
    (sectionSequence M U V).g ≫ (sectionsHomologyZeroIso M I (U ⊓ V)).hom =
      (pairHomologyZeroIso M I U V).hom ≫
        homologyMap (cochainSequence U V I.cocomplex).g 0 :=
  resolutionHomologyZeroMap_naturality M I (differenceNat X U V)

end AlgebraicGeometry.Scheme.Modules
