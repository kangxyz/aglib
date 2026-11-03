/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.MaximalModel
public import Aglib.AlgebraicGeometry.Cohomology.Proper.FibreDimension.Local

/-!
# Rationality at the actual stalks of proper birational models

Universal original H1 vanishing over a Nagata local surface propagates
to the actual closed nongeneric stalks of every normal proper birational model.
Local replacement retains each supplied local modification. The original Leray
triangle, local formal-functions vanishing and finite closed support kill its
original R1. Neither completeness nor a resolution is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Cohomology

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities

/-- The standard derived-category instance for the original scheme module sheaves. -/
local instance rationalPropagationSource (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The standard derived-category instance for modules over the original coefficient ring. -/
local instance rationalPropagationTarget (R : Type u) [CommRing R] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _

/-- The original Leray edge and its actual finite closed support kill R1
when the original upstairs H1 and downstairs H2 vanish. -/
theorem original_R1_isZero_of_structureH1_structureH2
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X) [IsProper g] [IsDominant g]
    (hX : NormalStalks X) (hdX : topologicalKrullDim X ≤ 2)
    (hgf : IsIso (CommRingCat.ofHom (functionFieldMap g)))
    (hY₁ : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf Y (SheafOfModules.unit Y.ringCatSheaf)) 1))
    (hX₂ : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf)) 2)) :
    IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj
      (FiniteTraceCoordinates.structureModule Y)) := by
  let α : Γ(X, ⊤) →+* Γ(X, ⊤) := RingHom.id _
  let T := moduleBirationalLerayTriangle X α g hX hgf
  let S := moduleBirationalLerayShortComplex X α g hX hgf
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let := moduleCohomologyModuleOfHom X α OX 2
  let e₂ := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α
    (injectiveResolution OX) 2
  have h₂ : IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) 2).obj
      T.obj₁) := ModuleCat.isZero_iff_subsingleton.mpr
    ⟨fun a b ↦ e₂.injective (@Subsingleton.elim _ hX₂ _ _)⟩
  let : Epi S.g := by
    change Epi ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) 1).map
      T.mor₂)
    let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) 0
    exact (H.homologySequence_epi_shift_map_mor₂_iff T
        (moduleBirationalLerayTriangle_distinguished X α g hX hgf) 1 2 (by omega)).mpr
      (h₂.eq_of_tgt _ _)
  let : Subsingleton S.X₂ :=
    ⟨fun a b ↦ (moduleBirationalLerayMiddleEquiv X α g hX hgf).injective
      (@Subsingleton.elim _ hY₁ _ _)⟩
  have h₃ : Subsingleton S.X₃ := by
    constructor
    intro a b
    obtain ⟨a', rfl⟩ := (ModuleCat.epi_iff_surjective S.g).mp inferInstance a
    obtain ⟨b', rfl⟩ := (ModuleCat.epi_iff_surjective S.g).mp inferInstance b
    exact congrArg S.g (Subsingleton.elim a' b')
  let e := (moduleBirationalLerayEdgeIso X α g hX hgf).toLinearEquiv
  have hΓ : Subsingleton ((moduleGlobalSectionsFunctorOfHom X α).obj
      (((Scheme.Modules.pushforward g).rightDerived 1).obj
        (FiniteTraceCoordinates.structureModule Y))) :=
    ⟨fun a b ↦ e.symm.injective (@Subsingleton.elim _ h₃ _ _)⟩
  obtain ⟨_, C, hC, hclosed, hsupp⟩ :=
    original_R1_coherent_finite_closed_support g hX hdX hgf
  exact module_isZero_of_finite_closed_support_of_sections_subsingleton X α _
    C hC hclosed hsupp hΓ

/-- Every closed nongeneric stalk of an actual normal proper birational
model of a rational Nagata local surface has universal original H1 vanishing.
Completeness and a chosen resolution are not premises. -/
theorem normalModificationH1Vanishing_stalk_of_normalModificationH1Vanishing
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : IsNagataRing.{u, 0} A) (hdA : ringKrullDim A = 2)
    (hrat : NormalModificationH1Vanishing A)
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] [IsDominant f]
    (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (x : X) (hx : IsClosed ({x} : Set X)) (hxη : x ≠ genericPoint X) :
    letI : IsDomain (X.presheaf.stalk x) := (hX x).1
    NormalModificationH1Vanishing (X.presheaf.stalk x) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian f }
  have hdX : topologicalKrullDim X ≤ 2 := actualModel_dimension_of_nagata f hA hdA.le hff
  have hne : (IsLocalRing.closedPoint A : Spec (.of A)) ≠
      genericPoint (Spec (.of A)) := by
    intro he
    have hfld : IsField ((Spec (.of A)).presheaf.stalk (IsLocalRing.closedPoint A)) :=
      he.symm ▸ Field.toIsField (Spec (.of A)).functionField
    have hfldA : IsField A :=
      (stalkClosedPointIso (.of A)).symm.commRingCatIsoToRingEquiv.isField hfld
    have hh := ringKrullDim_eq_zero_of_isField hfldA
    rw [hdA] at hh
    norm_num at hh
  have hX₂ : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf)) 2) :=
    subsingleton_moduleCohomology_of_local_of_dim_firstThickening f
      (SheafOfModules.unit X.ringCatSheaf) (affineLocallyFiniteType_unit X) 1 2
      (closedFibre_dim_le_one_of_integral_source f hdX hne) (by decide)
  apply normalModificationH1Vanishing_stalk_of_original_R1_vanishing X hX hdX _ x hx hxη
  intro Y hY g hg hdom hYN hgf
  let : IsIntegral Y := hY
  let : IsProper g := hg
  let : IsDominant g := hdom
  let : IsIso (CommRingCat.ofHom (functionFieldMap f)) := hff
  let : IsIso (CommRingCat.ofHom (functionFieldMap g)) := hgf
  have hcomp : IsIso (CommRingCat.ofHom (functionFieldMap (g ≫ f))) := by
    rw [functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance
  exact original_R1_isZero_of_structureH1_structureH2 X g hX hdX hgf
    (hrat Y (g ≫ f) hYN hcomp) hX₂

end AlgebraicGeometry.Scheme.RationalSingularities
