/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Underlying
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Original scalar restriction for constant-ring sheaves

The given ring map induces the original constant-ring coefficient map.
All comparisons retain the actual sectionwise restriction of scalars and
the original coefficient equivalences.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Sheaf.ConstantRing

universe u v r w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {Λ Γ : Type r} [Ring Λ] [Ring Γ] (φ : Λ →+* Γ)
  [HasWeakSheafify J RingCat.{r}]

/-- The same constant-ring map induced by the actual scalar homomorphism. -/
def constantRingCoefficientMap : constantRing J Λ ⟶ constantRing J Γ :=
  (constantSheaf J RingCat.{r}).map (RingCat.ofHom φ)

/-- The coefficient map retains the original two sheafification units. -/
@[reassoc]
theorem constantRingCoefficientMap_unit :
    constantRingUnit J Λ ≫ (constantRingCoefficientMap J φ).hom =
      (Functor.const Cᵒᵖ).map (RingCat.ofHom φ) ≫ constantRingUnit J Γ :=
  (CategoryTheory.toSheafify_naturality J
    ((Functor.const Cᵒᵖ).map (RingCat.ofHom φ))).symm

/-- Actual native ringed restriction along this same coefficient map. -/
def moduleRestrictScalars :
    ModuleSheaf.{u, v, r, w} J Γ ⥤ ModuleSheaf.{u, v, r, w} J Λ :=
  SheafOfModules.restrictScalars (constantRingCoefficientMap J φ)

variable [J.HasSheafCompose (ModuleCat.restrictScalars.{w} φ)]

/-- Actual pointwise restriction on the original module-valued sheaves. -/
def moduleValuedRestrictScalars :
    ModuleValuedSheaf.{u, v, r, w} J Γ ⥤ ModuleValuedSheaf.{u, v, r, w} J Λ :=
  sheafCompose J (ModuleCat.restrictScalars.{w} φ)

section Comparison

variable [J.WEqualsLocallyBijective RingCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Γ) AddCommGrpCat.{w})]

/-- The component is the original composition of the two scalar ring maps. -/
def moduleRestrictScalarsComparisonComponent
    (M : ModuleSheaf.{u, v, r, w} J Γ) (U : Cᵒᵖ) :
    (((moduleSheafEquivalence J Λ).inverse.obj
      ((moduleRestrictScalars J φ).obj M)).obj.obj U) ≅
    (((moduleValuedRestrictScalars J φ).obj
      ((moduleSheafEquivalence J Γ).inverse.obj M)).obj.obj U) := by
  have h := congrArg (fun a => a.app U) (constantRingCoefficientMap_unit J φ)
  let N := ModuleCat.of ((constantRing J Γ).obj.obj U) (M.val.obj U)
  exact (ModuleCat.restrictScalarsComp'App
    ((constantRingUnit J Λ).app U).hom ((constantRingCoefficientMap J φ).hom.app U).hom
    (((constantRingUnit J Γ).app U).hom.comp φ)
    (congrArg RingCat.Hom.hom h.symm) N).symm ≪≫
      (ModuleCat.restrictScalarsComp φ ((constantRingUnit J Γ).app U).hom).app N

/-- Both coefficient equivalences see exactly the original section maps. -/
def moduleRestrictScalarsComparison :
    moduleRestrictScalars J φ ⋙ (moduleSheafEquivalence J Λ).inverse ≅
      (moduleSheafEquivalence J Γ).inverse ⋙ moduleValuedRestrictScalars J φ :=
  NatIso.ofComponents (fun M => ObjectProperty.isoMk _
    (NatIso.ofComponents (moduleRestrictScalarsComparisonComponent J φ M)
      (by intros; ext x; rfl)))
    (by intros; apply ObjectProperty.hom_ext; ext U x; rfl)

/-- The actual ringed restriction is identified by those same components. -/
def moduleRestrictScalarsTransportIso :
    moduleRestrictScalars J φ ≅
      (moduleSheafEquivalence J Γ).inverse ⋙ moduleValuedRestrictScalars J φ ⋙
        (moduleSheafEquivalence J Λ).functor :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (moduleSheafEquivalence J Λ).counitIso.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleRestrictScalarsComparison J φ) _ ≪≫
    Functor.associator _ _ _

end Comparison

section Sheafification

variable [J.WEqualsLocallyBijective (Type w)]
  [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)]
  [J.PreservesSheafification (CategoryTheory.forget (ModuleCat.{w} Γ))]

omit [HasWeakSheafify J RingCat.{r}]
  [J.HasSheafCompose (ModuleCat.restrictScalars.{w} φ)] in
/-- The actual scalar-restriction functor preserves the original
sheafification class, as detected on the same underlying types. -/
theorem moduleRestrictScalars_preservesSheafification :
    J.PreservesSheafification (ModuleCat.restrictScalars.{w} φ) where
  le := by
    intro P Q α hα
    let R := ModuleCat.restrictScalars.{w} φ
    have ht : J.W (Functor.whiskerRight α (CategoryTheory.forget (ModuleCat.{w} Γ))) :=
      J.W_of_preservesSheafification (CategoryTheory.forget (ModuleCat.{w} Γ)) α hα
    have hi : Presheaf.IsLocallyInjective J (Functor.whiskerRight α R) :=
      (Presheaf.isLocallyInjective_forget_iff J _).mp ht.isLocallyInjective
    have hs : Presheaf.IsLocallySurjective J (Functor.whiskerRight α R) :=
      (Presheaf.isLocallySurjective_iff_whisker_forget J _).mpr ht.isLocallySurjective
    exact (J.W_iff_isLocallyBijective (Functor.whiskerRight α R)).mpr ⟨hi, hs⟩

end Sheafification

end ModuleCat.Sheaf.ConstantRing
