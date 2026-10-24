/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Actual scalar restriction along a map of constant coefficient rings -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

attribute [local instance] hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard

variable (X : Scheme.{u}) {Λ Γ : Type (u + 1)} [Ring Λ] [Ring Γ] (φ : Λ →+* Γ)

/-- The actual constant ring sheaf map induced by the given ring homomorphism. -/
def constantRingCoefficientMap : constantRing X Λ ⟶ constantRing X Γ :=
  (constantSheaf (Scheme.smallEtaleTopology X) RingCat.{u + 1}).map (RingCat.ofHom φ)

/-- The ring coefficient map retains the original constant-sheaf units. -/
@[reassoc]
theorem constantRingCoefficientMap_unit :
    constantRingUnit X Λ ≫ (constantRingCoefficientMap X φ).hom =
      (Functor.const X.Etaleᵒᵖ).map (RingCat.ofHom φ) ≫ constantRingUnit X Γ :=
  (CategoryTheory.toSheafify_naturality (Scheme.smallEtaleTopology X)
    ((Functor.const X.Etaleᵒᵖ).map (RingCat.ofHom φ))).symm

/-- Restriction along the actual map of sheaves of constant rings. -/
def moduleRestrictScalars : ModuleSheaf X Γ ⥤ ModuleSheaf X Λ :=
  SheafOfModules.restrictScalars (constantRingCoefficientMap X φ)

/-- Pointwise restriction of scalars on original module-valued sheaves. -/
def moduleValuedRestrictScalars : ModuleValuedSheaf X Γ ⥤ ModuleValuedSheaf X Λ :=
  sheafCompose (Scheme.smallEtaleTopology X) (ModuleCat.restrictScalars.{u + 1} φ)

/-- Sectionwise scalar restriction is the original composition of ring maps. -/
def moduleRestrictScalarsComparisonComponent (M : ModuleSheaf X Γ) (U : X.Etaleᵒᵖ) :
    (((moduleSheafEquivalence X Λ).inverse.obj
      ((moduleRestrictScalars X φ).obj M)).obj.obj U) ≅
    (((moduleValuedRestrictScalars X φ).obj
      ((moduleSheafEquivalence X Γ).inverse.obj M)).obj.obj U) := by
  have h := congrArg (fun a => a.app U) (constantRingCoefficientMap_unit X φ)
  let N := ModuleCat.of ((constantRing X Γ).obj.obj U) (M.val.obj U)
  exact (ModuleCat.restrictScalarsComp'App
    ((constantRingUnit X Λ).app U).hom ((constantRingCoefficientMap X φ).hom.app U).hom
    (((constantRingUnit X Γ).app U).hom.comp φ)
    (congrArg RingCat.Hom.hom h.symm) N).symm ≪≫
      (ModuleCat.restrictScalarsComp φ ((constantRingUnit X Γ).app U).hom).app N

/-- Native scalar restriction commutes with the actual inverse coefficient equivalence. -/
def moduleRestrictScalarsComparison :
    moduleRestrictScalars X φ ⋙ (moduleSheafEquivalence X Λ).inverse ≅
      (moduleSheafEquivalence X Γ).inverse ⋙ moduleValuedRestrictScalars X φ :=
  NatIso.ofComponents (fun M => ObjectProperty.isoMk _
    (NatIso.ofComponents (moduleRestrictScalarsComparisonComponent X φ M)
      (by intros; ext x; rfl)))
    (by intros; apply ObjectProperty.hom_ext; ext U x; rfl)

/-- The native scalar restriction has exactly the transported module-valued realization. -/
def moduleRestrictScalarsTransportIso :
    moduleRestrictScalars X φ ≅
      (moduleSheafEquivalence X Γ).inverse ⋙ moduleValuedRestrictScalars X φ ⋙
        (moduleSheafEquivalence X Λ).functor :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (moduleSheafEquivalence X Λ).counitIso.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleRestrictScalarsComparison X φ) _ ≪≫
    Functor.associator _ _ _

/-- Scalar restriction preserves the sheafification class on the actual étale site. -/
theorem moduleRestrictScalars_preservesSheafification :
    (Scheme.smallEtaleTopology X).PreservesSheafification
      (ModuleCat.restrictScalars.{u + 1} φ) where
  le := by
    intro P Q α hα
    let J := Scheme.smallEtaleTopology X
    let R := ModuleCat.restrictScalars.{u + 1} φ
    let : J.WEqualsLocallyBijective (ModuleCat.{u + 1} Λ) := by infer_instance
    have ht : J.W (Functor.whiskerRight α (CategoryTheory.forget (ModuleCat.{u + 1} Γ))) :=
      J.W_of_preservesSheafification (CategoryTheory.forget (ModuleCat.{u + 1} Γ)) α hα
    have hi : Presheaf.IsLocallyInjective J (Functor.whiskerRight α R) :=
      (Presheaf.isLocallyInjective_forget_iff J _).mp ht.isLocallyInjective
    have hs : Presheaf.IsLocallySurjective J (Functor.whiskerRight α R) :=
      (Presheaf.isLocallySurjective_iff_whisker_forget J _).mpr ht.isLocallySurjective
    exact (J.W_iff_isLocallyBijective (Functor.whiskerRight α R)).mpr ⟨hi, hs⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
