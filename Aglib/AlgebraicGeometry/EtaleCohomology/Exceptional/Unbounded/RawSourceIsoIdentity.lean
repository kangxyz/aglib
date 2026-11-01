/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIsoCompatibility
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenBaseChangeIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawIdentityComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionModel

/-! # Actual reflexive source transport on full unbounded raw compactifications -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u dX dM dS
variable {X M : Scheme.{u}} (j : X ⟶ M) [IsOpenImmersion j]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{dX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{dM} (ModuleSheaf M Λ)]

private theorem lowerSource_identity_aux (i : X ⟶ M) [IsOpenImmersion i]
    (hi : i = j) (sq : IsPullback (𝟙 X) i j (𝟙 M)) :
    (Functor.rightUnitor (moduleUnboundedDerivedLowerShriek j Λ)).symm ≪≫
      Functor.isoWhiskerLeft (moduleUnboundedDerivedLowerShriek j Λ)
        (moduleUnboundedDerivedInverseImageIdIso Λ M).symm ≪≫
      moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso (𝟙 X) i j (𝟙 M) sq Λ ≪≫
      Functor.isoWhiskerRight (moduleUnboundedDerivedInverseImageIdIso Λ X)
        (moduleUnboundedDerivedLowerShriek i Λ) ≪≫ Functor.leftUnitor _ ≪≫
      eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ hi) = Iso.refl _ := by
  subst i
  have h := moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso_identity_source
    j j (𝟙 M) sq.flip Λ
  rw [moduleUnboundedDerivedProperRefinementPullbackIso_id] at h
  simp only [eqToIso_refl, Iso.trans_refl]
  rw [← h, ← Functor.isoWhiskerLeft_symm]
  simp only [Iso.symm_self_id_assoc, Iso.symm_self_id]

/-- The original source map normalizes at reflexivity, retaining the actual geometric equality. -/
theorem moduleUnboundedDerivedLowerShriekSourceIso_refl :
    moduleUnboundedDerivedLowerShriekSourceIso (Iso.refl X) j Λ ≪≫
      Functor.isoWhiskerRight (moduleUnboundedDerivedInverseImageIdIso Λ X)
        (moduleUnboundedDerivedLowerShriek ((𝟙 X) ≫ j) Λ) ≪≫
      Functor.leftUnitor _ ≪≫
      eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ (Category.id_comp j)) = Iso.refl _ := by
  simpa only [moduleUnboundedDerivedLowerShriekSourceIso, Iso.refl_hom, Iso.trans_assoc] using
    lowerSource_identity_aux j Λ (𝟙 X ≫ j) (Category.id_comp j)
      (isPullback_sourceIsoOpen (Iso.refl X) j)

section Raw
variable {S : Scheme.{u}} {f : X ⟶ S} (C : Hom.Compactification f)
  [HasDerivedCategory.{dS} (ModuleSheaf S Λ)]
  [hC : HasDerivedCategory.{dM} (ModuleSheaf C.Xbar Λ)]
/-- The local derived-category model on `ModuleSheaf (C.ofSourceIso f (Iso.refl X)
(Category.id_comp f)).Xbar Λ`. -/
local instance unboundedSourceIsoIdentityRawModel : HasDerivedCategory.{dM}
    (ModuleSheaf (C.ofSourceIso f (Iso.refl X) (Category.id_comp f)).Xbar Λ) := hC

/-- Equality of the original transported raw value after the geometric identity law. -/
theorem moduleUnboundedRawCompactificationFunctor_source_refl :
    @moduleUnboundedRawCompactificationFunctor X S f
      (C.ofSourceIso f (Iso.refl X) (Category.id_comp f)) Λ _
      inferInstance inferInstance inferInstance =
        moduleUnboundedRawCompactificationFunctor C Λ := by
  (simp only [moduleUnboundedRawCompactificationFunctor, Hom.Compactification.ofSourceIso,
    Iso.refl_hom, Category.id_comp, unboundedSourceIsoIdentityRawModel]; rfl)

/-- The actual raw source comparison contracts by the original native inverse-image identity. -/
theorem moduleUnboundedRawCompactificationSourceIso_refl :
    moduleUnboundedRawCompactificationSourceIso (Iso.refl X) Λ f (Category.id_comp f) C ≪≫
      Functor.isoWhiskerRight (moduleUnboundedDerivedInverseImageIdIso Λ X)
        (moduleUnboundedRawCompactificationFunctor
          (C.ofSourceIso f (Iso.refl X) (Category.id_comp f)) Λ) ≪≫
      Functor.leftUnitor _ ≪≫
      eqToIso (moduleUnboundedRawCompactificationFunctor_source_refl Λ C) = Iso.refl _ := by
  have h := moduleUnboundedDerivedLowerShriekSourceIso_refl C.j Λ
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hk := congrArg (fun z => z.hom.app K) h
  change (moduleUnboundedDerivedLowerShriekSourceIso (Iso.refl X) C.j Λ).hom.app K ≫
    (moduleUnboundedDerivedLowerShriek C.j Λ).map
      ((moduleUnboundedDerivedInverseImageIdIso Λ X).hom.app K) ≫
    𝟙 _ ≫ 𝟙 _ = 𝟙 _ at hk
  simp only [Category.comp_id] at hk
  erw [Category.comp_id] at hk
  change ((moduleUnboundedDerivedDirectImage Λ C.p).map
      ((moduleUnboundedDerivedLowerShriekSourceIso (Iso.refl X) C.j Λ).hom.app K) ≫ 𝟙 _) ≫
    (moduleUnboundedDerivedDirectImage Λ C.p).map
      ((moduleUnboundedDerivedLowerShriek C.j Λ).map
        ((moduleUnboundedDerivedInverseImageIdIso Λ X).hom.app K)) ≫
    𝟙 _ ≫ 𝟙 _ = 𝟙 _
  simp only [Category.comp_id]
  calc
    _ = (moduleUnboundedDerivedDirectImage Λ C.p).map
        ((moduleUnboundedDerivedLowerShriekSourceIso (Iso.refl X) C.j Λ).hom.app K ≫
          (moduleUnboundedDerivedLowerShriek C.j Λ).map
            ((moduleUnboundedDerivedInverseImageIdIso Λ X).hom.app K)) :=
      ((moduleUnboundedDerivedDirectImage Λ C.p).map_comp _ _).symm
    _ = (moduleUnboundedDerivedDirectImage Λ C.p).map (𝟙 _) :=
      congrArg (fun z => (moduleUnboundedDerivedDirectImage Λ C.p).map z) hk
    _ = _ := (moduleUnboundedDerivedDirectImage Λ C.p).map_id _
end Raw

end AlgebraicGeometry.Scheme.EtaleCohomology
