/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleScalarRestrictionLowerMate

/-! # Composed original scalar mates for module-valued lower shriek -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.TwoSquare

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

attribute [local instance] hasSheafifyModules moduleRestrictScalars_preservesSheafification

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
  {Λ Γ : Type (u + 1)} [Ring Λ] [Ring Γ] (φ : Λ →+* Γ)

local instance moduleValuedScalarRestrictionPreservesCoproducts (ι : Type u) :
    PreservesColimitsOfShape (Discrete ι) (ModuleCat.restrictScalars.{u + 1} φ) where
  preservesColimit {K} := ModuleCat.preservesColimit_restrictScalars φ K

/-- The actual slice and slice-equivalence scalar squares compose to the old
module-valued lower-shriek comparison and have the literal restriction mate. -/
theorem moduleValuedLowerShriekScalarRestriction_composite_mate :
    (mateEquiv
      ((moduleEtaleSliceSheafEquivalence j Γ).toAdjunction.comp
        (Sheaf.SliceCohomology.lowerShriekAdjunction (Scheme.smallEtaleTopology X)
          (ModuleCat.{u + 1} Γ) (Scheme.Etale.mk j)))
      ((moduleEtaleSliceSheafEquivalence j Λ).toAdjunction.comp
        (Sheaf.SliceCohomology.lowerShriekAdjunction (Scheme.smallEtaleTopology X)
          (ModuleCat.{u + 1} Λ) (Scheme.Etale.mk j)))
      (TwoSquare.mk _ _ _ _ (moduleValuedLowerShriekScalarRestrictionIso j φ).inv)).natTrans =
    𝟙 (moduleValuedEtaleRestriction j Γ ⋙ moduleValuedRestrictScalars U φ) := by
  let aΓ := (moduleEtaleSliceSheafEquivalence j Γ).toAdjunction
  let aΛ := (moduleEtaleSliceSheafEquivalence j Λ).toAdjunction
  let bΓ := Sheaf.SliceCohomology.lowerShriekAdjunction (Scheme.smallEtaleTopology X)
    (ModuleCat.{u + 1} Γ) (Scheme.Etale.mk j)
  let bΛ := Sheaf.SliceCohomology.lowerShriekAdjunction (Scheme.smallEtaleTopology X)
    (ModuleCat.{u + 1} Λ) (Scheme.Etale.mk j)
  let α := TwoSquare.mk _ _ _ _ (moduleEtaleSliceScalarRestrictionIso j φ).inv
  let β := TwoSquare.mk _ _ _ _ (Sheaf.SliceCohomology.lowerShriekCoefficientIso
    (ModuleCat.restrictScalars.{u + 1} φ) (Scheme.Etale.mk j)
    (Scheme.smallEtaleTopology X)).hom
  have hs : mateEquiv aΓ aΛ α =
      TwoSquare.mk _ _ _ _ (moduleEtaleSliceInverseScalarRestrictionIso j φ).inv := by
    apply (mateEquiv aΓ aΛ).symm.injective
    rw [Equiv.symm_apply_apply]
    exact (moduleEtaleSliceScalarRestrictionIso_inv_mate j φ).symm
  have hl : mateEquiv bΓ bΛ β = TwoSquare.mk _ _ _ _
      (𝟙 ((Scheme.smallEtaleTopology X).overPullback (ModuleCat.{u + 1} Γ)
        (Scheme.Etale.mk j) ⋙
        sheafCompose ((Scheme.smallEtaleTopology X).over (Scheme.Etale.mk j))
          (ModuleCat.restrictScalars.{u + 1} φ))) :=
    moduleSliceLowerShriekScalarRestriction_mate j φ
  have hc : α ≫ᵥ β =
      TwoSquare.mk _ _ _ _ (moduleValuedLowerShriekScalarRestrictionIso j φ).inv := by
    apply TwoSquare.ext
    intro M
    simp only [α, β, TwoSquare.vComp, TwoSquare.mk, TwoSquare.natTrans,
      moduleValuedLowerShriekScalarRestrictionIso,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id]
    rfl
  have h := mateEquiv_hcomp aΓ aΛ bΓ bΛ α β
  rw [hc, hs, hl] at h
  apply NatTrans.ext
  funext M
  have hv := congrArg (fun t => t.natTrans.app M) h
  simp only [TwoSquare.hComp, TwoSquare.mk, TwoSquare.natTrans,
    moduleEtaleSliceInverseScalarRestrictionIso, Iso.refl_inv,
    NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at hv
  let N := ((Scheme.smallEtaleTopology X).overPullback (ModuleCat.{u + 1} Γ)
    (Scheme.Etale.mk j) ⋙
    sheafCompose ((Scheme.smallEtaleTopology X).over (Scheme.Etale.mk j))
      (ModuleCat.restrictScalars.{u + 1} φ)).obj M
  change _ = 𝟙 _ ≫ (moduleEtaleSliceSheafEquivalence j Λ).inverse.map (𝟙 N) at hv
  exact hv.trans ((congrArg (fun k => 𝟙 _ ≫ k)
    ((moduleEtaleSliceSheafEquivalence j Λ).inverse.map_id N)).trans (Category.id_comp _))

end AlgebraicGeometry.Scheme.EtaleCohomology
