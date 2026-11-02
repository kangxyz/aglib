/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleScalarRestrictionSliceMate

/-! # Actual scalar mates for the original slice lower shriek -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

attribute [local instance] hasSheafifyModules moduleRestrictScalars_preservesSheafification

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
  {Λ Γ : Type (u + 1)} [Ring Λ] [Ring Γ] (φ : Λ →+* Γ)

local instance moduleSliceScalarRestrictionPreservesCoproducts (ι : Type u) :
    PreservesColimitsOfShape (Discrete ι) (ModuleCat.restrictScalars.{u + 1} φ) where
  preservesColimit {K} := ModuleCat.preservesColimit_restrictScalars φ K

/-- The original slice lower-shriek coefficient comparison has literal coefficient
restriction as its actual right mate. -/
theorem moduleSliceLowerShriekScalarRestriction_mate :
    (mateEquiv
      (Sheaf.SliceCohomology.lowerShriekAdjunction (Scheme.smallEtaleTopology X)
        (ModuleCat.{u + 1} Γ) (Scheme.Etale.mk j))
      (Sheaf.SliceCohomology.lowerShriekAdjunction (Scheme.smallEtaleTopology X)
        (ModuleCat.{u + 1} Λ) (Scheme.Etale.mk j))
      (TwoSquare.mk _ _ _ _ (Sheaf.SliceCohomology.lowerShriekCoefficientIso
        (ModuleCat.restrictScalars.{u + 1} φ) (Scheme.Etale.mk j)
        (Scheme.smallEtaleTopology X)).hom)).natTrans =
    𝟙 ((Scheme.smallEtaleTopology X).overPullback (ModuleCat.{u + 1} Γ) (Scheme.Etale.mk j) ⋙
      sheafCompose ((Scheme.smallEtaleTopology X).over (Scheme.Etale.mk j))
        (ModuleCat.restrictScalars.{u + 1} φ)) := by
  let J := Scheme.smallEtaleTopology X
  let R := ModuleCat.restrictScalars.{u + 1} φ
  let e := Sheaf.SliceCohomology.lowerShriekCoefficientIso R (Scheme.Etale.mk j) J
  refine mateEquiv_inv_natTrans_eq_of_unit
    (Sheaf.SliceCohomology.lowerShriekAdjunction J (ModuleCat.{u + 1} Γ) (Scheme.Etale.mk j))
    (Sheaf.SliceCohomology.lowerShriekAdjunction J (ModuleCat.{u + 1} Λ) (Scheme.Etale.mk j))
    e.symm (𝟙 (J.overPullback (ModuleCat.{u + 1} Γ) (Scheme.Etale.mk j) ⋙
      sheafCompose (J.over (Scheme.Etale.mk j)) R)) ?_
  intro M
  change (sheafCompose (J.over (Scheme.Etale.mk j)) R).map
      ((Sheaf.SliceCohomology.lowerShriekAdjunction J (ModuleCat.{u + 1} Γ)
        (Scheme.Etale.mk j)).unit.app M) ≫ 𝟙 _ ≫
      (J.overPullback (ModuleCat.{u + 1} Λ) (Scheme.Etale.mk j)).map (e.inv.app M) = _
  erw [Category.id_comp]
  rw [← Sheaf.SliceCohomology.lowerShriekCoefficientIso_unit R (Scheme.Etale.mk j) J M]
  change ((Sheaf.SliceCohomology.lowerShriekAdjunction J (ModuleCat.{u + 1} Λ)
      (Scheme.Etale.mk j)).unit.app ((sheafCompose (J.over (Scheme.Etale.mk j)) R).obj M) ≫
      (J.overPullback (ModuleCat.{u + 1} Λ) (Scheme.Etale.mk j)).map (e.hom.app M)) ≫
      (J.overPullback (ModuleCat.{u + 1} Λ) (Scheme.Etale.mk j)).map (e.inv.app M) = _
  rw [Category.assoc, ← Functor.map_comp, e.hom_inv_id_app]
  exact (congrArg (fun k =>
    (Sheaf.SliceCohomology.lowerShriekAdjunction J (ModuleCat.{u + 1} Λ)
      (Scheme.Etale.mk j)).unit.app ((sheafCompose (J.over (Scheme.Etale.mk j)) R).obj M) ≫ k)
      ((J.overPullback (ModuleCat.{u + 1} Λ) (Scheme.Etale.mk j)).map_id _)).trans
        (Category.comp_id _)

end AlgebraicGeometry.Scheme.EtaleCohomology
