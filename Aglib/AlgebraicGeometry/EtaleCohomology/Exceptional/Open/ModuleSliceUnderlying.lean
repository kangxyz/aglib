/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleAdjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.AbelianAdjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying

/-! # Original underlying sheaves for the actual module slice equivalence -/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
  (Λ : Type (u + 1)) [Ring Λ]

/-- Inverse slice equivalence commutes literally with the original additive forgetting. -/
def moduleEtaleSliceInverseUnderlyingIso :
    sheafCompose ((Scheme.smallEtaleTopology X).over (Scheme.Etale.mk j))
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙
      (etaleSliceSheafEquivalence (Scheme.Etale.mk j)).inverse ≅
    (moduleEtaleSliceSheafEquivalence j Λ).inverse ⋙
      sheafCompose (Scheme.smallEtaleTopology U)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  Iso.refl _

/-- Forward slice equivalence commutes with forgetting through its actual unit and counit. -/
def moduleEtaleSliceUnderlyingIso :
    (moduleEtaleSliceSheafEquivalence j Λ).functor ⋙
      sheafCompose ((Scheme.smallEtaleTopology X).over (Scheme.Etale.mk j))
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≅
    sheafCompose (Scheme.smallEtaleTopology U)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙
      (etaleSliceSheafEquivalence (Scheme.Etale.mk j)).functor :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (etaleSliceSheafEquivalence (Scheme.Etale.mk j)).counitIso.symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (moduleEtaleSliceInverseUnderlyingIso j Λ) _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleEtaleSliceSheafEquivalence j Λ).unitIso.symm _ ≪≫
    Functor.leftUnitor _

end AlgebraicGeometry.Scheme.EtaleCohomology
