/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # The original ring map of an actual affine-open chart factorization

The map is precisely Spec.preimage of the native open-immersion lift. The
factorization and its uniqueness retain that original map; no chart model or
homology comparison is chosen.
-/

@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {R T : CommRingCat.{u}}
  (a : Spec R ⟶ X) [IsOpenImmersion a] (c : Spec T ⟶ X)
  (hc : Set.range c ⊆ Set.range a)

/-- Original affine ring map of the actual unique open factorization. -/
def affineOpenChartFactor : R ⟶ T :=
  Spec.preimage (IsOpenImmersion.lift a c hc)

/-- The Spec map is the original native open-immersion lift. -/
theorem affineOpenChartFactor_spec :
    Spec.map (affineOpenChartFactor a c hc) = IsOpenImmersion.lift a c hc :=
  Spec.map_preimage _

/-- The original factorization equation, not an input comparison. -/
@[reassoc]
theorem affineOpenChartFactor_comp :
    Spec.map (affineOpenChartFactor a c hc) ≫ a = c := by
  rw [affineOpenChartFactor_spec]
  exact IsOpenImmersion.lift_fac a c hc

/-- Uniqueness retains the given affine ring homomorphism whenever its actual
Spec factorization is known. -/
theorem affineOpenChartFactor_eq (f : R ⟶ T) (hf : Spec.map f ≫ a = c) :
    affineOpenChartFactor a c hc = f := by
  apply Spec.map_injective
  apply (cancel_mono a).mp
  exact (affineOpenChartFactor_comp a c hc).trans hf.symm

/-- Factoring one actual open immersion through another is still an actual open immersion. -/
theorem affineOpenChartFactor_isOpenImmersion [IsOpenImmersion c] :
    IsOpenImmersion (Spec.map (affineOpenChartFactor a c hc)) := by
  have h : IsOpenImmersion (Spec.map (affineOpenChartFactor a c hc) ≫ a) := by
    rw [affineOpenChartFactor_comp]
    infer_instance
  exact IsOpenImmersion.of_comp _ a

end AlgebraicGeometry.Scheme
