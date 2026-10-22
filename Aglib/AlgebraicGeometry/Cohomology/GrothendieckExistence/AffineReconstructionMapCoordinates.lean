/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineReconstructionMap

/-! # Original finite-stage coordinates of the affine reconstruction map

This coordinate obligation is required by the actual reconstructed sheaf map.
The independent bounded-module and candidate-isomorphism branches need only
the original completed-linear map and do not import this coordinate theorem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent
/-- Exactly the original coordinate equation, with its native carrier retained
as part of the interface rather than re-inferred at a geometric projection. -/
def NativeReconstructionData.Coordinate {R P : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] {I : Ideal R} {F G : ℕᵒᵖ ⥤ ModuleCat R}
    {hF : AdicCompletion.IsCompatibleSystem I F}
    {q : ∀ n, (P ⧸ (I ^ n • ⊤ : Submodule R P)) ≃ₗ[R] G.obj (op n)}
    {φ : F ⟶ G} (d : NativeReconstructionData I F G hF q φ)
    (x : ModuleCat.sectionsSubmodule F) (n : ℕ) : Prop :=
  q n (AdicCompletion.eval I P n (d.map x)) = φ.app (op n) (x.val (op n))

/-- The specified certificate proves its exact coordinate equation. -/
theorem NativeReconstructionData.coordinate {R P : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] {I : Ideal R} {F G : ℕᵒᵖ ⥤ ModuleCat R}
    {hF : AdicCompletion.IsCompatibleSystem I F}
    {q : ∀ n, (P ⧸ (I ^ n • ⊤ : Submodule R P)) ≃ₗ[R] G.obj (op n)}
    {φ : F ⟶ G} (d : NativeReconstructionData I F G hF q φ)
    (x : ModuleCat.sectionsSubmodule F) (n : ℕ) : d.Coordinate x n :=
  d.map_eval x n

/-- The original pullback relation gives the original stage square. The map
coordinate and quotient-unit laws are consumed before geometric substitution. -/
theorem NativeReconstructionData.stage_square {R P : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] (I : Ideal R) (F G : ℕᵒᵖ ⥤ ModuleCat R)
    (hF : AdicCompletion.IsCompatibleSystem I F)
    (uMap : ∀ n, P →ₗ[R] G.obj (op n))
    (q : ∀ n, {e : (P ⧸ (I ^ n • ⊤ : Submodule R P)) ≃ₗ[R] G.obj (op n) //
      ∀ y, e (Submodule.Quotient.mk y) = uMap n y})
    (φ : F ⟶ G) (d : NativeReconstructionData I F G hF (fun n => (q n).val) φ)
    (x : ModuleCat.sectionsSubmodule F) (y : P)
    (h : d.map x = AdicCompletion.of I P y) (n : ℕ) :
    φ.app (op n) (x.val (op n)) = uMap n y := by
  have hd := d.map_eval x n
  rw [h, AdicCompletion.eval_of] at hd
  exact hd.symm.trans ((q n).property y)

universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {K : (Spec B).IdealSheafData} {H : (Spec B).CoherentSheaf}
  {F : AdicSystem (Spec B) K}

local instance : H.obj.IsQuasicoherent :=
  ((QuasiCoherent.affineLocallyFiniteType_spec_iff B H.obj).mp H.property).1

variable (α : F ⟶ (completionFunctor (Spec B) K).obj H)

/-- Original finite-stage compatibility, stated in its exact native coordinate
proposition. Expanding `Coordinate` is the original quotient/stage equation. -/
theorem affineReconstructionMap_eval
    (x : ModuleCat.sectionsSubmodule F.affineSectionsTower) (n : ℕ) :
    (affineReconstructionMapData α).Coordinate x n :=
  (affineReconstructionMapData α).coordinate x n

end AlgebraicGeometry.Scheme.Modules.Coherent
