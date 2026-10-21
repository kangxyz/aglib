/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FullFaithfulReduction

/-! # Recovery retains every original morphism -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.InternalHom

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (F G : X.Modules)
  [F.IsQuasicoherent] [G.IsQuasicoherent]
  (hF : QuasiCoherent.affineLocallyFiniteType X F)
  (hG : QuasiCoherent.affineLocallyFiniteType X G)

local notation "α" => idealThickeningBaseScalar f

omit [IsNoetherianRing A] [IsAdicComplete I A] [IsLocallyNoetherian X] [IsProper f] in
/-- On each original affine section, the completed original arrow is its literal reduction. -/
theorem localQuotientHom_towerHom_mk (φ : F ⟶ G) (U : X.affineOpens)
    (n : ℕ) (x : Γ(F, U)) :
    (localQuotientHom f F G I (idealPowerQuotientTowerHom X α I φ) U).val n
        (Submodule.Quotient.mk x) = Submodule.Quotient.mk (φ.app U.val x) := by
  calc
    _ = (idealPowerQuotientAffineChartEquiv f G I U n).symm
        ((idealQuotientHom X α (I ^ n) φ).app U.val
          ((idealQuotientπ X α F (I ^ n)).app U.val x)) :=
      localQuotientHom_mk f F G I (idealPowerQuotientTowerHom X α I φ) U n x
    _ = (idealPowerQuotientAffineChartEquiv f G I U n).symm
        ((idealQuotientπ X α G (I ^ n)).app U.val (φ.app U.val x)) :=
      congrArg (idealPowerQuotientAffineChartEquiv f G I U n).symm
        (congrArg (fun k => k.app U.val x) (idealQuotientπ_hom X α (I ^ n) φ))
    _ = _ := (congrArg (idealPowerQuotientAffineChartEquiv f G I U n).symm
      (idealPowerQuotientAffineChartEquiv_mk f G I U n (φ.app U.val x)).symm).trans
        ((idealPowerQuotientAffineChartEquiv f G I U n).symm_apply_apply _)

omit [IsNoetherianRing A] [IsAdicComplete I A] [IsLocallyNoetherian X] [IsProper f] in
/-- The local formal system of an original arrow is its original module quotient system. -/
theorem localQuotientHom_towerHom (φ : F ⟶ G) (U : X.affineOpens) :
    localQuotientHom f F G I (idealPowerQuotientTowerHom X α I φ) U =
      AdicCompletion.quotientHom (I.map (idealSectionRingHom X α U.val))
        (φ.val.app (op U.val)).hom := by
  apply Subtype.ext
  funext n
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact (localQuotientHom_towerHom_mk I f F G φ U n x).trans
    (AdicCompletion.quotientHom_apply_mk
      (I.map (idealSectionRingHom X α U.val)) (φ.val.app (op U.val)).hom n x).symm

omit [IsNoetherianRing A] [IsAdicComplete I A] [IsProper f] in
/-- The completed local representatives of an original arrow are its actual
completed internal-Hom section restrictions. -/
theorem localCompletedHom_towerHom (φ : F ⟶ G) (U : X.affineOpens) :
    letI := idealSectionModule X α (sheaf X F G) U.val
    AdicCompletion.of I Γ(sheaf X F G, U)
        ((sheaf X F G).val.map (homOfLE le_top : U.val ⟶ ⊤).op
          (globalHomEquiv X F G φ)) =
      localCompletedHom f F G hF hG I (idealPowerQuotientTowerHom X α I φ) U := by
  let := idealSectionModule X α (sheaf X F G) U.val
  let e := affineStructuralCompletedHomEquiv U F G hF hG α I
  let s := (sheaf X F G).val.map (homOfLE le_top : U.val ⟶ ⊤).op
    (globalHomEquiv X F G φ)
  have hs : sectionEvaluation X F G U s = (φ.val.app (op U.val)).hom := by
    apply LinearMap.ext
    intro m
    exact sectionEvaluation_globalHomEquiv F G φ U.val m
  apply e.injective
  calc
    e (AdicCompletion.of I _ s) =
        AdicCompletion.quotientHom (I.map (idealSectionRingHom X α U.val))
          (sectionEvaluation X F G U s) :=
      affineStructuralCompletedHomEquiv_of U F G hF hG α I s
    _ = AdicCompletion.quotientHom (I.map (idealSectionRingHom X α U.val))
        (φ.val.app (op U.val)).hom := congrArg _ hs
    _ = localQuotientHom f F G I (idealPowerQuotientTowerHom X α I φ) U :=
      (localQuotientHom_towerHom I f F G φ U).symm
    _ = _ := (e.apply_symm_apply _).symm

/-- Algebraizing the completion of an original morphism returns that very morphism. -/
theorem formalHomLift_towerHom (φ : F ⟶ G) :
    formalHomLift I f F G hF hG (idealPowerQuotientTowerHom X α I φ) = φ := by
  have hs : globalHomEquiv X F G φ =
      formalHomSection I f F G hF hG (idealPowerQuotientTowerHom X α I φ) :=
    (existsUnique_internalHomSection I f F G hF hG
      (idealPowerQuotientTowerHom X α I φ)).choose_spec.2 _
        (localCompletedHom_towerHom I f F G hF hG φ)
  apply (globalHomEquiv X F G).injective
  exact ((globalHomEquiv X F G).apply_symm_apply _).trans hs.symm

/-- Full faithfulness on original coherent coefficient morphisms, with the
canonical quotient tower as forward map. -/
def formalHomEquiv : (F ⟶ G) ≃
    (idealPowerQuotientFunctor X α F I ⟶ idealPowerQuotientFunctor X α G I) where
  toFun := idealPowerQuotientTowerHom X α I
  invFun := formalHomLift I f F G hF hG
  left_inv := formalHomLift_towerHom I f F G hF hG
  right_inv := idealPowerQuotientTowerHom_formalHomLift I f F G hF hG

end AlgebraicGeometry.Scheme.Cohomology
