/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FullFaithfulSections
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.CompletionFunctorComparison
public import Aglib.AlgebraicGeometry.Modules.InternalHom.GlobalEvaluation

/-! # The recovered original morphism has exactly the prescribed formal reduction -/

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

/-- The recovered arrow agrees with the prescribed formal map on every
original affine source section at every quotient stage. -/
theorem formalHomLift_coordinate
    (η : idealPowerQuotientFunctor X α F I ⟶ idealPowerQuotientFunctor X α G I)
    (U : X.affineOpens) (n : ℕ) (m : Γ(F, U)) :
    (idealQuotientπ X α G (I ^ n)).app U.val
        ((formalHomLift I f F G hF hG η).app U.val m) =
      (η.app (op n)).app U.val ((idealQuotientπ X α F (I ^ n)).app U.val m) := by
  let := idealSectionModule X α (sheaf X F G) U.val
  let := idealSectionModule X α F U.val
  let := idealSectionModule X α G U.val
  have hc := localCompletedHom_coordinate f F G hF hG I η U n m
  erw [← formalHomSection_completion I f F G hF hG η U,
    affineCompletedEvaluation_of_of] at hc
  simp only [AdicCompletion.eval_of, Submodule.mkQ_apply,
    idealQuotientAffineSectionsEquiv_mk] at hc
  exact (congrArg ((idealQuotientπ X α G (I ^ n)).app U.val)
    (sectionEvaluation_globalHomEquiv_symm F G
      (formalHomSection I f F G hF hG η) U.val m)).symm.trans hc

/-- Completing the recovered original arrow yields exactly the original given
natural transformation, on all stages and all opens. -/
theorem idealPowerQuotientTowerHom_formalHomLift
    (η : idealPowerQuotientFunctor X α F I ⟶ idealPowerQuotientFunctor X α G I) :
    idealPowerQuotientTowerHom X α I (formalHomLift I f F G hF hG η) = η := by
  apply NatTrans.ext
  funext n
  apply moduleHom_ext_affine
  intro U
  ext x
  obtain ⟨m, rfl⟩ := idealQuotientπ_affine_surjective f F (I ^ n.unop) U x
  exact (congrArg (fun k => k.app U.val m)
    (idealQuotientπ_hom X α (I ^ n.unop) (formalHomLift I f F G hF hG η))).trans
      (formalHomLift_coordinate I f F G hF hG η U n.unop m)

end AlgebraicGeometry.Scheme.Cohomology
