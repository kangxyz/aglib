/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.LocalHomSystem
public import Aglib.AlgebraicGeometry.Modules.InternalHom.CompletedCoordinates
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.AffineQuotientScalarComparison

/-! # Completed local Hom sections of original formal morphisms -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.InternalHom

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (F G : X.Modules)
  [F.IsQuasicoherent] [G.IsQuasicoherent]
  (hF : QuasiCoherent.affineLocallyFiniteType X F)
  (hG : QuasiCoherent.affineLocallyFiniteType X G) (I : Ideal A)

local notation "α" => idealThickeningBaseScalar f

/-- The unique completed original Hom section representing the formal morphism
on an affine open. -/
def localCompletedHom
    (η : idealPowerQuotientFunctor X α F I ⟶ idealPowerQuotientFunctor X α G I)
    (U : X.affineOpens) :
    letI := idealSectionModule X α (sheaf X F G) U.val
    AdicCompletion I Γ(sheaf X F G, U) :=
  (affineStructuralCompletedHomEquiv U F G hF hG α I).symm
    (localQuotientHom f F G I η U)

/-- The local completed Hom section has the original formal morphism as its
actual quotient evaluation, rather than a substituted affine model. -/
theorem localCompletedHom_coordinate
    (η : idealPowerQuotientFunctor X α F I ⟶ idealPowerQuotientFunctor X α G I)
    (U : X.affineOpens) (n : ℕ) (m : Γ(F, U)) :
    letI := idealSectionModule X α (sheaf X F G) U.val
    letI := idealSectionModule X α F U.val
    letI := idealSectionModule X α G U.val
    idealQuotientAffineSectionsEquiv f G (I ^ n) U
        (AdicCompletion.eval I Γ(G, U) n
          (affineCompletedEvaluation α I U F G hF hG
            (localCompletedHom f F G hF hG I η U) (AdicCompletion.of I _ m))) =
      (η.app (op n)).app U.val ((idealQuotientπ X α F (I ^ n)).app U.val m) := by
  let := idealSectionModule X α (sheaf X F G) U.val
  let := idealSectionModule X α F U.val
  let := idealSectionModule X α G U.val
  let : Algebra A Γ(X, U) := (idealSectionRingHom X α U.val).toAlgebra
  let : IsScalarTower A Γ(X, U) Γ(G, U) := IsScalarTower.of_compHom A Γ(X, U) _
  let h := localCompletedHom f F G hF hG I η U
  let e := affineStructuralCompletedHomEquiv U F G hF hG α I
  have he : e h = localQuotientHom f F G I η U := e.apply_symm_apply _
  have hc := (congrArg (fun z => z.val n (Submodule.Quotient.mk m)) he).symm.trans
    (affineCompletedEvaluation_coordinate α I U F G hF hG n h m)
  calc
    _ = idealPowerQuotientAffineChartEquiv f G I U n
        (AdicCompletion.mapIdealQuotientEquiv (S := Γ(X, U)) I Γ(G, U) n
          (AdicCompletion.eval I Γ(G, U) n
            (affineCompletedEvaluation α I U F G hF hG h (AdicCompletion.of I _ m)))) :=
      (idealPowerQuotientAffineChartEquiv_mapIdeal f G I U n _).symm
    _ = idealPowerQuotientAffineChartEquiv f G I U n
        ((localQuotientHom f F G I η U).val n (Submodule.Quotient.mk m)) :=
      congrArg (idealPowerQuotientAffineChartEquiv f G I U n) hc.symm
    _ = _ := by
      erw [localQuotientHom_mk]
      exact (idealPowerQuotientAffineChartEquiv f G I U n).apply_symm_apply _

end AlgebraicGeometry.Scheme.Cohomology
