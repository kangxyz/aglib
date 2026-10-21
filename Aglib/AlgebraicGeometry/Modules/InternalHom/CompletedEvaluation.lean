/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.FormalComparison
public import Aglib.RingTheory.AdicCompletion.ExtendedHom
public import Aglib.RingTheory.AdicCompletion.Ext

/-! # Actual affine Hom evaluation on structural completions -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.InternalHom

universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable {A : Type u} [CommRing A] (α : A →+* Γ(X, ⊤)) (I : Ideal A)
variable (U : X.affineOpens) (F G : X.Modules)
variable (hF : QuasiCoherent.affineLocallyFiniteType X F)
variable (hG : QuasiCoherent.affineLocallyFiniteType X G)

/-- The actual evaluation pairing extended to completions for the structural
ideal. This definition uses only finite generation over the affine chart ring. -/
def affineCompletedEvaluation :
    letI := idealSectionModule X α (sheaf X F G) U.val
    letI := idealSectionModule X α F U.val
    letI := idealSectionModule X α G U.val
    AdicCompletion I Γ(sheaf X F G, U) →ₗ[A]
      AdicCompletion I Γ(F, U) →ₗ[A] AdicCompletion I Γ(G, U) := by
  letI := idealSectionModule X α (sheaf X F G) U.val
  letI := idealSectionModule X α F U.val
  letI := idealSectionModule X α G U.val
  letI : Algebra A Γ(X, U) := (idealSectionRingHom X α U.val).toAlgebra
  letI : IsScalarTower A Γ(X, U) Γ(sheaf X F G, U) :=
    IsScalarTower.of_compHom A Γ(X, U) _
  letI : IsScalarTower A Γ(X, U) Γ(F, U) := IsScalarTower.of_compHom A Γ(X, U) _
  letI : IsScalarTower A Γ(X, U) Γ(G, U) := IsScalarTower.of_compHom A Γ(X, U) _
  letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  letI : Module.Finite Γ(X, U) Γ(F, U) :=
    QuasiCoherent.finite_sections_of_affineLocallyFiniteType F hF U
  letI : Module.Finite Γ(X, U) Γ(G, U) :=
    QuasiCoherent.finite_sections_of_affineLocallyFiniteType G hG U
  exact (AdicCompletion.extendedHomEvaluation I Γ(F, U) Γ(G, U)).comp
    ((AdicCompletion.map I ((sectionEvaluation X F G U).restrictScalars A)).restrictScalars A)

/-- Completed evaluation retains the original section evaluation on classes. -/
@[simp]
theorem affineCompletedEvaluation_of_of
    (s : Γ(sheaf X F G, U)) (m : Γ(F, U)) :
    letI := idealSectionModule X α (sheaf X F G) U.val
    letI := idealSectionModule X α F U.val
    letI := idealSectionModule X α G U.val
    affineCompletedEvaluation α I U F G hF hG
      (AdicCompletion.of I _ s) (AdicCompletion.of I _ m) =
        AdicCompletion.of I _ (sectionEvaluation X F G U s m) := by
  simp [affineCompletedEvaluation, AdicCompletion.map_of]

end AlgebraicGeometry.Scheme.Modules.InternalHom
