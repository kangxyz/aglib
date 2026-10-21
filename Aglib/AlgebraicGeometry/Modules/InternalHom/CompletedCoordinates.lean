/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.CompletedEvaluation
public import Aglib.RingTheory.AdicCompletion.ExtendedHomCoordinates
public import Aglib.RingTheory.AdicCompletion.MappedHomCoordinates

/-! # Original quotient coordinates of completed affine Hom evaluation -/

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

/-- On original source elements, the formal Hom coordinate is the actual
completed evaluation followed by the canonical extended-ideal quotient map. -/
theorem affineCompletedEvaluation_coordinate (n : ℕ) :
    letI := idealSectionModule X α (sheaf X F G) U.val
    letI := idealSectionModule X α F U.val
    letI := idealSectionModule X α G U.val
    letI : Algebra A Γ(X, U) := (idealSectionRingHom X α U.val).toAlgebra
    letI : IsScalarTower A Γ(X, U) Γ(G, U) := IsScalarTower.of_compHom A Γ(X, U) _
    ∀ (h : AdicCompletion I Γ(sheaf X F G, U)) (m : Γ(F, U)),
      (affineStructuralCompletedHomEquiv U F G hF hG α I h).val n
          (Submodule.Quotient.mk m) =
        AdicCompletion.mapIdealQuotientEquiv (S := Γ(X, U)) I Γ(G, U) n
          (AdicCompletion.eval I Γ(G, U) n
            (affineCompletedEvaluation α I U F G hF hG h (AdicCompletion.of I _ m))) := by
  let := idealSectionModule X α (sheaf X F G) U.val
  let := idealSectionModule X α F U.val
  let := idealSectionModule X α G U.val
  let : Algebra A Γ(X, U) := (idealSectionRingHom X α U.val).toAlgebra
  let : IsScalarTower A Γ(X, U) Γ(sheaf X F G, U) :=
    IsScalarTower.of_compHom A Γ(X, U) _
  let : IsScalarTower A Γ(X, U) Γ(F, U) := IsScalarTower.of_compHom A Γ(X, U) _
  let : IsScalarTower A Γ(X, U) Γ(G, U) := IsScalarTower.of_compHom A Γ(X, U) _
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  let : Module.Finite Γ(X, U) Γ(F, U) :=
    QuasiCoherent.finite_sections_of_affineLocallyFiniteType F hF U
  let : Module.Finite Γ(X, U) Γ(G, U) :=
    QuasiCoherent.finite_sections_of_affineLocallyFiniteType G hG U
  let : (F.restrict U.property.fromSpec).IsQuasicoherent := (hF _ _).1
  intro h m
  exact AdicCompletion.extendedHomEvaluation_coordinate_map (B := Γ(X, U))
    I Γ(F, U) Γ(G, U) (sectionEvaluation X F G U) h m n

end AlgebraicGeometry.Scheme.Modules.InternalHom
