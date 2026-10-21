/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.AffineEvaluation
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.AffineSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Sections
public import Aglib.RingTheory.AdicCompletion.FormalHom
public import Aglib.RingTheory.AdicCompletion.ScalarExtension
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Affine formal comparison for coherent internal Hom

Completion of the original Hom-sheaf sections agrees with compatible maps
between reductions of the original section modules. The affine coordinate
ring is not assumed complete. In particular no finite-stage nonflat Hom
base-change assertion is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.InternalHom

universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable (U : X.affineOpens) (F G : X.Modules)
variable (hF : QuasiCoherent.affineLocallyFiniteType X F)
variable (hG : QuasiCoherent.affineLocallyFiniteType X G)

/-- The affine Hom comparison after completion and passage to compatible
systems, without assuming completeness of the affine coordinate ring. -/
def affineCompletedHomEquiv (J : Ideal Γ(X, U)) :
    AdicCompletion J Γ(sheaf X F G, U) ≃
      AdicCompletion.CompatibleQuotientHom J Γ(F, U) Γ(G, U) := by
  letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  letI : (F.restrict U.property.fromSpec).IsQuasicoherent := (hF _ _).1
  letI : Module.Finite Γ(X, U) Γ(F, U) :=
    QuasiCoherent.finite_sections_of_affineLocallyFiniteType F hF U
  letI : Module.Finite Γ(X, U) Γ(G, U) :=
    QuasiCoherent.finite_sections_of_affineLocallyFiniteType G hG U
  exact (AdicCompletion.congr J (affineSectionsEquiv U F G)).toEquiv.trans
    (AdicCompletion.completedHomFormalEquiv J)

/-- Original Hom sections give precisely their original quotient maps. -/
theorem affineCompletedHomEquiv_of (J : Ideal Γ(X, U))
    (s : Γ(sheaf X F G, U)) :
    affineCompletedHomEquiv U F G hF hG J (AdicCompletion.of J _ s) =
      AdicCompletion.quotientHom J (sectionEvaluation X F G U s) := by
  simp [affineCompletedHomEquiv, AdicCompletion.congr_apply, AdicCompletion.map_of,
    affineSectionsEquiv]

variable {A : Type u} [CommRing A] (α : A →+* Γ(X, ⊤))

/-- Structural-ideal completion of affine Hom sections, with the chart ideal
extended along the actual structural section map. -/
def affineStructuralCompletedHomEquiv (I : Ideal A) :
    letI := idealSectionModule X α (sheaf X F G) U.val
    AdicCompletion I Γ(sheaf X F G, U) ≃
      AdicCompletion.CompatibleQuotientHom
        (I.map (idealSectionRingHom X α U.val)) Γ(F, U) Γ(G, U) := by
  letI := idealSectionModule X α (sheaf X F G) U.val
  letI : Algebra A Γ(X, U) := (idealSectionRingHom X α U.val).toAlgebra
  letI : IsScalarTower A Γ(X, U) Γ(sheaf X F G, U) :=
    IsScalarTower.of_compHom A Γ(X, U) _
  exact (AdicCompletion.mapIdealLinearEquiv (S := Γ(X, U)) I Γ(sheaf X F G, U)).toEquiv.trans
    (affineCompletedHomEquiv U F G hF hG (I.map (idealSectionRingHom X α U.val)))

/-- Structural completion still extends the literal evaluation/reduction map. -/
theorem affineStructuralCompletedHomEquiv_of (I : Ideal A)
    (s : Γ(sheaf X F G, U)) :
    let := idealSectionModule X α (sheaf X F G) U.val
    affineStructuralCompletedHomEquiv U F G hF hG α I (AdicCompletion.of I _ s) =
      AdicCompletion.quotientHom (I.map (idealSectionRingHom X α U.val))
        (sectionEvaluation X F G U s) := by
  let := idealSectionModule X α (sheaf X F G) U.val
  let : Algebra A Γ(X, U) := (idealSectionRingHom X α U.val).toAlgebra
  let : IsScalarTower A Γ(X, U) Γ(sheaf X F G, U) :=
    IsScalarTower.of_compHom A Γ(X, U) _
  change affineCompletedHomEquiv U F G hF hG _
    (AdicCompletion.mapIdealLinearEquiv (S := Γ(X, U)) I _ (AdicCompletion.of I _ s)) = _
  rw [AdicCompletion.mapIdealLinearEquiv_of]
  exact affineCompletedHomEquiv_of U F G hF hG _ s

end AlgebraicGeometry.Scheme.Modules.InternalHom
