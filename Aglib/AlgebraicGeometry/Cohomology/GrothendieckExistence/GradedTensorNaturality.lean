/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAffineScalars
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedRestriction
public import Aglib.RingTheory.TensorProduct.CommutingActionsNaturality

/-! # Actual tensor-semilinearity of formal graded restrictions -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite DirectSum GradedMonoid
open scoped TensorProduct
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

omit [IsLocallyNoetherian X] in
/-- The original coordinate restriction is a morphism of the specified base algebras. -/
def formalGradedCoordinateRestriction {U V : X.Opens} (h : U ≤ V) :
    letI := formalGradedSectionAlgebra f U
    letI := formalGradedSectionAlgebra f V
    Γ(X, V) →ₐ[A] Γ(X, U) := by
  letI := formalGradedSectionAlgebra f U
  letI := formalGradedSectionAlgebra f V
  exact {
    toRingHom := (X.presheaf.map (homOfLE h).op).hom
    commutes' a := by
      change X.presheaf.map (homOfLE h).op
        (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (idealThickeningBaseScalar f a)) =
          X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (idealThickeningBaseScalar f a)
      rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
      congr 1
  }

/-- Original restrictions intertwine the actual tensor action under the original tensor map. -/
theorem formalGradedSectionsRestriction_tensor_smul {U V : X.Opens} (h : U ≤ V) :
    letI := formalGradedSectionAlgebra f U
    letI := formalGradedSectionAlgebra f V
    letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
    letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
    letI : Semiring (Γ(X, V) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, V)) (B := I.associatedGraded)
    letI : NonAssocSemiring (Γ(X, V) ⊗[A] I.associatedGraded) :=
      (inferInstance : Semiring (Γ(X, V) ⊗[A] I.associatedGraded)).toNonAssocSemiring
    letI := formalGradedAffineModule f I F U
    letI := formalGradedAffineModule f I F V
    ∀ (t : Γ(X, V) ⊗[A] I.associatedGraded) (x : ⨁ n, Γ(F.gradedPiece n, V)),
      formalGradedSectionsRestriction f I F h (t • x) =
        @SMul.smul (Γ(X, U) ⊗[A] I.associatedGraded)
          (⨁ n, Γ(F.gradedPiece n, U)) inferInstance
          (Algebra.TensorProduct.map (formalGradedCoordinateRestriction f h)
            (AlgHom.id A I.associatedGraded) t)
          (formalGradedSectionsRestriction f I F h x) := by
  let := formalGradedSectionAlgebra f U
  let := formalGradedSectionAlgebra f V
  let : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
  let : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  let : Semiring (Γ(X, V) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, V)) (B := I.associatedGraded)
  let : NonAssocSemiring (Γ(X, V) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, V) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  let := formalGradedAffineModule f I F U
  let := formalGradedAffineModule f I F V
  let ρ : (⨁ n, Γ(F.gradedPiece n, V)) →+ (⨁ n, Γ(F.gradedPiece n, U)) :=
    { toFun := formalGradedSectionsRestriction f I F h
      map_zero' := (formalGradedSectionsRestriction f I F h).map_zero
      map_add' := (formalGradedSectionsRestriction f I F h).map_add }
  have hρ (n : ℕ) (x : Γ(F.gradedPiece n, V)) :
      ρ (DirectSum.of (fun k => Γ(F.gradedPiece k, V)) n x) =
        DirectSum.of (fun k => Γ(F.gradedPiece k, U)) n
          ((F.gradedPiece n).val.map (homOfLE h).op x) :=
    formalGradedSectionsRestriction_of f I F h n x
  intro t x
  change ρ (t • x) =
    Algebra.TensorProduct.map (formalGradedCoordinateRestriction f h)
      (AlgHom.id A I.associatedGraded) t • ρ x
  induction t using TensorProduct.inductionOn with
  | tmul b s =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    induction s using DirectSum.Decomposition.inductionOn I.associatedGradedGrading with
    | zero =>
      simp only [TensorProduct.tmul_zero, zero_smul]
      exact (congrArg ρ (zero_smul (Γ(X, V) ⊗[A] I.associatedGraded) x)).trans ρ.map_zero
    | homogeneous a =>
      induction x using DirectSum.induction_on with
      | zero => simp only [smul_zero, map_zero]
      | of n x =>
        rw [formalGradedAffineModule_tmul_component_smul,
          hρ, hρ,
          formalGradedAffineModule_tmul_component_smul]
        apply congrArg (DirectSum.of (fun k => Γ(F.gradedPiece k, U)) (_ + n))
        change (F.gradedPiece (_ + n)).val.map (homOfLE h).op
          (b • (formalGradedHomogeneousAction f I F _ n a).app V x) = _
        rw [(F.gradedPiece (_ + n)).val.map_smul]
        apply congrArg ((X.presheaf.map (homOfLE h).op b) • ·)
        exact formalGradedHomogeneousAction_restriction f I F h _ n a x
      | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | add s t hs ht =>
      simp only [TensorProduct.tmul_add, add_smul]
      exact (congrArg ρ (add_smul (b ⊗ₜ[A] s) (b ⊗ₜ[A] t) x)).trans
        ((ρ.map_add _ _).trans (congrArg₂ (· + ·) hs ht))
  | add s t hs ht =>
    simp only [map_add, add_smul]
    exact congrArg₂ (· + ·) hs ht

end AlgebraicGeometry.Scheme.Cohomology
