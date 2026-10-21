/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAffineScalars
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAffineGeneration
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedGeneratorAction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Sections
public import Aglib.RingTheory.AssociatedGraded.TensorRing

/-! # Finite affine modules of the actual formal graded coefficient -/

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
  (F : AdicSystem X (idealThickeningIdealSheaf f I)) (U : X.Opens)

private theorem generator_of_heq {M : ℕ → Type u} [∀ n, AddCommGroup (M n)]
    {r n : ℕ} (h : r = n) (x : M r) (y : M n) (hxy : HEq x y) :
    DirectSum.of M r x = DirectSum.of M n y := by
  subst n
  rw [eq_of_heq hxy]

omit [IsLocallyNoetherian X] in
private theorem generator_value_heq {M N N' : X.Modules} (hN : N = N')
    (φ : M ⟶ N) (ψ : M ⟶ N') (h : HEq φ ψ) (x : Γ(M, U)) :
    HEq (φ.app U x) (ψ.app U x) := by
  subst N'
  rw [eq_of_heq h]

/-- A tensor scalar on degree zero is the original first-level generator. -/
theorem formalGradedAffineModule_generator (n : ℕ) (a : ↥(I ^ n))
    (y : Γ(F.obj.obj (op 1), U)) :
    letI := formalGradedSectionAlgebra f U
    letI := formalGradedAffineModule f I F U
    ((1 : Γ(X, U)) ⊗ₜ[A]
      (I.associatedGradedComponentMap n a : I.associatedGraded)) •
        DirectSum.of (fun k => Γ(F.gradedPiece k, U)) 0 (F.gradedPieceZeroIso.inv.app U y) =
      DirectSum.of (fun k => Γ(F.gradedPiece k, U)) n
        ((formalGradedPieceGenerator f I F n a).app U y) := by
  let := formalGradedSectionAlgebra f U
  let := formalGradedAffineModule f I F U
  let := formalGradedAffineModule_scalarTower_left f I F U
  rw [formalGradedAffineModule_tmul_component_smul, one_smul]
  change DirectSum.of (fun k => Γ(F.gradedPiece k, U)) (n + 0)
    ((formalGradedHomogeneousAction f I F n 0
      (I.associatedGradedComponentMap n a)).app U (F.gradedPieceZeroIso.inv.app U y)) = _
  rw [formalGradedHomogeneousAction_componentMap]
  apply generator_of_heq (Nat.add_zero n)
  have hh := generator_value_heq U (congrArg F.gradedPiece (Nat.add_zero n)) _ _
    (formalGradedScalarMap_generator f I F n a) (F.gradedPieceZeroIso.inv.app U y)
  convert hh using 1
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  have he := congrArg (fun g => g.app U y) F.gradedPieceZeroIso.inv_hom_id
  simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] using
    (congrArg ((formalGradedPieceGenerator f I F n a).app U) he).symm

/-- The actual local scalar-extension presentation from degree zero. -/
def formalGradedAffinePresentation :
    letI := formalGradedSectionAlgebra f U
    letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
    letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
    letI := formalGradedAffineModule f I F U
    letI := formalGradedAffineModule_scalarTower_left f I F U
    (↑(X.presheaf.obj (op U)) ⊗[A] I.associatedGraded) ⊗[↑(X.presheaf.obj (op U))]
      Γ(F.gradedPiece 0, U) →ₗ[↑(X.presheaf.obj (op U)) ⊗[A] I.associatedGraded]
        (⨁ n, Γ(F.gradedPiece n, U)) := by
  letI := formalGradedSectionAlgebra f U
  letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
  letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  letI := formalGradedAffineModule f I F U
  letI := formalGradedAffineModule_scalarTower_left f I F U
  exact GradedModule.degreeZeroTensorMap (B := ↑(X.presheaf.obj (op U)))
    (↑(X.presheaf.obj (op U)) ⊗[A] I.associatedGraded) (fun n => Γ(F.gradedPiece n, U))

/-- The original presentation is surjective on an affine open, proved from
finite-stage formal reductions rather than assumed as realization data. -/
theorem formalGradedAffinePresentation_surjective (hU : IsAffineOpen U) :
    Function.Surjective (formalGradedAffinePresentation f I F U) := by
  let := formalGradedSectionAlgebra f U
  let := formalGradedAffineModule f I F U
  let := formalGradedAffineModule_scalarTower_left f I F U
  let P := LinearMap.range (formalGradedAffinePresentation f I F U)
  have hn (n : ℕ) (x : Γ(F.gradedPiece n, U)) : DirectSum.of _ n x ∈ P := by
    have hle : Submodule.span Γ(X, U)
        {z : Γ(F.gradedPiece n, U) | ∃ a : ↥(I ^ n),
          ∃ y : Γ(F.obj.obj (op 1), U),
            z = (formalGradedPieceGenerator f I F n a).app U y} ≤
        (P.restrictScalars Γ(X, U)).comap (DirectSum.lof Γ(X, U) ℕ _ n) := by
      apply Submodule.span_le.mpr
      rintro z ⟨a, y, rfl⟩
      refine ⟨((1 : Γ(X, U)) ⊗ₜ[A]
        (I.associatedGradedComponentMap n a : I.associatedGraded)) ⊗ₜ[Γ(X, U)]
          (F.gradedPieceZeroIso.inv.app U y), ?_⟩
      exact formalGradedAffineModule_generator f I F U n a y
    rw [formalGradedPieceGenerator_affine_span f I F n ⟨U, hU⟩] at hle
    exact hle (Submodule.mem_top : x ∈ (⊤ : Submodule Γ(X, U) Γ(F.gradedPiece n, U)))
  intro x
  change x ∈ P
  induction x using DirectSum.induction_on with
  | zero => exact P.zero_mem
  | of n x => exact hn n x
  | add x y hx hy => exact P.add_mem hx hy

/-- The original affine graded module is finite over the actual tensor ring,
not generally finite over the base associated-graded ring alone. -/
theorem formalGradedAffineModule_finite (hU : IsAffineOpen U) :
    letI := formalGradedSectionAlgebra f U
    letI := formalGradedAffineModule f I F U
    Module.Finite (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, U)) := by
  let := formalGradedSectionAlgebra f U
  let := formalGradedAffineModule f I F U
  let := formalGradedAffineModule_scalarTower_left f I F U
  let : Module.Finite Γ(X, U) Γ(F.gradedPiece 0, U) :=
    QuasiCoherent.finite_sections_of_affineLocallyFiniteType _
      (F.gradedPiece_coherent 0) ⟨U, hU⟩
  let : Module.Finite (Γ(X, U) ⊗[A] I.associatedGraded)
      ((Γ(X, U) ⊗[A] I.associatedGraded) ⊗[Γ(X, U)] Γ(F.gradedPiece 0, U)) :=
    Module.Finite.base_change Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded)
      Γ(F.gradedPiece 0, U)
  exact Module.Finite.of_surjective (formalGradedAffinePresentation f I F U)
    (formalGradedAffinePresentation_surjective f I F U hU)

end AlgebraicGeometry.Scheme.Cohomology
