/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # Section-preserving Noetherian descent for a standard smooth algebra

The original section maps a finite-type model into the original base ring.
Its actual range is a finite-type integer subalgebra of that base. Base change
to this same range gives a standard smooth model with a genuine retraction.
The native tensor cancellation isomorphism retains the whole original section
map, not just selected equations or an additional descent certificate.
-/

@[expose] public noncomputable section
open scoped TensorProduct

namespace Algebra.IsStandardSmoothOfRelativeDimension
universe u

/-- A standard smooth algebra with its original section descends to a finite
integer subalgebra together with a genuine section. The original algebra and
whole section are recovered by the native base-change comparison. -/
theorem exists_subalgebra_fg_with_section
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    (n : ℕ) [IsStandardSmoothOfRelativeDimension n R B] (σ : B →ₐ[R] R) :
    ∃ (S : Subalgebra ℤ R) (D : Type u) (_ : CommRing D) (_ : Algebra S D),
      S.FG ∧ IsStandardSmoothOfRelativeDimension n S D ∧
      ∃ (e : R ⊗[S] D ≃ₐ[R] B) (τ : D →ₐ[S] S),
        σ.comp e.toAlgHom = Algebra.TensorProduct.lift (AlgHom.id R R)
          ((Algebra.ofId S R).comp τ) (fun _ _ => Commute.all _ _) := by
  obtain ⟨A, D₀, hD₀, hAD₀, hA, hstandard, ⟨e₀⟩⟩ :=
    exists_subalgebra_fg (R := ℤ) (A := R) (B := B) n
  let : CommRing D₀ := hD₀
  let : Algebra A D₀ := hAD₀
  let : IsStandardSmoothOfRelativeDimension n A D₀ := hstandard
  let : Algebra.IsStandardSmooth A D₀ :=
    IsStandardSmoothOfRelativeDimension.isStandardSmooth (R := A) (S := D₀) n
  let F : R ⊗[A] D₀ →ₐ[R] R := σ.comp e₀.symm.toAlgHom
  let φ : D₀ →ₐ[A] R := (F.restrictScalars A).comp Algebra.TensorProduct.includeRight
  let U : Subalgebra A R := φ.range
  let S : Subalgebra ℤ R := U.restrictScalars ℤ
  let : Algebra A S := U.algebra
  let : IsScalarTower A S R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.FiniteType ℤ A := A.fg_iff_finiteType.mp hA
  let : Algebra.FiniteType A U :=
    Algebra.FiniteType.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  let : Algebra.FiniteType ℤ S :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℤ A)
      (inferInstance : Algebra.FiniteType A U)
  let D := S ⊗[A] D₀
  let τ : D →ₐ[S] S := Algebra.TensorProduct.lift (AlgHom.id S S)
    φ.rangeRestrict (fun _ _ => Commute.all _ _)
  let e : R ⊗[S] D ≃ₐ[R] B :=
    (Algebra.TensorProduct.cancelBaseChange A S R R D₀).trans e₀.symm
  refine ⟨S, D, inferInstance, inferInstance, S.fg_iff_finiteType.mpr inferInstance,
    inferInstance, e, τ, ?_⟩
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · ext d
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply, AlgEquiv.toAlgHom_apply,
        e, AlgEquiv.trans_apply, Algebra.TensorProduct.lift_tmul,
        one_mul, Algebra.ofId_apply, map_one]
      rw [Algebra.TensorProduct.cancelBaseChange_tmul A S R R D₀ (1 : R) (1 : S) d,
        one_smul]
      have hτ : τ (1 ⊗ₜ[A] d) = φ.rangeRestrict d := by
        exact (Algebra.TensorProduct.lift_tmul (AlgHom.id S S) φ.rangeRestrict
          (fun _ _ => Commute.all _ _) (1 : S) d).trans (one_mul _)
      rw [hτ]
      rfl

end Algebra.IsStandardSmoothOfRelativeDimension
