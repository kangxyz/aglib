/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.Basic

/-!
# Original inverse on homogeneous Kunneth classes

The one selected degreewise inverse and total-source inverse retain the
original homogeneous inclusions. Degree-one support is proved at its consumer.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct DirectSum

universe u m n p

namespace DirectSum

variable {R : Type u} [CommSemiring R]
  {M : ℕ → Type m} {N : ℕ → Type n}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ j, AddCommMonoid (N j)] [∀ j, Module R (N j)]

/-- Evaluate the original degree-one source support at one class before any
cohomology family or degreewise inverse is specialized. -/
theorem equivAfterEquiv_symm_degreeOne_apply_of_source
    {P : ℕ → Type p} [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
    (E : ((⨁ i, M i) ⊗[R] ⨁ j, N j) ≃ₗ[R]
      ⨁ d, ⨁ t : HomologicalComplex₂.TotalDegree d,
        M t.val.1 ⊗[R] N t.val.2)
    (hE : E = tensorFiberEquiv (R := R) M N
      (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)))
    (e : ∀ d, (⨁ t : HomologicalComplex₂.TotalDegree d,
      M t.val.1 ⊗[R] N t.val.2) ≃ₗ[R] P d)
    (C : ((⨁ i, M i) ⊗[R] ⨁ j, N j) ≃ₗ[R] ⨁ d, P d)
    (hC : C = equivAfterEquiv E e) (z : P 1) :
    TensorProduct.map
        (lof R ℕ M 0 ∘ₗ DFinsupp.lapply 0)
        (lof R ℕ N 1 ∘ₗ DFinsupp.lapply 1)
        (C.symm (lof R ℕ P 1 z)) +
      TensorProduct.map
        (lof R ℕ M 1 ∘ₗ DFinsupp.lapply 1)
        (lof R ℕ N 0 ∘ₗ DFinsupp.lapply 0)
        (C.symm (lof R ℕ P 1 z)) =
      C.symm (lof R ℕ P 1 z) := by
  subst C
  subst E
  have hSource := tensorFiberEquiv_symm_degreeOne (R := R) M N
    (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)) rfl
  have hWhole := equivAfterEquiv_symm_support
    (tensorFiberEquiv (R := R) M N
      (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)))
    e 1
    (TensorProduct.map (lof R ℕ M 0 ∘ₗ DFinsupp.lapply 0)
      (lof R ℕ N 1 ∘ₗ DFinsupp.lapply 1))
    (TensorProduct.map (lof R ℕ M 1 ∘ₗ DFinsupp.lapply 1)
      (lof R ℕ N 0 ∘ₗ DFinsupp.lapply 0)) hSource
  have hValue := LinearMap.congr_fun hWhole z
  simp only [LinearMap.add_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap] at hValue
  exact hValue

end DirectSum

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y : FScheme k)

variable [QuasiCompact X.hom] [QuasiSeparated X.hom]
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom]

/-- On every homogeneous class, the inverse is the original antidiagonal inverse. -/
theorem structureExternalLinearEquiv_symm_inclusion (n : ℕ)
    (z : structureCohomology k (X ⊗ Y) n) :
    (structureExternalLinearEquiv X Y).symm (structureCohomologyInclusion (X ⊗ Y) n z) =
      (structureTensorTotalSourceEquiv X Y).symm
        (DirectSum.lof k ℕ _ n ((structureKunnethDegreeEquiv X Y n).symm z)) := by
  exact DirectSum.equivAfterEquiv_symm_lof
    (structureTensorTotalSourceEquiv X Y) (structureKunnethDegreeEquiv X Y) n z

end AlgebraicGeometry.Scheme.Cohomology
