/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.FrobeniusEquation.Module
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Actual etale root spectra for semilinear tensor equations

The original polynomial root algebra is bundled once as a native algebra over
the base. Its actual structural algebra morphism gives an etale-surjective
spectrum map, and the solution retains the original tensor restriction map.
No sheaf section realization or nontriviality assumption is used.
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

variable (A : CommRingCat.{u}) {M : Type v} [AddCommGroup M] [Module A M]
  [Module.Free A M] [Module.Finite A M]
  (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
  (Φ : M →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA] M)
  (B : CommAlgCat.{u} A) [Etale (Spec.map (CommRingCat.ofHom (algebraMap A B)))]

/-- Every original tensor section has a root on an actual etale-surjective
spectrum. The root algebra remains in the base universe even for a larger module. -/
theorem exists_etale_surjective_frobenius_solution (y : B ⊗[A] M) :
    ∃ (C : CommAlgCat.{u} A) (f : B ⟶ C),
      Etale (Spec.map (CommRingCat.ofHom f.hom.toRingHom)) ∧
      Surjective (Spec.map (CommRingCat.ofHom f.hom.toRingHom)) ∧
      Etale (Spec.map (CommRingCat.ofHom (algebraMap A C))) ∧
      ∃ z : C ⊗[A] M, LinearMap.frobeniusBaseChange p hp hA Φ C z - z =
        f.hom.toLinearMap.rTensor M y := by
  obtain ⟨C, hring, hBC, hAC, htower, het, hsurj, z, hz⟩ :=
    Algebra.FrobeniusEquation.exists_etale_surjective_solution p hp hA Φ B y
  let := hring
  let := hBC
  let := hAC
  let := htower
  let := het
  have hcov : Etale (Spec.map (CommRingCat.ofHom (algebraMap B C))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    change (algebraMap B C).Etale
    rw [RingHom.etale_algebraMap]
    infer_instance
  let := hcov
  let f : B ⟶ CommAlgCat.of A C := CommAlgCat.ofHom (IsScalarTower.toAlgHom A B C)
  let q := (algSpec A).map f.op
  have hcomp : Spec.map (CommRingCat.ofHom (algebraMap A C)) =
      Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)) := q.w.symm
  have hC : Etale (Spec.map (CommRingCat.ofHom (algebraMap A C))) := by
    rw [hcomp]
    infer_instance
  refine ⟨CommAlgCat.of A C, f, hcov, ⟨hsurj⟩, hC, z, ?_⟩
  rw [LinearMap.rTensor_def]
  exact hz

end AlgebraicGeometry.Scheme
