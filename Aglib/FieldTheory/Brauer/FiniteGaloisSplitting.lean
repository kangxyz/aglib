/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Brauer.GenericSeparableElement
public import Aglib.FieldTheory.Brauer.MaximalSubfield
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Finite Galois splitting of central division algebras over infinite fields

An algebraic-closure splitting yields a full-degree separable element by the
generic-resultant argument. Its native root-adjunction field embeds into the
division algebra and therefore splits it. Passing matrix coefficients to the
native splitting field of the minimal polynomial gives a finite Galois matrix
representation, which is an equivalence by simplicity and dimension.
-/

@[expose] public noncomputable section

open scoped TensorProduct IsMulCommutative
open Polynomial

universe u v

namespace Algebra

private theorem nonempty_matrix_of_representation
    {K L D : Type*} [Field K] [Field L] [DivisionRing D]
    [Algebra K L] [Algebra K D] [FiniteDimensional K D] [IsCentral K D]
    {n : ℕ} [NeZero n] (hD : Module.finrank K D = n ^ 2)
    (f : D →ₐ[K] Matrix (Fin n) (Fin n) L) :
    Nonempty (L ⊗[K] D ≃ₐ[L] Matrix (Fin n) (Fin n) L) := by
  let C : CSA K := { toAlgCat := AlgCat.of K D }
  let : IsSimpleRing (L ⊗[K] D) := CSA.isSimpleRing_baseChange C L
  let g : L ⊗[K] D →ₐ[L] Matrix (Fin n) (Fin n) L :=
    AlgHom.liftEquiv K L D (Matrix (Fin n) (Fin n) L) f
  have hi : Function.Injective g := g.toRingHom.injective
  have hd : Module.finrank L (L ⊗[K] D) =
      Module.finrank L (Matrix (Fin n) (Fin n) L) := by
    rw [Module.finrank_baseChange, hD, Module.finrank_matrix]
    simp [pow_two]
  exact ⟨AlgEquiv.ofBijective g ⟨hi,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd
      (f := g.toLinearMap)).mp hi⟩⟩

/-- A finite-dimensional central division algebra over an infinite field has
an actual finite Galois matrix splitting. The splitting field is constructed
from a separable minimal polynomial, not postulated as a structure field. -/
theorem exists_finiteGalois_matrix_splitting
    (K : Type u) (D : Type v) [Field K] [Infinite K] [DivisionRing D]
    [Algebra K D] [FiniteDimensional K D] [IsCentral K D] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : IsGalois K L) (n : ℕ) (_ : NeZero n),
      Nonempty (L ⊗[K] D ≃ₐ[L] Matrix (Fin n) (Fin n) L) := by
  classical
  let C : CSA K := { toAlgCat := AlgCat.of K D }
  obtain ⟨n, hn, ⟨e⟩⟩ := CSA.exists_matrix_baseChange_of_isAlgClosed C (AlgebraicClosure K)
  have hD : Module.finrank K D = n ^ 2 := CSA.finrank_eq_sq_of_baseChange_matrix C _ n e
  obtain ⟨a, hs, ha⟩ := exists_separable_minpoly_natDegree_of_splitting e
  have hi : IsIntegral K a := Algebra.IsIntegral.isIntegral a
  let p := minpoly K a
  let : Fact (Irreducible p) := ⟨minpoly.irreducible hi⟩
  let E := AdjoinRoot p
  let pb := AdjoinRoot.powerBasis (minpoly.ne_zero hi)
  let : FiniteDimensional K E := pb.finite
  have hE : Module.finrank K E = n := pb.finrank.trans ha
  let S := Algebra.adjoin K ({a} : Set D)
  let aS : S := ⟨a, Algebra.subset_adjoin (Set.mem_singleton a)⟩
  have hzS : p.aeval aS = 0 := by
    apply Subtype.val_injective
    change S.val (p.aeval aS) = S.val 0
    rw [map_zero, ← Polynomial.aeval_algHom_apply]
    exact minpoly.aeval K a
  let j : E →ₐ[K] D := S.val.comp
    (AdjoinRoot.liftAlgHom p (Algebra.ofId K S) aS hzS)
  obtain ⟨eE⟩ := nonempty_matrix_of_subfield_finrank j n hD hE
  let L := p.SplittingField
  let : IsGalois K L := IsGalois.of_separable_splitting_field hs
  have hp : p.degree ≠ 0 := Polynomial.degree_ne_of_natDegree_ne (by
    change (minpoly K a).natDegree ≠ 0
    rw [ha]
    exact NeZero.ne n)
  obtain ⟨z, hz⟩ := (Polynomial.SplittingField.splits p).exists_eval_eq_zero
    (by simpa only [Polynomial.degree_map] using hp)
  have hzL : p.aeval z = 0 := by
    rw [← Polynomial.eval_map_algebraMap]
    exact hz
  let jL : E →ₐ[K] L := AdjoinRoot.liftAlgHom p (Algebra.ofId K L) z hzL
  let f : D →ₐ[K] Matrix (Fin n) (Fin n) L := jL.mapMatrix.comp
    ((eE.restrictScalars K).toAlgHom.comp Algebra.TensorProduct.includeRight)
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, n, hn,
    nonempty_matrix_of_representation hD f⟩

end Algebra
