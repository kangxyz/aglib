/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Unramified.PointFactorization
public import Aglib.AlgebraicGeometry.AffineScheme.AlgebraMapTriangles
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Finite separable refinement of a prescribed point of an etale scheme

The original field-valued point factors through an affine neighborhood of its
image. The actual kernel quotient of its coordinate map then gives a finite
separable field chart, preserving the original point rather than selecting an
unrelated point over a Galois extension.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A prescribed field-valued point of an etale scheme over a field refines
through an actual finite separable field chart, with both original triangles. -/
theorem exists_finite_separable_field_point
    (K : Type u) [Field K] {Ω : Type u} [Field Ω] {U : Scheme.{u}}
    (p : U ⟶ Spec (.of K)) [Etale p] (a : Spec (.of Ω) ⟶ U) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
      Module.Finite K L ∧ Algebra.IsSeparable K L ∧
        ∃ (v : Spec (.of L) ⟶ U) (ζ : Spec (.of Ω) ⟶ Spec (.of L)),
          ζ ≫ v = a ∧ v ≫ p = Spec.algebraMap K L := by
  obtain ⟨A, j, _, hj, _⟩ := exists_affine_mem_range_and_range_subset
    (x := a (default : Spec (.of Ω))) (U := ⊤) (by simp)
  have hrange : Set.range a ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    simpa only [Subsingleton.elim x (default : Spec (.of Ω))] using hj
  let a' := IsOpenImmersion.lift j a hrange
  have ha' : a' ≫ j = a := IsOpenImmersion.lift_fac j a hrange
  obtain ⟨g, hg⟩ := Spec.map_surjective (j ≫ p)
  let : Algebra K A := g.hom.toAlgebra
  have hcoord : Spec.algebraMap K A = j ≫ p := hg
  let : Algebra.Etale K A := by
    have he : Etale (Spec.algebraMap K A) := by
      rw [hcoord]
      infer_instance
    exact RingHom.etale_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Etale.{u})).mp he)
  obtain ⟨b, hb⟩ := Spec.map_surjective a'
  let : Algebra K Ω := (b.hom.comp (algebraMap K A)).toAlgebra
  let b' : A →ₐ[K] Ω :=
    { toRingHom := b.hom
      commutes' _ := rfl }
  obtain ⟨L, hL, hKL, hfin, hsep, q, e, he⟩ :=
    Algebra.FormallyUnramified.exists_finite_separable_factorization K b'
  let := hL
  let := hKL
  refine ⟨L, hL, hKL, hfin, hsep,
    Spec.map (CommRingCat.ofHom q.toRingHom) ≫ j,
    Spec.map (CommRingCat.ofHom e.toRingHom), ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp]
    have he' : CommRingCat.ofHom q.toRingHom ≫ CommRingCat.ofHom e.toRingHom = b := by
      apply CommRingCat.hom_ext
      exact congrArg AlgHom.toRingHom he
    rw [he', hb]
    exact ha'
  · rw [Category.assoc, ← hcoord]
    exact Spec.map_algHom_algebraMap q

end AlgebraicGeometry.Scheme
