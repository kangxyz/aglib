/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Affine

/-! Actual field-valued sections of affine algebras, without a finiteness
condition. The finite-etale fibre comparison is its specialization. -/

@[expose] public section


open _root_.AlgebraicGeometry.Scheme.FiniteEtale



noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Spec

universe u
variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]

def affineFieldSectionEquiv (A : CommAlgCat.{u} K) :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ⟶
      (algebraSpecOver K).obj (op A)) ≃ (A →ₐ[K] Ω) where
  toFun p := ((algebraSpecOver K).preimage
    (X := op (CommAlgCat.of K Ω)) (Y := op A) p).unop.hom
  invFun φ := (algebraSpecOver K).map (CommAlgCat.ofHom φ).op
  left_inv p := (algebraSpecOver K).map_preimage
    (X := op (CommAlgCat.of K Ω)) (Y := op A) p
  right_inv φ := by
    change ((algebraSpecOver K).preimage (X := op (CommAlgCat.of K Ω)) (Y := op A)
      ((algebraSpecOver K).map (CommAlgCat.ofHom φ).op)).unop.hom = φ
    rw [_root_.CategoryTheory.Functor.preimage_map]
    rfl

theorem affineFieldSectionEquiv_map {A B : CommAlgCat.{u} K} (f : A ⟶ B)
    (p : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ⟶
      (algebraSpecOver K).obj (op B)) :
    affineFieldSectionEquiv K Ω A (p ≫ (algebraSpecOver K).map f.op) =
      (affineFieldSectionEquiv K Ω B p).comp f.hom := by
  change ((algebraSpecOver K).preimage
      (X := op (CommAlgCat.of K Ω)) (Y := op A)
      (p ≫ (algebraSpecOver K).map f.op)).unop.hom =
    (((algebraSpecOver K).preimage
      (X := op (CommAlgCat.of K Ω)) (Y := op B) p).unop.hom).comp f.hom
  erw [_root_.CategoryTheory.Functor.preimage_comp,
    _root_.CategoryTheory.Functor.preimage_map]
  rfl

end AlgebraicGeometry.Spec

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Morphisms/FiniteEtale/AffineFieldSections.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 638a78665c4862382eb197a6c8627badb03dfb2afb464b5817b6379ca075f878.
Native names and imports replace the source wrappers; stated conditions and maps are retained. -/
