/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Square
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # Scalar extension of a complete original additive square

Retain the four objects and four maps of one supplied additive square.
Their specified scalar actions and actual linearity produce its scalar-extension
square together, without independently reconstructing any cohomology object.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u w

namespace ModuleCat

/-- Scalarize a whole original additive square, then transpose its two
semilinear edges using the original scalar adjunction. -/
def extendAdditiveSquare {R S : Type u} [CommRing R] [CommRing S] (σ : R →+* S)
    (s : Square AddCommGrpCat.{max u w})
    (m₁ : Module R s.X₁) (m₂ : Module S s.X₂)
    (m₃ : Module R s.X₃) (m₄ : Module S s.X₄)
    (h₁₂ : letI := m₁; letI := m₂;
      ∀ (a : R) (x : s.X₁), s.f₁₂ (a • x) = σ a • s.f₁₂ x)
    (h₁₃ : letI := m₁; letI := m₃;
      ∀ (a : R) (x : s.X₁), s.f₁₃ (a • x) = a • s.f₁₃ x)
    (h₂₄ : letI := m₂; letI := m₄;
      ∀ (a : S) (x : s.X₂), s.f₂₄ (a • x) = a • s.f₂₄ x)
    (h₃₄ : letI := m₃; letI := m₄;
      ∀ (a : R) (x : s.X₃), s.f₃₄ (a • x) = σ a • s.f₃₄ x) :
    Square (ModuleCat.{max u w} S) := by
  letI := m₁
  letI := m₂
  letI := m₃
  letI := m₄
  let A := ModuleCat.of R s.X₁
  let B := ModuleCat.of S s.X₂
  let C := ModuleCat.of R s.X₃
  let D := ModuleCat.of S s.X₄
  let p : A ⟶ (restrictScalars σ).obj B :=
    ModuleCat.ofHom (X := A) (Y := (restrictScalars σ).obj B)
      { __ := s.f₁₂.hom, map_smul' := h₁₂ }
  let b : C ⟶ (restrictScalars σ).obj D :=
    ModuleCat.ofHom (X := C) (Y := (restrictScalars σ).obj D)
      { __ := s.f₃₄.hom, map_smul' := h₃₄ }
  let l : A ⟶ C := ModuleCat.ofHom (X := A) (Y := C)
    { __ := s.f₁₃.hom, map_smul' := h₁₃ }
  let r : B ⟶ D := ModuleCat.ofHom (X := B) (Y := D)
    { __ := s.f₂₄.hom, map_smul' := h₂₄ }
  let adj := extendRestrictScalarsAdj.{max u w, u, u} σ
  let q := (adj.homEquiv _ _).symm p
  let δ := (adj.homEquiv _ _).symm b
  have hq (x : s.X₁) : q ((1 : S) ⊗ₜ[R,σ] x) = s.f₁₂ x :=
    congrArg (fun f => f x) ((adj.homEquiv _ _).apply_symm_apply p)
  have hδ (x : s.X₃) : δ ((1 : S) ⊗ₜ[R,σ] x) = s.f₃₄ x :=
    congrArg (fun f => f x) ((adj.homEquiv _ _).apply_symm_apply b)
  refine { X₁ := (extendScalars σ).obj A, X₂ := B
           X₃ := (extendScalars σ).obj C, X₄ := D
           f₁₂ := q, f₁₃ := (extendScalars σ).map l, f₂₄ := r, f₃₄ := δ, fac := ?_ }
  apply ExtendScalars.hom_ext
  intro x
  change r (q ((1 : S) ⊗ₜ[R,σ] x)) =
    δ ((extendScalars σ).map l ((1 : S) ⊗ₜ[R,σ] x))
  calc
    _ = s.f₂₄ (s.f₁₂ x) := congrArg r (hq x)
    _ = s.f₃₄ (s.f₁₃ x) := ConcreteCategory.congr_hom s.fac x
    _ = δ ((1 : S) ⊗ₜ[R,σ] l x) := (hδ (l x)).symm
    _ = _ := congrArg δ (ExtendScalars.map_tmul σ l 1 x).symm

end ModuleCat

namespace CategoryTheory.Square

/-- Transport the lower row of the same square through its specified original
isomorphisms, keeping its top edge unchanged. -/
def transportBottom {C : Type*} [Category* C] (s : Square C)
    {A B : C} (e₃ : s.X₃ ≅ A) (e₄ : s.X₄ ≅ B) : Square C where
  X₁ := s.X₁
  X₂ := s.X₂
  X₃ := A
  X₄ := B
  f₁₂ := s.f₁₂
  f₁₃ := s.f₁₃ ≫ e₃.hom
  f₂₄ := s.f₂₄ ≫ e₄.hom
  f₃₄ := e₃.inv ≫ s.f₃₄ ≫ e₄.hom
  fac := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, s.fac]
    simp only [Category.assoc]

end CategoryTheory.Square

namespace CategoryTheory.Adjunction

/-- Evaluation of the original whiskered mate is the original component mate. -/
theorem whiskerRight_homEquiv_symm_app
    {I C D : Type*} [Category* I] [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (F : I ⥤ C) (G : I ⥤ D) (η : F ⟶ G ⋙ R) (i : I) :
    (((adj.whiskerRight I).homEquiv F G).symm η).app i =
      (adj.homEquiv (F.obj i) (G.obj i)).symm (η.app i) := by
  simp only [Adjunction.homEquiv_symm_apply, NatTrans.comp_app,
    Functor.whiskeringRight_obj_map, Functor.whiskerRight_app,
    Adjunction.whiskerRight_counit_app_app]

end CategoryTheory.Adjunction
