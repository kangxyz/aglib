/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Common affine refinements for two charts over a scheme morphism

The affine refinement of a pulled-back open cover supplies pointwise common
refinements of two affine chart pairs. All comparison equations are equations
of the original scheme morphisms. No finiteness or flatness is needed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- Two affine chart pairs over a morphism have a common affine refinement near
every point of their actual overlap, on both the source and base. -/
-- Retain both open-chart hypotheses in the symmetric public interface.
@[nolint unusedArguments]
theorem exists_commonAffineBaseChangeRefinement
    {V X : Scheme.{u}} (g : V ⟶ X)
    {R₁ R₂ S₁ S₂ : CommRingCat.{u}}
    (j₁ : Spec R₁ ⟶ X) (j₂ : Spec R₂ ⟶ X)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (v₁ : Spec S₁ ⟶ V) (v₂ : Spec S₂ ⟶ V)
    [IsOpenImmersion v₁] [IsOpenImmersion v₂]
    (r₁ : Spec S₁ ⟶ Spec R₁) (r₂ : Spec S₂ ⟶ Spec R₂)
    (h₁ : r₁ ≫ j₁ = v₁ ≫ g) (h₂ : r₂ ≫ j₂ = v₂ ≫ g)
    (x : (pullback v₁ v₂ : Scheme.{u})) :
    ∃ (A B : CommRingCat.{u}) (s : Spec A ⟶ X)
      (z : Spec B ⟶ pullback v₁ v₂)
      (ρ₁ : Spec A ⟶ Spec R₁) (ρ₂ : Spec A ⟶ Spec R₂)
      (r : Spec B ⟶ Spec A),
      IsOpenImmersion s ∧ IsOpenImmersion z ∧
      IsOpenImmersion ρ₁ ∧ IsOpenImmersion ρ₂ ∧ x ∈ Set.range z ∧
      ρ₁ ≫ j₁ = s ∧ ρ₂ ≫ j₂ = s ∧
      r ≫ ρ₁ = z ≫ pullback.fst v₁ v₂ ≫ r₁ ∧
      r ≫ ρ₂ = z ≫ pullback.snd v₁ v₂ ≫ r₂ := by
  classical
  let T : Scheme.{u} := pullback v₁ v₂
  let U : Scheme.{u} := pullback j₁ j₂
  have hw : (pullback.fst v₁ v₂ ≫ r₁) ≫ j₁ =
      (pullback.snd v₁ v₂ ≫ r₂) ≫ j₂ := by
    simp only [Category.assoc]
    rw [h₁, h₂]
    simpa only [Category.assoc] using
      congrArg (fun k => k ≫ g) (pullback.condition (f := v₁) (g := v₂))
  let φ : T ⟶ U := pullback.lift
    (pullback.fst v₁ v₂ ≫ r₁) (pullback.snd v₁ v₂ ≫ r₂) hw
  let C : U.AffineOpenCover := U.affineOpenCover
  let D : T.OpenCover := C.openCover.pullback₁ φ
  let E : T.AffineOpenCover := D.affineRefinement
  let a := D.fromAffineRefinement
  let i := E.openCover.idx x
  let k := a.s₀ i
  let u : Spec (C.X k) ⟶ U := C.f k
  let z : Spec (E.X i) ⟶ T := E.f i
  let r : Spec (E.X i) ⟶ Spec (C.X k) := a.h₀ i ≫ C.openCover.pullbackHom φ k
  let ρ₁ : Spec (C.X k) ⟶ Spec R₁ := u ≫ pullback.fst j₁ j₂
  let ρ₂ : Spec (C.X k) ⟶ Spec R₂ := u ≫ pullback.snd j₁ j₂
  let s : Spec (C.X k) ⟶ X := ρ₁ ≫ j₁
  have hr : r ≫ u = z ≫ φ := by
    dsimp only [r, u, z]
    erw [Category.assoc, Cover.pullbackHom_map, ← Category.assoc, a.w₀]
  let hu : IsOpenImmersion u := C.map_prop k
  let hz : IsOpenImmersion z := E.map_prop i
  let hρ₁ : IsOpenImmersion ρ₁ := by dsimp only [ρ₁]; infer_instance
  let hρ₂ : IsOpenImmersion ρ₂ := by dsimp only [ρ₂]; infer_instance
  have hs : IsOpenImmersion s := by dsimp only [s]; infer_instance
  refine ⟨C.X k, E.X i, s, z, ρ₁, ρ₂, r, hs, hz, hρ₁, hρ₂,
    E.openCover.covers x, rfl, ?_, ?_, ?_⟩
  · dsimp only [ρ₂, s, ρ₁]
    simpa only [Category.assoc] using
      congrArg (fun k => u ≫ k) (pullback.condition (f := j₁) (g := j₂)).symm
  · dsimp only [ρ₁]
    rw [← Category.assoc, hr, Category.assoc]
    simp only [φ, pullback.lift_fst]
  · dsimp only [ρ₂]
    rw [← Category.assoc, hr, Category.assoc]
    simp only [φ, pullback.lift_snd]

end AlgebraicGeometry.Scheme
