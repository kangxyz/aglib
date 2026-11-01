/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldCoverGluing

/-! # Descent of a prescribed field-valued point to a finite intermediate field

One native fibre retains both the prescribed base point and the original
extension-valued lift. The finite intermediate field comes from the existing
finite-presentation Hom descent; no replacement cover is constructed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

universe u

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]

private theorem exists_finite_field_point_over
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k)) [LocallyOfFinitePresentation p]
    (z : Spec (.of Ω) ⟶ Y) (hz : z ≫ p = Spec.algebraMap k Ω) :
    ∃ (s : Finset Ω) (a : Spec (.of (FieldLimit.finiteField k Ω s)) ⟶ Y),
      a ≫ p = Spec.algebraMap k (FieldLimit.finiteField k Ω s) ∧
      Spec.algebraMap (FieldLimit.finiteField k Ω s) Ω ≫ a = z := by
  let b := Spec.algebraMap k Ω
  let i := 𝟙 (Spec (.of k))
  let q : pullback i b ⟶ Y := pullback.snd i b ≫ z
  have hq : q ≫ p = pullback.fst i b := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => pullback.snd i b ≫ f) hz).trans
        (pullback.condition.symm.trans (Category.comp_id _)))
  let V : Over (Spec (.of k)) := Over.mk p
  let : LocallyOfFinitePresentation V.hom := inferInstanceAs (LocallyOfFinitePresentation p)
  obtain ⟨s, g, hg, he⟩ := FieldLimit.exists_finite_field_hom k Ω i V q hq
  let F := FieldLimit.finiteField k Ω s.unop
  let bF := Spec.algebraMap k F
  let d : Spec (.of F) ⟶ pullback bF i :=
    pullback.lift (𝟙 _) bF (by simp [i])
  let dΩ : Spec (.of Ω) ⟶ pullback i b :=
    pullback.lift b (𝟙 _) (by simp [i])
  have hd : d ≫ pullback.snd bF i = bF := pullback.lift_snd _ _ _
  have hdΩ : dΩ ≫ pullback.snd i b = 𝟙 _ := pullback.lift_snd _ _ _
  have hproj : dΩ ≫ FieldLimit.fieldProjection k Ω i s =
      Spec.algebraMap F Ω ≫ d := by
    let v : pullback i b ⟶ pullback bF i := FieldLimit.fieldProjection k Ω i s
    have hv₁ : v ≫ pullback.fst bF i =
        pullback.snd i b ≫ Spec.algebraMap F Ω := fieldProjection_field k Ω i s.unop
    have hv₂ : v ≫ pullback.snd bF i = pullback.fst i b :=
      FieldLimit.fieldProjection_base k Ω i s
    have hd₁ : d ≫ pullback.fst bF i = 𝟙 _ := pullback.lift_fst _ _ _
    change dΩ ≫ v = Spec.algebraMap F Ω ≫ d
    apply pullback.hom_ext
    · rw [Category.assoc, hv₁, ← Category.assoc, hdΩ, Category.id_comp,
        Category.assoc, hd₁, Category.comp_id]
    · rw [Category.assoc, hv₂, Category.assoc, hd]
      have hleft : dΩ ≫ pullback.fst i b = b := pullback.lift_fst _ _ _
      rw [hleft]
      change Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp]
      congr 1
  refine ⟨s.unop, d ≫ g, ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans ((congrArg (fun f => d ≫ f) hg).trans hd)
  · calc
      Spec.algebraMap F Ω ≫ (d ≫ g) = (dΩ ≫ FieldLimit.fieldProjection k Ω i s) ≫ g :=
        (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ g) hproj.symm)
      _ = dΩ ≫ q := (Category.assoc _ _ _).trans (congrArg (fun f => dΩ ≫ f) he)
      _ = z := (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ z) hdΩ).trans (Category.id_comp _))

/-- A prescribed lift of an original rational point descends to a finite
intermediate field, retaining both the base-point and extension-point equations. -/
theorem exists_finite_field_point
    {U Z : Scheme.{u}} (f : Z ⟶ U) [LocallyOfFinitePresentation f]
    (x : Spec (.of k) ⟶ U) (z : Spec (.of Ω) ⟶ Z)
    (hz : z ≫ f = Spec.algebraMap k Ω ≫ x) :
    ∃ (s : Finset Ω) (a : Spec (.of (FieldLimit.finiteField k Ω s)) ⟶ Z),
      a ≫ f = Spec.algebraMap k (FieldLimit.finiteField k Ω s) ≫ x ∧
      Spec.algebraMap (FieldLimit.finiteField k Ω s) Ω ≫ a = z := by
  let b := Spec.algebraMap k Ω
  let P := pullback f x
  let y : Spec (.of Ω) ⟶ P := pullback.lift z b hz
  have hy : y ≫ pullback.snd f x = b := pullback.lift_snd _ _ _
  obtain ⟨s, a, ha, he⟩ := exists_finite_field_point_over k Ω (pullback.snd f x) y hy
  refine ⟨s, a ≫ pullback.fst f x, ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun g => a ≫ g) (pullback.condition (f := f) (g := x))).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫ x) ha)))
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun g => g ≫ pullback.fst f x) he).trans (pullback.lift_fst _ _ _))

end AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent
