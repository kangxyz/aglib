/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.GeometricPointExtension

/-! # Original geometric Hom fibres under a separably closed field extension -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Transport the point-extension bijection across the actual pullback universal property. -/
theorem bijective_over_precomp_of_pullback {C : Type*} [Category* C]
    {P Q X S : C} (f : X ⟶ S) (ξ : P ⟶ S) (e : Q ⟶ P) [HasPullback f ξ]
    (hb : Function.Bijective
      (fun s : Over.mk (𝟙 P) ⟶ Over.mk (pullback.snd f ξ) =>
        (Over.homMk e (Category.comp_id e) : Over.mk e ⟶ Over.mk (𝟙 P)) ≫ s)) :
    Function.Bijective
      (fun s : Over.mk ξ ⟶ Over.mk f =>
        (Over.homMk e rfl : Over.mk (e ≫ ξ) ⟶ Over.mk ξ) ≫ s) := by
  constructor
  · intro p q h
    let p₀ : Over.mk (𝟙 P) ⟶ Over.mk (pullback.snd f ξ) :=
      Over.homMk (pullback.lift p.left (𝟙 _) (by simpa using p.w))
        (pullback.lift_snd _ _ _)
    let q₀ : Over.mk (𝟙 P) ⟶ Over.mk (pullback.snd f ξ) :=
      Over.homMk (pullback.lift q.left (𝟙 _) (by simpa using q.w))
        (pullback.lift_snd _ _ _)
    have h₀ : (Over.homMk e (Category.comp_id e) : Over.mk e ⟶ Over.mk (𝟙 P)) ≫ p₀ =
        (Over.homMk e (Category.comp_id e) : Over.mk e ⟶ Over.mk (𝟙 P)) ≫ q₀ := by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · have h' := congrArg (fun k => k.left) h
        simpa [p₀, q₀, Category.assoc, pullback.lift_fst, pullback.lift_snd] using h'
      · simp [p₀, q₀, Category.assoc, pullback.lift_snd]
    have he := congrArg (fun k => k.left ≫ pullback.fst f ξ) (hb.1 h₀)
    apply Over.OverMorphism.ext
    simpa [p₀, q₀, pullback.lift_fst] using he
  · intro p
    let p₀ : Over.mk e ⟶ Over.mk (pullback.snd f ξ) :=
      Over.homMk (pullback.lift p.left e p.w) (pullback.lift_snd _ _ _)
    obtain ⟨s, hs⟩ := hb.2 p₀
    have hsw : s.left ≫ pullback.snd f ξ = 𝟙 P := s.w
    have hq : (s.left ≫ pullback.fst f ξ) ≫ f = ξ := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hsw]
      exact Category.id_comp ξ
    refine ⟨Over.homMk (s.left ≫ pullback.fst f ξ) hq, ?_⟩
    apply Over.OverMorphism.ext
    have he := congrArg (fun k => k.left ≫ pullback.fst f ξ) hs
    simpa [p₀, Category.assoc, pullback.lift_fst] using he

end CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

variable {κ Ω : Type u} [Field κ] [IsSepClosed κ] [Field Ω]
  {X : Scheme.{u}} (ξ : Spec (.of κ) ⟶ X) (e : Spec (.of Ω) ⟶ Spec (.of κ))

/-- The original map on actual geometric Hom fibres is precomposition by the field map. -/
def pointFiberExtension (U : X.Etale) :
    (Over.mk ξ ⟶ (Scheme.Etale.forget X).obj U) →
      (Over.mk (e ≫ ξ) ⟶ (Scheme.Etale.forget X).obj U) :=
  fun p => (Over.homMk e rfl : Over.mk (e ≫ ξ) ⟶ Over.mk ξ) ≫ p

/-- Actual geometric Hom fibres are unchanged by extension of the separably closed field. -/
theorem pointFiberExtension_bijective (U : X.Etale) :
    Function.Bijective (pointFiberExtension ξ e U) := by
  have : Etale U.hom := U.prop
  exact bijective_over_precomp_of_pullback U.hom ξ e
    (bijective_etale_point_extension e (pullback.snd U.hom ξ))

end AlgebraicGeometry.Scheme.EtaleCohomology
