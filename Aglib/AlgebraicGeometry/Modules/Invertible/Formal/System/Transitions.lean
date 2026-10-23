/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.System.Adic

/-! # Original successor units in the native line-bundle system -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Invertible.CompatibleLineBundleSystem

universe u

section Triangle

variable {X Y Z : Scheme.{u}} (p : Y ⟶ X) (v : Z ⟶ Y) (q : Z ⟶ X)
  (h : v ≫ p = q) (M : X.Modules) (L : Y.Modules) (N : Z.Modules)
  (α : (pullback p).obj M ≅ L) (e : (pullback v).obj L ≅ N)

/-- The original pullback composition and equality comparisons, followed by
actual coefficient isomorphisms on a triangle. -/
def triangleCoefficientIso : (pullback q).obj M ≅ N :=
  ((pullbackComp v p).app M ≪≫ (pullbackCongr h).app M).symm ≪≫
    (pullback v).mapIso α ≪≫ e

/-- Pushforward of the original successor unit and coefficient isomorphism,
with the original pushforward composition and equality comparisons. -/
def originalSuccessorMap : (pushforward p).obj L ⟶ (pushforward q).obj N :=
  (pushforward p).map (adjointCoefficientMap v L N e.hom) ≫
    (pushforwardComp v p).hom.app N ≫ (pushforwardCongr h).hom.app N

theorem originalSuccessorMap_eq_unit :
    originalSuccessorMap p v q h L N e =
      (pushforward p).map ((pullbackPushforwardAdjunction v).unit.app L ≫
        (pushforward v).map e.hom) ≫
      (pushforwardComp v p).hom.app N ≫ (pushforwardCongr h).hom.app N := rfl

/-- The original triangle unit is compatible with every actual coefficient
isomorphism. Variable coefficients keep concrete fibre-product conversion out
of the categorical calculation. -/
theorem adjoint_triangleCoefficientIso :
    adjointCoefficientMap q M N (triangleCoefficientIso p v q h M L N α e).hom =
      adjointCoefficientMap p M L α.hom ≫ originalSuccessorMap p v q h L N e := by
  let ε := α.hom
  let c := (pullbackComp v p).app M ≪≫ (pullbackCongr h).app M
  let a := pushforwardComp v p ≪≫ pushforwardCongr h
  let d := c.inv ≫ (pullback v).map ε ≫ e.hom
  let b := (pullbackPushforwardAdjunction v).unit.app ((pullback p).obj M) ≫
    (pushforward v).map c.hom
  have ht : (pullbackPushforwardAdjunction p).unit.app M ≫
      (pushforward p).map b ≫ a.hom.app ((pullback q).obj M) =
        (pullbackPushforwardAdjunction q).unit.app M :=
    pullbackUnit_triangle M p v q h
  have ha : a.hom.app ((pullback q).obj M) ≫ (pushforward q).map d =
      (pushforward p).map ((pushforward v).map d) ≫ a.hom.app N :=
    (a.hom.naturality d).symm
  have hε : (pullbackPushforwardAdjunction v).unit.app ((pullback p).obj M) ≫
      (pushforward v).map ((pullback v).map ε) =
        ε ≫ (pullbackPushforwardAdjunction v).unit.app L :=
    ((pullbackPushforwardAdjunction v).unit.naturality ε).symm
  have hb : b ≫ (pushforward v).map d =
      ε ≫ (pullbackPushforwardAdjunction v).unit.app L ≫ (pushforward v).map e.hom := by
    dsimp only [b, d]
    rw [Category.assoc, ← Functor.map_comp]
    simp only [Iso.hom_inv_id_assoc, Functor.map_comp]
    rw [← Category.assoc, hε, Category.assoc]
  change (pullbackPushforwardAdjunction q).unit.app M ≫ (pushforward q).map d =
    ((pullbackPushforwardAdjunction p).unit.app M ≫ (pushforward p).map ε) ≫
      (pushforward p).map ((pullbackPushforwardAdjunction v).unit.app L ≫
        (pushforward v).map e.hom) ≫ a.hom.app N
  calc
    _ = (pullbackPushforwardAdjunction p).unit.app M ≫
        (pushforward p).map (b ≫ (pushforward v).map d) ≫ a.hom.app N := by
          rw [← ht]
          simp only [Functor.map_comp, Category.assoc]
          rw [ha]
    _ = _ := by
      rw [hb]
      simp only [Functor.map_comp, Category.assoc]

theorem adjoint_triangleCoefficientIso_of_identity
    (a : (pullback p).obj ((pushforward p).obj L) ≅ L)
    (ha : adjointCoefficientMap p ((pushforward p).obj L) L a.hom = 𝟙 _) :
    adjointCoefficientMap q ((pushforward p).obj L) N
        (triangleCoefficientIso p v q h ((pushforward p).obj L) L N a e).hom =
      originalSuccessorMap p v q h L N e := by
  rw [adjoint_triangleCoefficientIso, ha, Category.id_comp]

/-- The original right triangle identity, with the coefficient map folded. -/
theorem adjointCoefficientMap_counit (p : Y ⟶ X) (L : Y.Modules) :
    adjointCoefficientMap p ((pushforward p).obj L) L
      ((pullbackPushforwardAdjunction p).counit.app L) = 𝟙 _ :=
  (pullbackPushforwardAdjunction p).right_triangle_components L

end Triangle

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)} {I : Ideal R}
  (S : CompatibleLineBundleSystem f I)

/-- The native positive transition is the original successor-map unit,
followed by the supplied isomorphism and original geometric comparisons. -/
theorem positiveTransition_original (n : ℕ) :
    S.positiveTransition n = originalSuccessorMap
      (idealThickeningι f (I ^ (n + 2)))
      (idealThickeningMap f (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
      (idealThickeningι f (I ^ (n + 1)))
      (idealThickeningMap_ι f (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
      (S.bundle (n + 1)).val (S.bundle n).val (S.successorIso n) := by
  have hc : S.successorCoefficientIso n = triangleCoefficientIso
      (idealThickeningι f (I ^ (n + 2)))
      (idealThickeningMap f (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
      (idealThickeningι f (I ^ (n + 1)))
      (idealThickeningMap_ι f (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
      (S.positiveTerm (n + 1)) (S.bundle (n + 1)).val (S.bundle n).val
      (S.positiveStageIso (n + 1)) (S.successorIso n) := rfl
  change adjointCoefficientMap _ _ _ (S.successorCoefficientIso n).hom = _
  rw [hc]
  apply adjoint_triangleCoefficientIso_of_identity
  exact adjointCoefficientMap_counit _ _

end AlgebraicGeometry.Scheme.Modules.Invertible.CompatibleLineBundleSystem
