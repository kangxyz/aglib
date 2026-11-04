/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.EvaluationLaws

/-! # The original all-test character correspondence is contravariantly functorial -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

universe u
open AlgebraicGeometry.Scheme.OverField (FScheme Base)
attribute [local instance] Over.cartesianMonoidalCategory

private theorem groupPullbackBaseMap_tensor {k : Type u} [Field k]
    (G : Grp (FScheme k)) {T U : FScheme k} (h : U ⟶ T) :
    groupPullbackBaseMap G h = (𝟙 G.X ⊗ₘ h).left := rfl

private theorem groupPullbackMap_tensor {k : Type u} [Field k]
    {G H : Grp (FScheme k)} (f : G ⟶ H) (T : FScheme k) :
    ((Over.pullback T.hom).mapGrp.map f).hom.hom.left = (f.hom.hom ⊗ₘ 𝟙 T).left := by
  apply pullback.hom_ext
  · rw [Over.tensorHom_left_fst]
    exact BaseChange.groupSchemeBaseChange_map_left_fst T.hom f
  · rw [Over.tensorHom_left_snd, Over.id_left, Category.comp_id]
    exact BaseChange.groupSchemeBaseChange_map_left_snd T.hom f

variable {k : Type u} [Field k]
  {G H : Grp (FScheme k)} [IsFinite G.X.hom] [IsCommMonObj G.X]
  [IsFinite H.X.hom] [IsCommMonObj H.X]

/-- A point composed with the original dual map represents precomposition by the original map. -/
theorem characterOfPoint_dualMap (f : G ⟶ H) (T : FScheme k)
    (p : T ⟶ (dualGroup H).X) :
    characterOfPoint G T (p ≫ (dualMap f).hom.hom) =
      (Over.pullback T.hom).mapGrp.map f ≫ characterOfPoint H T p := by
  have he : (𝟙 G.X ⊗ₘ (p ≫ (dualMap f).hom.hom)) ≫ evaluation G =
      (f.hom.hom ⊗ₘ 𝟙 T) ≫ (𝟙 H.X ⊗ₘ p) ≫ evaluation H := by
    calc
      _ = (𝟙 G.X ⊗ₘ p) ≫ (𝟙 G.X ⊗ₘ (dualMap f).hom.hom) ≫
          evaluation G := by
        rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
      _ = (𝟙 G.X ⊗ₘ p) ≫ (f.hom.hom ⊗ₘ 𝟙 (dualGroup H).X) ≫
          evaluation H := by rw [← evaluation_naturality f]
      _ = _ := by
        simp only [← Category.assoc, tensorHom_comp_tensorHom,
          Category.id_comp, Category.comp_id]
  have hc := congrArg (fun a => a.left ≫ prod.snd) he
  simp only [Over.comp_left, Category.assoc] at hc
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · rw [characterOfPoint_evaluation]
    simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc]
    rw [characterOfPoint_evaluation, groupPullbackMap_tensor,
      groupPullbackBaseMap_tensor, groupPullbackBaseMap_tensor]
    exact hc

/-- The same original character equivalence is contravariantly natural in the group. -/
theorem characterEquiv_dualMap (f : G ⟶ H) (T : FScheme k)
    (p : T ⟶ (dualGroup H).X) :
    characterEquiv G T (p ≫ (dualMap f).hom.hom) =
      (Over.pullback T.hom).mapGrp.map f ≫ characterEquiv H T p :=
  characterOfPoint_dualMap f T p

end AlgebraicGeometry.Scheme.Group.CartierDuality
