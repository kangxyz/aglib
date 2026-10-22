/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.LimitLocalModels
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Gluing

/-!
# Local cover models on finite intersections

Each intersection is modeled by restricting a model on one containing affine
chart. The intersection itself is not required to be affine or separated.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

universe u v

/-- A cartesian chart comparison transports a cover reconstruction to the
literal pullback square used by the finite-etale base-change functor. -/
def chartComparison {S T U V : Scheme.{u}}
    {r : V ⟶ U} {f : V ⟶ T} {g : U ⟶ S} {π : T ⟶ S}
    (H : IsPullback r f g π) (M : FiniteEtale U) (Y : FiniteEtale T)
    (e : (baseChange r).obj M ≅ (baseChange f).obj Y) :
    (baseChange (pullback.fst g π)).obj M ≅
      (baseChange (pullback.snd g π)).obj Y :=
  (eqToIso (congrArg baseChange H.isoPullback_inv_fst.symm)).app M ≪≫
    (baseChangeComp r H.isoPullback.inv).app M ≪≫
    (baseChange H.isoPullback.inv).mapIso e ≪≫
    (baseChangeComp f H.isoPullback.inv).symm.app Y ≪≫
    (eqToIso (congrArg baseChange H.isoPullback_inv_snd)).app Y

/-- Restricting each common affine model along a specified chart inclusion gives
models of all the chosen subcharts, with their original limit comparisons. -/
theorem exists_common_subchart_models
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {J : Type v} [Finite J] (U V : J → Scheme.{u}) [∀ j, IsAffine (U j)]
    (f : ∀ j, U j ⟶ D.obj i) (g : ∀ j, V j ⟶ D.obj i)
    (l : ∀ j, V j ⟶ U j) (hl : ∀ j, l j ≫ f j = g j)
    (Y : FiniteEtale c.pt) :
    ∃ k : Over i, ∃ M : ∀ j, FiniteEtale ((baseChangeDiagram D i (g j)).obj k),
      ∀ j, Nonempty
        ((baseChange ((baseChangeCone D c i (g j)).π.app k)).obj (M j) ≅
          (baseChange (pullback.fst (c.π.app i) (g j))).obj Y) := by
  let Z (j : J) := (baseChange (pullback.fst (c.π.app i) (f j))).obj Y
  obtain ⟨k, M, e⟩ := exists_common_affine_chart_models D c hc i U f Z
  let a (j : J) : (baseChangeDiagram D i (g j)).obj k ⟶
      (baseChangeDiagram D i (f j)).obj k :=
    pullback.map _ _ _ _ (𝟙 _) (l j) (𝟙 _) (by simp) (by simpa using (hl j).symm)
  let b (j : J) : (baseChangeCone D c i (g j)).pt ⟶
      (baseChangeCone D c i (f j)).pt :=
    pullback.map _ _ _ _ (𝟙 _) (l j) (𝟙 _) (by simp) (by simpa using (hl j).symm)
  have h (j : J) : (baseChangeCone D c i (g j)).π.app k ≫ a j =
      b j ≫ (baseChangeCone D c i (f j)).π.app k := by
    apply pullback.hom_ext
    · simp [a, b, pullback.map, Category.assoc]
    · simp [a, b, pullback.map, Category.assoc]
  refine ⟨k, fun j ↦ (baseChange (a j)).obj (M j), fun j ↦ ⟨?_⟩⟩
  exact (baseChangeComp (a j) ((baseChangeCone D c i (g j)).π.app k)).symm.app (M j) ≪≫
    (eqToIso (congrArg baseChange (h j))).app (M j) ≪≫
    (baseChangeComp ((baseChangeCone D c i (f j)).π.app k) (b j)).app (M j) ≪≫
    (baseChange (b j)).mapIso (Classical.choice (e j)) ≪≫
    (baseChangeComp (pullback.fst (c.π.app i) (f j)) (b j)).symm.app Y ≪≫
    (eqToIso (congrArg baseChange (show b j ≫ pullback.fst (c.π.app i) (f j) =
      pullback.fst (c.π.app i) (g j) by simp [b]))).app Y

end AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent
