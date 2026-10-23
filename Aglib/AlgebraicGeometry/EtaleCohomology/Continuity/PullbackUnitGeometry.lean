/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackUnitRepresentatives

/-! # Relative test morphisms for original inverse-image units -/
@[expose] public noncomputable section
open CategoryTheory Limits Opposite

private theorem projected_composite {C : Type*} [Category C]
    {A B D E H J K : C} (b : A ⟶ B) (m : B ⟶ D) (i : D ⟶ E)
    (p : E ⟶ H) (q : D ⟶ J) (s : J ⟶ H) (r : B ⟶ K) (t : K ⟶ J)
    (hi : i ≫ p = q ≫ s) (hm : m ≫ q = r ≫ t) :
    (b ≫ m ≫ i) ≫ p = b ≫ r ≫ t ≫ s := by
  rw [Category.assoc, Category.assoc, hi, ← Category.assoc m, hm, Category.assoc r]

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge

/-- First projection of the original site composition isomorphism. -/
theorem siteBaseChangeComp_inv_fst {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
    (U : X.Etale) :
    ((siteBaseChangeComp f g).inv.app U).left ≫ pullback.fst U.hom (g ≫ f) =
      pullback.fst (pullback.snd U.hom f) g ≫ pullback.fst U.hom f := by
  change ((pullbackLeftPullbackSndIso U.hom f g).hom ≫
      (pullback.congrHom (rfl : U.hom = U.hom) (rfl : g ≫ f = g ≫ f)).inv) ≫
      pullback.fst U.hom (g ≫ f) = _
  simp only [Category.assoc, pullback.congrHom_inv, pullback.lift_fst,
    Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]

/-- Projection of a composed test morphism to the original chart. -/
theorem composedTestMap_fst {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
    {U : X.Etale} {V : S.Etale} {W : T.Etale}
    (a : V ⟶ (siteBaseChange f).obj U) (b : W ⟶ (siteBaseChange g).obj V) :
    (composedTestMap f g a b).left ≫ pullback.fst U.hom (g ≫ f) =
      b.left ≫ pullback.fst V.hom g ≫ a.left ≫ pullback.fst U.hom f := by
  have hm : ((siteBaseChange g).map a).left ≫ pullback.fst (pullback.snd U.hom f) g =
      pullback.fst V.hom g ≫ a.left := by
    change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    exact pullback.lift_fst _ _ _
  exact projected_composite b.left ((siteBaseChange g).map a).left
    ((siteBaseChangeComp f g).inv.app U).left _ _ _ _ _
    (siteBaseChangeComp_inv_fst f g U) hm

/-- A terminal test map is determined by its projection to the original chart. -/
theorem terminalTestMap_ext {X S : Scheme.{u}} (f : S ⟶ X) (U : X.Etale)
    {a b : etaleTerminal S ⟶ (siteBaseChange f).obj U}
    (h : a.left ≫ pullback.fst U.hom f = b.left ≫ pullback.fst U.hom f) : a = b := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · exact h
  · exact (MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm

/-- The terminal pullback comparison has the expected first projection. -/
theorem siteBaseChangeTerminalIso_inv_fst {X S : Scheme.{u}} (f : S ⟶ X) :
    (siteBaseChangeTerminalIso f).inv.left ≫ pullback.fst (𝟙 X) f = f := by
  have h := congrArg (fun k => (siteBaseChangeTerminalIso f).inv.left ≫ k)
    (pullback.condition (f := 𝟙 X) (g := f))
  have hw : (siteBaseChangeTerminalIso f).inv.left ≫ pullback.snd (𝟙 X) f = 𝟙 S :=
    MorphismProperty.Over.w (siteBaseChangeTerminalIso f).inv
  have h₀ := congrArg (fun k => (siteBaseChangeTerminalIso f).inv.left ≫ k)
    (Category.comp_id (pullback.fst (𝟙 X) f))
  have h₁ : (siteBaseChangeTerminalIso f).inv.left ≫ pullback.fst (𝟙 X) f =
      ((siteBaseChangeTerminalIso f).inv.left ≫ pullback.snd (𝟙 X) f) ≫ f :=
    h₀.symm.trans (h.trans (Category.assoc _ _ _).symm)
  exact h₁.trans ((congrArg (fun k => k ≫ f) hw).trans (Category.id_comp f))

/-- The original chart projection of an arbitrary base-change test morphism. -/
def unitRepresentativeArrow {X S : Scheme.{u}} (f : S ⟶ X)
    {U : X.Etale} {W : S.Etale} (a : W ⟶ (siteBaseChange f).obj U) :
    Over.mk (W.hom ≫ f) ⟶ Over.mk U.hom :=
  Over.homMk (a.left ≫ pullback.fst U.hom f) (by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => a.left ≫ k) (pullback.condition (f := U.hom) (g := f))).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ f) (MorphismProperty.Over.w a)))))

/-- A relative chart arrow gives a terminal test morphism over its domain. -/
def relativeTerminalTest {X S : Scheme.{u}} (f : S ⟶ X) (U : X.Etale)
    (b : S ⟶ U.left) (h : b ≫ U.hom = f) :
    etaleTerminal S ⟶ (siteBaseChange f).obj U :=
  MorphismProperty.Over.homMk (pullback.lift b (𝟙 S) (h.trans (Category.id_comp f).symm))
    (pullback.lift_snd _ _ _) (by trivial)

/-- The two original tests describing a local representative and a relative section coincide. -/
theorem composedTestMap_diagonal {X S : Scheme.{u}} (f : S ⟶ X)
    {U : X.Etale} {W : S.Etale} (a : W ⟶ (siteBaseChange f).obj U) :
    composedTestMap f W.hom a (chartDiagonal W) =
      relativeTerminalTest (W.hom ≫ f) U (unitRepresentativeArrow f a).left
        (Over.w (unitRepresentativeArrow f a)) := by
  apply terminalTestMap_ext
  have hd := congrArg (fun k => k ≫ a.left ≫ pullback.fst U.hom f)
    (pullback.diagonal_fst W.hom)
  have hx : (chartDiagonal W).left ≫ pullback.fst W.hom W.hom ≫
      a.left ≫ pullback.fst U.hom f = a.left ≫ pullback.fst U.hom f :=
    (Category.assoc _ _ _).symm.trans (hd.trans (Category.id_comp _))
  exact (composedTestMap_fst f W.hom a (chartDiagonal W)).trans
    (hx.trans (pullback.lift_fst _ _ _).symm)

/-- The original terminal comparison followed by a chart diagonal gives the relative test. -/
theorem composedTestMap_terminal {X S : Scheme.{u}} (U : X.Etale) (b : S ⟶ U.left) :
    composedTestMap U.hom b (chartDiagonal U) (siteBaseChangeTerminalIso b).inv =
      relativeTerminalTest (b ≫ U.hom) U b rfl := by
  apply terminalTestMap_ext
  have hd := congrArg (fun k => (siteBaseChangeTerminalIso b).inv.left ≫
    pullback.fst (𝟙 U.left) b ≫ k) (pullback.diagonal_fst U.hom)
  have hx : (siteBaseChangeTerminalIso b).inv.left ≫ pullback.fst (𝟙 U.left) b ≫
      (chartDiagonal U).left ≫ pullback.fst U.hom U.hom = b :=
    hd.trans ((congrArg (fun k => (siteBaseChangeTerminalIso b).inv.left ≫ k)
      (Category.comp_id (pullback.fst (𝟙 U.left) b))).trans
        (siteBaseChangeTerminalIso_inv_fst b))
  exact (composedTestMap_fst U.hom b (chartDiagonal U)
    (siteBaseChangeTerminalIso b).inv).trans (hx.trans (pullback.lift_fst _ _ _).symm)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
