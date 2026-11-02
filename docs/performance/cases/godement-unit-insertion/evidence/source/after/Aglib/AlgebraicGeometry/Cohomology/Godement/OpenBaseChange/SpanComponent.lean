/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.OpenBaseChange.FirstSquare
public import Aglib.AlgebraicGeometry.Cohomology.Godement.OpenBaseChange.SecondSquare

/-! # Pasting the original evaluated Godement squares

The two supplied component equations are proved from the original geometric unit
and Godement augmentation naturality. Their original factors paste in the same
ordinary module category, independently of the native whole-span theorem.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u uC vC
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules.Godement

attribute [local instance] openBaseChangeDerivedStandard

private lemma unit_span_pasting {C : Type uC} [Category.{vC} C]
    {A B D E F G : C} {u : A ⟶ B} {p : B ⟶ D} {v : A ⟶ E}
    {q : E ⟶ D} {r : D ⟶ F} {s : E ⟶ G} {t : G ⟶ F}
    (h₁ : u ≫ p = v ≫ q) (h₂ : q ≫ r = s ≫ t) :
    u ≫ p ≫ r = (v ≫ s) ≫ t := by
  calc
    u ≫ p ≫ r = (u ≫ p) ≫ r := (Category.assoc _ _ _).symm
    _ = (v ≫ q) ≫ r := congrArg (fun k => k ≫ r) h₁
    _ = v ≫ (q ≫ r) := Category.assoc _ _ _
    _ = v ≫ (s ≫ t) := congrArg (fun k => v ≫ k) h₂
    _ = (v ≫ s) ≫ t := (Category.assoc _ _ _).symm

variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)

lemma open_unit_span_component (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    (((Scheme.Modules.restrictFunctor j).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (K.obj.X n))) ≫
        (Scheme.Modules.restrictFunctor j).map ((Scheme.Modules.pushforward f).map
          (((godementTotalPlusUnit U).app
            ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).hom.f n))) ≫
      (cartesianOpenBaseChange a b f j h).hom.app
        (((godementTotalPlus U).obj
          ((Scheme.Modules.pullback f).mapCochainComplexPlus.obj K)).obj.X n) ≫
      (Scheme.Modules.pushforward b).map
        (((godementTotalPlusUnit W).app (restrictedTotalPlus a f K)).hom.f n) =
      ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app
        ((Scheme.Modules.restrictFunctor j).obj (K.obj.X n)) ≫
      (Scheme.Modules.pushforward b).map
        (((godementTotalPlusUnit W).app ((Scheme.Modules.pullback b).mapCochainComplexPlus.obj
          ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K))).hom.f n)) ≫
      (Scheme.Modules.pushforward b).map
        (((godementTotalPlus W).map (openTotalBridge a b f j h K)).hom.f n) := by
  have h₁ := open_component_first_square a b f j h K n
  have h₂ := open_component_second_square a b f j h K n
  have he := unit_span_pasting h₁ h₂
  exact he

end AlgebraicGeometry.Scheme.Modules.Godement
