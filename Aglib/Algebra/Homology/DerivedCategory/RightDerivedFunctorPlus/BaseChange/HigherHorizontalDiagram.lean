/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HigherHorizontalEdges

/-! # Independent path transports in the actual higher horizontal diagram -/

@[expose] public section
namespace CategoryTheory

/-- The original two-layer horizontal diagram, before imposing any equations. -/
structure HorizontalMappedDiagram
    (C D₁ D₂ A₁ A₂ : Type*)
    [Category* C] [Category* D₁] [Category* D₂] [Category* A₁] [Category* A₂] where
  /-- First layer functor in the comparison `γ`. -/
  H₁ : D₁ ⥤ A₁
  /-- Second layer functor in the comparison `γ`. -/
  H₂ : D₂ ⥤ A₂
  /-- Functor on the comparison targets `A₁` and `A₂`. -/
  G : A₁ ⥤ A₂
  /-- Functor relating the source categories `D₁` and `D₂`. -/
  DG : D₁ ⥤ D₂
  /-- Comparison isomorphism between `DG ⋙ H₂` and `H₁ ⋙ G`. -/
  γ : DG ⋙ H₂ ≅ H₁ ⋙ G
  /-- Functor assigning each object of `C` its original `D₁` object. -/
  R : C ⥤ D₁
  /-- Functor assigning each object of `C` its original `D₂` object. -/
  Q : C ⥤ D₂
  /-- Original natural map from `R ⋙ DG` to `Q`. -/
  β₂ : R ⋙ DG ⟶ Q
  /-- Base object where the input arrow and original comparison maps are evaluated. -/
  X : C
  /-- Base object identified with `X` by the specified isomorphism `p`. -/
  Y : C
  /-- Specified isomorphism from `Y` to `X`. -/
  p : Y ≅ X
  /-- Original `D₁` object at the source of `β₁`. -/
  U : D₁
  /-- Original arrow from `U` to `R.obj X`. -/
  β₁ : U ⟶ R.obj X
  /-- Initial `D₂` object for the route through `a` and `d`. -/
  A : D₂
  /-- Intermediate `D₂` object on the route from `A` to `Q.obj X`. -/
  T : D₂
  /-- Original arrow from `A` to `DG.obj U`. -/
  a : A ⟶ DG.obj U
  /-- Original comparison-path arrow from `A` to `T`. -/
  d : A ⟶ T
  /-- Final original arrow from `T` to `Q.obj X`. -/
  e : T ⟶ Q.obj X
  /-- Object in `A₁` compared with `H₁.obj U`. -/
  U' : A₁
  /-- Object in `A₁` used for the comparisons over `R.obj X` and `R.obj Y`. -/
  V' : A₁
  /-- Isomorphism from `U'` to `H₁.obj U`. -/
  iU : U' ≅ H₁.obj U
  /-- Isomorphism from `V'` to `H₁.obj (R.obj X)`. -/
  iV : V' ≅ H₁.obj (R.obj X)
  /-- Isomorphism from `V'` to `H₁.obj (R.obj Y)`. -/
  iE : V' ≅ H₁.obj (R.obj Y)
  /-- Isomorphism from `G.obj V'` to `H₂.obj (DG.obj (R.obj Y))`. -/
  iS : G.obj V' ≅ H₂.obj (DG.obj (R.obj Y))
  /-- Object in `A₂` used as the comparison target over `Q.obj Y`. -/
  W : A₂
  /-- Isomorphism from `W` to `H₂.obj (Q.obj Y)`. -/
  iW : W ≅ H₂.obj (Q.obj Y)
  /-- Actual `A₁` arrow from `U'` to `V'`. -/
  b₁ : U' ⟶ V'
  /-- Actual `A₂` arrow from `G.obj V'` to `W`. -/
  b₂ : G.obj V' ⟶ W
  /-- Object in `A₂` compared with `H₂.obj A`. -/
  A' : A₂
  /-- Object in `A₂` compared with `H₂.obj T`. -/
  T' : A₂
  /-- Isomorphism from `A'` to `H₂.obj A`. -/
  iA : A' ≅ H₂.obj A
  /-- Isomorphism from `T'` to `H₂.obj T`. -/
  iT : T' ≅ H₂.obj T
  /-- Comparison-route arrow from `A'` to `G.obj U'`. -/
  a' : A' ⟶ G.obj U'
  /-- Comparison-route arrow from `A'` to `T'. -/
  d' : A' ⟶ T'
  /-- Final comparison-route arrow from `T'` to `W`. -/
  e' : T' ⟶ W

namespace HorizontalMappedDiagram
variable {C D₁ D₂ A₁ A₂ : Type*}
  [Category* C] [Category* D₁] [Category* D₂] [Category* A₁] [Category* A₂]
  (δ : HorizontalMappedDiagram C D₁ D₂ A₁ A₂)

/-- The original derived pasting equation. -/
def DerivedPasting : Prop := δ.a ≫ δ.DG.map δ.β₁ ≫ δ.β₂.app δ.X = δ.d ≫ δ.e
/-- The native source comparison edge. -/
def SourceEdge : Prop :=
  δ.a' ≫ δ.G.map δ.iU.hom ≫ δ.γ.inv.app δ.U = δ.iA.hom ≫ δ.H₂.map δ.a
/-- The first actual higher exchange factor. -/
def FirstFactor : Prop := MappedTargetInverseEquation δ.H₁ δ.β₁ δ.iU δ.iV δ.b₁
/-- The second actual higher exchange factor. -/
def SecondFactor : Prop :=
  MappedTargetInverseEquation δ.H₂ (δ.β₂.app δ.Y) δ.iS δ.iW δ.b₂
/-- The original target comparison changes the single coefficient. -/
def MiddleTarget : Prop := δ.iV.hom = δ.iE.hom ≫ δ.H₁.map (δ.R.map δ.p.hom)
/-- The original source comparison factors through exact homology. -/
def MiddleSource : Prop := δ.iS.hom = δ.G.map δ.iE.hom ≫ δ.γ.inv.app (δ.R.obj δ.Y)
/-- The composite actual higher exchange factor. -/
def CompositeFactor : Prop := MappedTargetInverseEquation δ.H₂ δ.d δ.iA δ.iT δ.d'
/-- The native target comparison edge. -/
def TargetEdge : Prop :=
  δ.e' ≫ δ.iW.hom ≫ δ.H₂.map (δ.Q.map δ.p.hom) = δ.iT.hom ≫ δ.H₂.map δ.e

/-- Transport of the entire upper path, independently of derived pasting. -/
def LeftPathTransport : Prop :=
  (δ.a' ≫ δ.G.map δ.b₁ ≫ δ.b₂) ≫
      (δ.iW.hom ≫ δ.H₂.map (δ.Q.map δ.p.hom)) =
    δ.iA.hom ≫ δ.H₂.map (δ.a ≫ δ.DG.map δ.β₁ ≫ δ.β₂.app δ.X)

/-- Transport of the lower path, independently of derived pasting. -/
def RightPathTransport : Prop :=
  (δ.d' ≫ δ.e') ≫ (δ.iW.hom ≫ δ.H₂.map (δ.Q.map δ.p.hom)) =
    δ.iA.hom ≫ δ.H₂.map (δ.d ≫ δ.e)

/-- The literal actual-map equation. -/
def Equation : Prop := MappedHorizontalPastingEquation δ.G δ.a' δ.b₁ δ.b₂ δ.d' δ.e'

/-- Naturality supplies the middle coefficient edge and transports the upper path. -/
theorem leftPathTransport (ha : δ.SourceEdge) (hb₁ : δ.FirstFactor)
    (hb₂ : δ.SecondFactor) (ht : δ.MiddleTarget) (hs : δ.MiddleSource) :
    δ.LeftPathTransport := by
  have hm : δ.G.map δ.iV.hom ≫ δ.γ.inv.app (δ.R.obj δ.X) =
      δ.iS.hom ≫ δ.H₂.map (δ.DG.map (δ.R.map δ.p.hom)) := by
    have hn := δ.γ.inv.naturality (δ.R.map δ.p.hom)
    simp only [Functor.comp_map] at hn
    rw [show δ.iV.hom = _ from ht, δ.G.map_comp, Category.assoc, hn,
      show δ.iS.hom = _ from hs, Category.assoc]
  have hfirst := mapped_horizontal_pullback_edge δ.H₁ δ.H₂ δ.G δ.DG δ.γ
    δ.β₁ δ.iU δ.iV δ.b₁ hb₁
  have hsecond := mapped_horizontal_single_edge δ.H₂ δ.β₂ δ.p.hom
    δ.iS δ.iW δ.b₂ hb₂
  simp only [Functor.comp_map] at hsecond
  rw [← hm] at hsecond
  dsimp only [LeftPathTransport]
  rw [Category.assoc, Category.assoc, hsecond, ← Category.assoc (δ.G.map δ.b₁),
    hfirst, Category.assoc, ← Category.assoc δ.a', show δ.a' ≫ _ = _ from ha]
  simp only [Category.assoc, Functor.map_comp]

/-- The composite exchange and target comparison transport the lower path. -/
theorem rightPathTransport (hd : δ.CompositeFactor) (he : δ.TargetEdge) :
    δ.RightPathTransport := by
  dsimp only [RightPathTransport]
  rw [Category.assoc, show δ.e' ≫ _ ≫ _ = _ from he,
    ← Category.assoc, show δ.d' ≫ δ.iT.hom = _ from hd,
    Category.assoc, ← δ.H₂.map_comp]

/-- Compare the two independently transported paths using the original derived square. -/
theorem equation (hl : δ.LeftPathTransport) (hr : δ.RightPathTransport)
    (hp : δ.DerivedPasting) : δ.Equation := by
  let j := δ.iW ≪≫ δ.H₂.mapIso (δ.Q.mapIso δ.p)
  apply (cancel_mono j.hom).mp
  change (δ.a' ≫ δ.G.map δ.b₁ ≫ δ.b₂) ≫
      (δ.iW.hom ≫ δ.H₂.map (δ.Q.map δ.p.hom)) =
    (δ.d' ≫ δ.e') ≫ (δ.iW.hom ≫ δ.H₂.map (δ.Q.map δ.p.hom))
  exact hl.trans ((congrArg (fun z => δ.iA.hom ≫ δ.H₂.map z) hp).trans hr.symm)

/-- Read the original actual-map equation at the generic boundary. -/
theorem equation_eq (h : δ.Equation) : δ.a' ≫ δ.G.map δ.b₁ ≫ δ.b₂ = δ.d' ≫ δ.e' := h

end HorizontalMappedDiagram

end CategoryTheory
