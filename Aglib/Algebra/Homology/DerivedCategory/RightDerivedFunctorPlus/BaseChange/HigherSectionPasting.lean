/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HigherHorizontalEdges
public import Mathlib.Algebra.Category.Grp.Basic

/-! # Original horizontal exchange pasting on actual sections

An original mapped horizontal-pasting equation and the actual section-unit
triangle combine two original section formulas. The original outer map and
coefficient transport stay opaque, avoiding geometric mate expansion.
-/

@[expose] public section

open CategoryTheory

universe v

namespace CategoryTheory

/-- Compose actual section formulas through the original mapped horizontal
pasting equation, retaining the original outer arrow and target transport. -/
theorem MappedHorizontalPastingEquation.section_apply
    {A B : Type*} [Category* A] [Category* B] (G : A ⥤ B)
    (ΓA : A ⥤ AddCommGrpCat.{v}) (ΓB : B ⥤ AddCommGrpCat.{v})
    (s : ΓA ⟶ G ⋙ ΓB)
    {U V : A} {P Q W : B} (a : P ⟶ G.obj U) (b : U ⟶ V)
    (c : G.obj V ⟶ W) (d : P ⟶ Q) (e : Q ⟶ W)
    (h : MappedHorizontalPastingEquation G a b c d e)
    {Z : AddCommGrpCat.{v}} (u : Z ⟶ ΓB.obj P) (t : Z ⟶ ΓA.obj U)
    (hu : u ≫ ΓB.map a = t ≫ s.app U)
    (x : Z) (y : ΓA.obj V) (z : ΓB.obj W)
    (hy : ΓA.map b (t x) = y) (hz : ΓB.map c (s.app V y) = z) :
    ΓB.map e (ΓB.map d (u x)) = z := by
  change a ≫ G.map b ≫ c = d ≫ e at h
  have hn := s.naturality b
  change ΓA.map b ≫ s.app V = s.app U ≫ ΓB.map (G.map b) at hn
  have hm : u ≫ ΓB.map d ≫ ΓB.map e =
      t ≫ ΓA.map b ≫ s.app V ≫ ΓB.map c := by
    calc
      _ = u ≫ ΓB.map (d ≫ e) := by rw [ΓB.map_comp]
      _ = u ≫ ΓB.map (a ≫ G.map b ≫ c) :=
        congrArg (fun k => u ≫ ΓB.map k) h.symm
      _ = (u ≫ ΓB.map a) ≫ ΓB.map (G.map b) ≫ ΓB.map c := by
        simp only [ΓB.map_comp, Category.assoc]
      _ = (t ≫ s.app U) ≫ ΓB.map (G.map b) ≫ ΓB.map c :=
        congrArg (fun k => k ≫ ΓB.map (G.map b) ≫ ΓB.map c) hu
      _ = t ≫ (s.app U ≫ ΓB.map (G.map b)) ≫ ΓB.map c := by
        simp only [Category.assoc]
      _ = t ≫ (ΓA.map b ≫ s.app V) ≫ ΓB.map c :=
        congrArg (fun k => t ≫ k ≫ ΓB.map c) hn.symm
      _ = _ := by rw [Category.assoc]
  have hv := ConcreteCategory.congr_hom hm x
  change ΓB.map e (ΓB.map d (u x)) =
    ΓB.map c (s.app V (ΓA.map b (t x))) at hv
  exact hv.trans ((congrArg (fun k => ΓB.map c (s.app V k)) hy).trans hz)

end CategoryTheory
