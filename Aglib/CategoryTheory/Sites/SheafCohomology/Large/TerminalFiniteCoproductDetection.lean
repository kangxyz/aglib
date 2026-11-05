/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.TerminalFiniteCoproduct
public import Aglib.Algebra.Homology.DerivedCategory.Ext.FiniteCoproductDetection

/-! # Detection by the actual finite terminal-cover augmentations

The original global cohomology class is tested by the free-representable
component maps followed by the inverse original integer-source comparison.
No equality between an unspecified cohomology equivalence and restriction
maps is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory Limits CategoryTheory.Abelian Opposite
namespace CategoryTheory.Sheaf.LargeCohomology
open Hypercohomology
universe c h t e r
variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max h t}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max h t})]

/-- The original terminal-cover augmentation tests detect the unchanged
original class, using the genuine finite free-representable coproduct. -/
theorem eq_zero_of_terminalFiniteCoproduct_precomp
    {ι : Type r} [Finite ι] {U : ι → C} {T : C}
    (hT : IsTerminal T) (f : ∀ i, U i ⟶ T)
    (hs : ∀ F : Sheaf J AddCommGrpCat.{max h t}, Function.Bijective
      (fun x : F.obj.obj (op T) => fun i => F.obj.map (f i).op x))
    (F : Sheaf J AddCommGrpCat.{max h t}) (q : ℕ) (x : Sheaf.H.{e} F q)
    (hx : ∀ i, (Ext.mk₀ ((freeAbelianSheafFunctor J).map (f i) ≫
      (constantIntegerFreeTerminalIso J hT).inv)).comp x (Nat.zero_add q) = 0) :
    x = 0 := by
  let : Fintype ι := Fintype.ofFinite ι
  let E := constantIntegerFreeTerminalIso J hT
  let y : Ext (freeAbelianSheaf.{t} J T) F q := (Ext.mk₀ E.inv).comp x (Nat.zero_add q)
  have hy : y = 0 := by
    apply Ext.eq_zero_of_finite_cofan (fun i => freeAbelianSheaf.{t} J (U i))
      (freeRepresentableCofan J T f) (freeRepresentableCofanIsColimit J T f hs) F q y
    intro i
    change (Ext.mk₀ ((freeAbelianSheafFunctor J).map (f i))).comp
      ((Ext.mk₀ E.inv).comp x (Nat.zero_add q)) (Nat.zero_add q) = 0
    rw [Ext.mk₀_comp_mk₀_assoc]
    exact hx i
  have hz := congrArg (fun z : Ext (freeAbelianSheaf.{t} J T) F q =>
    (Ext.mk₀ E.hom).comp z (Nat.zero_add q)) hy
  simpa only [y, Ext.mk₀_comp_mk₀_assoc, E.hom_inv_id, Ext.mk₀_id_comp,
    Ext.comp_zero] using hz

end CategoryTheory.Sheaf.LargeCohomology
