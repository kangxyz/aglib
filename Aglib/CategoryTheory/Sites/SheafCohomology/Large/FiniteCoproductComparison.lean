/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.FiniteCoproduct

/-! # Original finite represented-cohomology decomposition with endpoint comparisons

Compose the actual finite-coproduct Ext decomposition with given original
endpoint comparisons over variable sites and coefficients. All carrier and
Ext universes remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf.LargeCohomology

/-- Compose the whole additive comparison before projecting concrete equivalences. -/
def assembleFiniteComparison {A B : Type*} {ι : Type*}
    {C D : ι → Type*} [AddCommGroup A] [AddCommGroup B]
    [∀ i, AddCommGroup (C i)] [∀ i, AddCommGroup (D i)]
    (e₀ : B ≃+ A) (e₁ : B ≃+ ∀ i, C i) (e₂ : ∀ i, C i ≃+ D i) :
    A ≃+ ∀ i, D i :=
  e₀.symm.trans (e₁.trans (AddEquiv.piCongrRight e₂))

/-- Build the complete represented-cohomology decomposition at the original
variable site and coefficient, before roots or scheme charts are supplied. -/
def representedFiniteComparison.{c, h, t, e, r, a, b}
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max h t}]
    [HasExt.{e} (Sheaf J AddCommGrpCat.{max h t})]
    {ι : Type r} [Fintype ι] {U : ι → C} (V : C) (f : ∀ i, U i ⟶ V)
    (hs : ∀ F : Sheaf J AddCommGrpCat.{max h t}, Function.Bijective
      (fun x : F.obj.obj (Opposite.op V) => fun i => F.obj.map (f i).op x))
    (F : Sheaf J AddCommGrpCat.{max h t}) (q : ℕ)
    {A : Type a} {B : ι → Type b} [AddCommGroup A] [∀ i, AddCommGroup (B i)]
    (e₀ : Sheaf.LargeCohomology.H.{e, t, h, c} J F q V ≃+ A)
    (e₂ : ∀ i, Sheaf.LargeCohomology.H.{e, t, h, c} J F q (U i) ≃+ B i) :
    A ≃+ ∀ i, B i :=
  assembleFiniteComparison e₀
    (Sheaf.LargeCohomology.finiteCoproductAddEquiv.{c, h, t, e, r} J V f hs F q) e₂

end CategoryTheory.Sheaf.LargeCohomology
