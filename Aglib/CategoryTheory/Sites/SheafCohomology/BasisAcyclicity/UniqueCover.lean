/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.AlgebraicTopology.CechNerve

/-! # Unique-index covers and the original single-object nerve

For a unique indexing type the family Čech cosimplicial object is the actual
product nerve of the covering object. No coproduct distribution or preservation
of coefficient products is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.Cech

universe c h a b w

variable {C : Type c} [Category.{h} C] [HasFiniteProducts C]
  {A : Type a} [Category.{b} A] [HasProducts.{w} A]
  (ι : Type w) [Unique ι] (Z : C) (P : Cᵒᵖ ⥤ A)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Collapse the actual family-index product using its unique projection,
retaining every original simplex map. -/
def uniqueCoverCosimplicialIso :
    (FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.mk _ (fun _ : ι => Z)).cech).obj P ≅
        (cechNerveTerminalFrom Z).rightOp ⋙ P := by
  refine NatIso.ofComponents (fun n => productUniqueIso
    (fun _ : Fin (n.len + 1) → ι => P.obj (op (∏ᶜ fun _ : Fin (n.len + 1) => Z)))) ?_
  intro n m f
  let Q (k : ℕ) := P.obj (op (∏ᶜ fun _ : Fin (k + 1) => Z))
  let p : (∏ᶜ fun _ : Fin (m.len + 1) => Z) ⟶
      ∏ᶜ fun _ : Fin (n.len + 1) => Z :=
    Pi.lift fun k => Pi.π (fun _ : Fin (m.len + 1) => Z) (f.toOrderHom k)
  change (Pi.lift (fun a : Fin (m.len + 1) → ι =>
    Pi.π (fun _ : Fin (n.len + 1) → ι => Q n.len) (a ∘ f.toOrderHom) ≫ P.map p.op)) ≫
      Pi.π (fun _ : Fin (m.len + 1) → ι => Q m.len) default =
    Pi.π (fun _ : Fin (n.len + 1) → ι => Q n.len) default ≫ P.map p.op
  rw [Pi.lift_comp_π]
  rfl

variable [Preadditive A]

/-- The native family complex of a unique cover equals the original alternating
complex of its single covering object. -/
def uniqueCoverComplexIso :
    (cechComplexFunctor (fun _ : ι => Z)).obj P ≅
      (AlgebraicTopology.alternatingCofaceMapComplex A).obj
        ((cechNerveTerminalFrom Z).rightOp ⋙ P) :=
  (AlgebraicTopology.alternatingCofaceMapComplex A).mapIso
    (uniqueCoverCosimplicialIso ι Z P)

end CategoryTheory.Cech
