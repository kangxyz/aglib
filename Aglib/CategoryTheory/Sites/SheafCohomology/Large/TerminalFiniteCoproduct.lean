/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.FiniteCoproduct
public import Aglib.CategoryTheory.Sites.Hypercohomology.Terminal

/-! # Global cohomology of a finite disjoint cover of the terminal object

The original constant integer source is the free representable of the
terminal object. Its actual source isomorphism, followed by the existing
finite represented-cohomology decomposition, avoids introducing an
inverse-image identity functor in this arbitrary-site comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.LargeCohomology

universe c h t e r

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max h t}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max h t})]
  {ι : Type r} [Fintype ι] {U : ι → C} {T : C}

/-- Original global cohomology decomposes over a supplied finite disjoint
section decomposition of the actual terminal object. -/
def terminalFiniteCoproductAddEquiv (hT : IsTerminal T) (f : ∀ i, U i ⟶ T)
    (hs : ∀ F : Sheaf J AddCommGrpCat.{max h t}, Function.Bijective
      (fun x : F.obj.obj (op T) => fun i => F.obj.map (f i).op x))
    (F : Sheaf J AddCommGrpCat.{max h t}) (q : ℕ) :
    Sheaf.H.{e} F q ≃+ ∀ i, H.{e} J F q (U i) := by
  let d := Sheaf.Hypercohomology.constantIntegerFreeTerminalIso J hT
  let e₀ : Sheaf.H.{e} F q ≃+ H.{e} J F q T :=
    (((extFunctor q).mapIso d.op).app F).symm.addCommGroupIsoToAddEquiv
  exact e₀.trans (finiteCoproductAddEquiv J T f hs F q)

end CategoryTheory.Sheaf.LargeCohomology
