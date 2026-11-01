/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.RepresentedTransfer.LocalFormula

/-! Original product-fan interfaces and approved-axiom guards. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MorphismProperty.Over

universe c h
variable {C : Type c} [Category.{h} C] [HasPullbacks C]
  (P : MorphismProperty C) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
  {X : C} {V U : P.Over ⊤ X} (f : V ⟶ U)

/-- The graph uses the existing selected pullback product, without HasBinaryProducts. -/
example : productGraph P f ≫ productFst P U V = 𝟙 V := productGraph_fst P f

/-- The whole graph construction retains its actual second projection. -/
example : productGraph P f ≫ productSnd P U V = f := productGraph_snd P f

/-- info: 'CategoryTheory.MorphismProperty.Over.productGraph_diagonal_map_symmetry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.MorphismProperty.Over.productGraph_diagonal_map_symmetry

/-- info: 'CategoryTheory.Sheaf.Hypercohomology.representedSectionsMap_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.Hypercohomology.representedSectionsMap_comp

/-- info: 'CategoryTheory.Sheaf.Hypercohomology.representedSectionsMap_local' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.Hypercohomology.representedSectionsMap_local

/-- info: 'CategoryTheory.Sheaf.Hypercohomology.representedRestrictionTrace_local' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.Hypercohomology.representedRestrictionTrace_local
