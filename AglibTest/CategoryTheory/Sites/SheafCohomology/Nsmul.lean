/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Nsmul

/-! Interface examples and approved-foundation guards for the shared provider. -/

@[expose] public section

open CategoryTheory

universe u v a w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{a}] [HasExt.{w} (Sheaf J AddCommGrpCat.{a})]

/-- Scheme, coefficient and Ext universes are not identified. -/
example (F : Sheaf J AddCommGrpCat.{a}) (q n : ℕ) (x : Sheaf.H.{w} F q) :
    Sheaf.H.map (n • 𝟙 F) q x = n • x :=
  Sheaf.H.map_nsmul_id_apply F q n x

/-- info: 'CategoryTheory.Sheaf.H.map_nsmul_id' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.H.map_nsmul_id

/-- info: 'CategoryTheory.Sheaf.H.map_nsmul_id_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.H.map_nsmul_id_apply
