/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Monoidal.Grp.Transport

/-! The native transported group comparison has the supplied original arrows. -/

@[expose] public section

open CategoryTheory

variable {C D : Type*} [Category C] [Category D]
  [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
  {F : C ⥤ D} [F.Monoidal] (hF : F.FullyFaithful) (X : C) (G : Grp D)
  (e : F.obj X ≅ G.X)

example : (hF.grpObjIso X G e).hom.hom.hom = e.hom := hF.grpObjIso_hom_hom X G e
example : (hF.grpObjIso X G e).inv.hom.hom = e.inv := hF.grpObjIso_inv_hom X G e
