/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Monoidal.Grp

/-!
# The original comparison for fully faithful group transport

The construction uses native `GrpObj.ofIso` and `FullyFaithful.grpObj`.
The comparison retains the supplied isomorphism on both underlying arrows.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D]
  [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
  {F : C ⥤ D} [F.Monoidal]

set_option backward.isDefEq.respectTransparency false in
/-- The original isomorphism after the native fully faithful group transport. -/
def FullyFaithful.grpObjIso (hF : F.FullyFaithful) (X : C) (G : Grp D)
    (e : F.obj X ≅ G.X) :
    letI : GrpObj (F.obj X) := GrpObj.ofIso e.symm
    letI : GrpObj X := hF.grpObj X
    F.mapGrp.obj (Grp.mk X) ≅ G := by
  letI : GrpObj (F.obj X) := GrpObj.ofIso e.symm
  letI : GrpObj X := hF.grpObj X
  refine Grp.mkIso e ?_ ?_ <;> simp [MonObj.ofIso_one, MonObj.ofIso_mul]

@[simp]
theorem FullyFaithful.grpObjIso_hom_hom (hF : F.FullyFaithful) (X : C) (G : Grp D)
    (e : F.obj X ≅ G.X) : (hF.grpObjIso X G e).hom.hom.hom = e.hom := rfl

@[simp]
theorem FullyFaithful.grpObjIso_inv_hom (hF : F.FullyFaithful) (X : C) (G : Grp D)
    (e : F.obj X ≅ G.X) : (hF.grpObjIso X G e).inv.hom.hom = e.inv := rfl

end CategoryTheory.Functor
