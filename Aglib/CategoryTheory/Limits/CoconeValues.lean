/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-! # Values of actual colimit cocones

All points, legs, comparison isomorphisms and source maps are supplied actual
ones. Ordinary preserved-colimit zero detection needs no filteredness or
forgetful preservation. Element relations and eventual zero retain the actual
filtered forgetful-preservation hypothesis and independent worlds.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits.CoconeValues

universe uI vI uC vC uD vD e

section Ordinary

variable {I : Type uI} [Category.{vI} I]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- A preserved actual colimit of zero images has zero original image point.
No preservation of zero objects or exactness is assumed. -/
theorem isZero_obj_of_preservesColimit [HasZeroMorphisms D]
    (H : C ⥤ D) {F : I ⥤ C} {c : Cocone F} (hc : IsColimit c)
    [PreservesColimit F H] (hF : ∀ i, IsZero (H.obj (F.obj i))) :
    IsZero (H.obj c.pt) := by
  apply (IsZero.iff_id_eq_zero (H.obj c.pt)).mpr
  apply (isColimitOfPreserves H hc).hom_ext
  intro i
  exact (hF i).eq_of_src _ _

/-- Naturality of the same uniqueness isomorphisms follows from the two
original cocone-leg squares. No desired comparison square is supplied. -/
theorem coconePointUniqueUpToIso_naturality
    {F G : I ⥤ C} {c c' : Cocone F} {d d' : Cocone G}
    (hc : IsColimit c) (hc' : IsColimit c') (hd : IsColimit d) (hd' : IsColimit d')
    (a : ∀ i, F.obj i ⟶ G.obj i) (f : c.pt ⟶ d.pt) (g : c'.pt ⟶ d'.pt)
    (hf : ∀ i, c.ι.app i ≫ f = a i ≫ d.ι.app i)
    (hg : ∀ i, c'.ι.app i ≫ g = a i ≫ d'.ι.app i) :
    (hc.coconePointUniqueUpToIso hc').hom ≫ g =
      f ≫ (hd.coconePointUniqueUpToIso hd').hom := by
  apply hc.hom_ext
  intro i
  calc
    c.ι.app i ≫ ((hc.coconePointUniqueUpToIso hc').hom ≫ g) =
        c'.ι.app i ≫ g := by
      rw [← Category.assoc, hc.comp_coconePointUniqueUpToIso_hom hc' i]
    _ = a i ≫ d'.ι.app i := hg i
    _ = a i ≫ (d.ι.app i ≫ (hd.coconePointUniqueUpToIso hd').hom) :=
      congrArg (fun z => a i ≫ z) (hd.comp_coconePointUniqueUpToIso_hom hd' i).symm
    _ = (a i ≫ d.ι.app i) ≫ (hd.coconePointUniqueUpToIso hd').hom :=
      (Category.assoc _ _ _).symm
    _ = (c.ι.app i ≫ f) ≫ (hd.coconePointUniqueUpToIso hd').hom :=
      congrArg (fun z => z ≫ (hd.coconePointUniqueUpToIso hd').hom) (hf i).symm
    _ = c.ι.app i ≫ (f ≫ (hd.coconePointUniqueUpToIso hd').hom) :=
      Category.assoc _ _ _

end Ordinary

section Groups

variable {I : Type uI} [Category.{vI} I] (F : I ⥤ AddCommGrpCat.{e})
  [PreservesColimit F (forget AddCommGrpCat.{e})]
  {c : Cocone F} (hc : IsColimit c)

include hc in
/-- Every original point value comes from an original cocone leg. -/
theorem exists_rep (x : c.pt) : ∃ (i : I) (y : F.obj i), (c.ι.app i).hom y = x :=
  Concrete.isColimit_exists_rep F hc x

include hc in
/-- Equality at the original point is witnessed by two actual transitions. -/
theorem exists_relation [IsFiltered I] {i j : I} (x : F.obj i) (y : F.obj j)
    (h : (c.ι.app i).hom x = (c.ι.app j).hom y) :
    ∃ (k : I) (a : i ⟶ k) (b : j ⟶ k), (F.map a).hom x = (F.map b).hom y := by
  exact Concrete.isColimit_exists_of_rep_eq (C := AddCommGrpCat.{e})
    (FC := fun A B : AddCommGrpCat.{e} => A →+ B)
    (CC := fun A : AddCommGrpCat.{e} => (A : Type e))
    (D := c) (i := i) (j := j) F hc x y h

include hc in
/-- A stage value zero at the original point becomes zero at a genuine stage. -/
theorem exists_map_eq_zero [IsFiltered I] {i : I} (x : F.obj i)
    (hx : (c.ι.app i).hom x = 0) :
    ∃ (j : I) (a : i ⟶ j), (F.map a).hom x = 0 := by
  obtain ⟨j, a, b, hab⟩ := exists_relation F hc x (0 : F.obj i)
    (hx.trans (c.ι.app i).hom.map_zero.symm)
  exact ⟨j, a, hab.trans (F.map b).hom.map_zero⟩

include hc in
/-- A compatible original source cone with common composite sends an original
value zero at the colimit to zero at an original stage. -/
theorem exists_zero_of_cone [IsFiltered I] (b : Cone F) (l : b.pt ⟶ c.pt)
    (hl : ∀ i, b.π.app i ≫ c.ι.app i = l) (x : b.pt) (hx : l.hom x = 0) :
    ∃ i, (b.π.app i).hom x = 0 := by
  let i : I := Classical.choice (IsFiltered.nonempty : Nonempty I)
  have hi : (c.ι.app i).hom ((b.π.app i).hom x) = 0 := by
    change (b.π.app i ≫ c.ι.app i).hom x = 0
    rw [hl i]
    exact hx
  obtain ⟨j, a, ha⟩ := exists_map_eq_zero F hc ((b.π.app i).hom x) hi
  have hcone : (F.map a).hom ((b.π.app i).hom x) = (b.π.app j).hom x :=
    ConcreteCategory.congr_hom (b.w a) x
  exact ⟨j, hcone.symm.trans ha⟩

end Groups

end CategoryTheory.Limits.CoconeValues
