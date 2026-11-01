/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# An original localization as a colimit of principal localizations

The index consists of finite subsets of the original denominator submonoid.
Every stage is the native localization away from their product. The cocone
vertex is the supplied localization, not a newly constructed colimit ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace IsLocalization.PrincipalDiagram

universe u

variable {R : Type u} [CommRing R] (M : Submonoid R)

/-- The product of a finite family of allowed denominators. -/
def denominator (s : Finset M) : R := s.prod fun x => (x : R)

/-- Every stage denominator belongs to the original submonoid. -/
theorem denominator_mem (s : Finset M) : denominator M s ∈ M :=
  M.prod_mem fun x _ => x.property

/-- The actual principal localization at a finite stage. -/
abbrev stage (s : Finset M) := Localization.Away (denominator M s)

/-- The canonical map associated with inclusion of denominator families. -/
def transition {s t : Finset M} (h : s ⊆ t) : stage M s →+* stage M t :=
  IsLocalization.Away.lift (denominator M s)
    (IsLocalization.Away.isUnit_of_dvd (denominator M t)
      (Finset.prod_dvd_prod_of_subset s t (fun x => (x : R)) h))

@[simp]
theorem transition_algebraMap {s t : Finset M} (h : s ⊆ t) (r : R) :
    transition M h (algebraMap R (stage M s) r) = algebraMap R (stage M t) r :=
  IsLocalization.Away.lift_eq _ _ _

/-- The filtered diagram of genuine principal localization rings. -/
def ringDiagram : Finset M ⥤ CommRingCat.{u} where
  obj s := .of (stage M s)
  map f := CommRingCat.ofHom (transition M (leOfHom f))
  map_id s := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers (denominator M s))
    ext r
    simp
  map_comp {s t v} f g := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers (denominator M s))
    ext r
    simp

variable (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S]

/-- The original localization receives each principal stage by its universal map. -/
def projection (s : Finset M) : stage M s →+* S :=
  IsLocalization.Away.lift (denominator M s)
    (IsLocalization.map_units S ⟨denominator M s, denominator_mem M s⟩)

@[simp]
theorem projection_algebraMap (s : Finset M) (r : R) :
    projection M S s (algebraMap R (stage M s) r) = algebraMap R S r :=
  IsLocalization.Away.lift_eq _ _ _

/-- The cocone has the supplied original localization as its literal vertex. -/
def ringCocone : Cocone (ringDiagram M) where
  pt := .of S
  ι :=
    { app s := CommRingCat.ofHom (projection M S s)
      naturality s t f := by
        apply CommRingCat.hom_ext
        change (projection M S t).comp (transition M (leOfHom f)) = projection M S s
        apply IsLocalization.ringHom_ext (Submonoid.powers (denominator M s))
        ext r
        simp }

variable {S}

/-- The coefficient map of an arbitrary cocone, read at the empty stage. -/
def coconeBase (c : Cocone (ringDiagram M)) : R →+* c.pt :=
  (c.ι.app ∅).hom.comp (algebraMap R (stage M ∅))

/-- Every leg of a cocone has the same original coefficient map. -/
theorem coconeBase_eq (c : Cocone (ringDiagram M)) (s : Finset M) :
    coconeBase M c = (c.ι.app s).hom.comp (algebraMap R (stage M s)) := by
  ext r
  have h := congrArg (fun f => f.hom (algebraMap R (stage M ∅) r))
    (c.w (homOfLE (Finset.empty_subset s)))
  simpa [coconeBase, ringDiagram] using h.symm

/-- Each original denominator becomes a unit under a cocone's coefficient map. -/
theorem coconeBase_isUnit (c : Cocone (ringDiagram M)) (s : M) :
    IsUnit (coconeBase M c s) := by
  classical
  rw [coconeBase_eq M c {s}]
  change IsUnit ((c.ι.app {s}).hom (algebraMap R (stage M {s}) (s : R)))
  apply IsUnit.map
  simpa [denominator] using
    (IsLocalization.Away.algebraMap_isUnit (S := stage M {s}) (denominator M {s}))

variable (S)

/-- The supplied localization satisfies the colimit universal property. -/
def ringCoconeIsColimit : IsColimit (ringCocone M S) where
  desc c := CommRingCat.ofHom (IsLocalization.lift (S := S) (coconeBase_isUnit M c))
  fac c s := by
    apply CommRingCat.hom_ext
    change (IsLocalization.lift (S := S) (coconeBase_isUnit M c)).comp
      (projection M S s) = (c.ι.app s).hom
    apply IsLocalization.ringHom_ext (Submonoid.powers (denominator M s))
    ext r
    change IsLocalization.lift (coconeBase_isUnit M c)
      (projection M S s (algebraMap R (stage M s) r)) =
      (c.ι.app s).hom (algebraMap R (stage M s) r)
    rw [projection_algebraMap, IsLocalization.lift_eq, coconeBase_eq]
    rfl
  uniq c m hm := by
    apply CommRingCat.hom_ext
    change m.hom = IsLocalization.lift (S := S) (coconeBase_isUnit M c)
    apply IsLocalization.ringHom_ext (S := S) M
    ext r
    change m.hom (algebraMap R S r) =
      IsLocalization.lift (S := S) (coconeBase_isUnit M c) (algebraMap R S r)
    rw [IsLocalization.lift_eq]
    have h := congrArg (fun f => f.hom (algebraMap R (stage M ∅) r)) (hm ∅)
    change m.hom (projection M S ∅ (algebraMap R (stage M ∅) r)) =
      (c.ι.app ∅).hom (algebraMap R (stage M ∅) r) at h
    rw [projection_algebraMap] at h
    exact h

end IsLocalization.PrincipalDiagram
