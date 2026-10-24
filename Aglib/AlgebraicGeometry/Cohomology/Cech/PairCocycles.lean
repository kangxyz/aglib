/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Sections

/-!
# Degree-one Čech cocycles of the structure sheaf on pairwise intersections

For a family of opens `U : ι → X.Opens` of a scheme `X`, a pair cochain is a section `b j l` of
the structure sheaf on every pairwise intersection `U j ⊓ U l`.

* `Scheme.pairCocycles U`: the pair cochains with `b j l + b l m = b j m` after restriction to
  every open contained in `U j`, `U l` and `U m`.
* `Scheme.pairCoboundary U`: the coboundary `(δ a) j l = a l - a j` of sections `a j` on the
  members of the family; its values are pair cocycles (`pairCoboundary_mem_pairCocycles`).
* `Scheme.PairCohomology U`: pair cocycles modulo coboundaries.

These are the degree-one Čech cocycles, coboundaries and cohomology of the structure sheaf,
written with the pairwise intersections `U j ⊓ U l` instead of the categorical products of
Mathlib's `CategoryTheory.cechComplexFunctor`; the comparison with that complex is a separate
leaf. No hypothesis on `X` or on the family is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible (sectionRestrict sectionRestrict_comp)

universe u v

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {ι : Type v} (U : ι → X.Opens)

/-- Pair cocycles: sections `b j l` on the pairwise intersections with `b j l + b l m = b j m`
after restriction to every open contained in `U j`, `U l` and `U m`. -/
def pairCocycles : AddSubgroup (∀ j l : ι, Γ(X, U j ⊓ U l)) where
  carrier b := ∀ (j l m : ι) (V : X.Opens) (hj : V ≤ U j) (hl : V ≤ U l) (hm : V ≤ U m),
    sectionRestrict X (le_inf hj hl) (b j l) + sectionRestrict X (le_inf hl hm) (b l m) =
      sectionRestrict X (le_inf hj hm) (b j m)
  zero_mem' := by
    intro j l m V hj hl hm
    simp only [Pi.zero_apply, map_zero, add_zero]
  add_mem' {b b'} hb hb' := by
    intro j l m V hj hl hm
    simp only [Pi.add_apply, map_add]
    rw [← hb j l m V hj hl hm, ← hb' j l m V hj hl hm]
    abel
  neg_mem' {b} hb := by
    intro j l m V hj hl hm
    simp only [Pi.neg_apply, map_neg]
    rw [← hb j l m V hj hl hm]
    abel

variable {U} in
theorem mem_pairCocycles_iff (b : ∀ j l : ι, Γ(X, U j ⊓ U l)) :
    b ∈ pairCocycles U ↔
      ∀ (j l m : ι) (V : X.Opens) (hj : V ≤ U j) (hl : V ≤ U l) (hm : V ≤ U m),
        sectionRestrict X (le_inf hj hl) (b j l) + sectionRestrict X (le_inf hl hm) (b l m) =
          sectionRestrict X (le_inf hj hm) (b j m) :=
  Iff.rfl

/-- The coboundary `(δ a) j l = a l - a j` of sections on the members of the family. -/
def pairCoboundary : (∀ j : ι, Γ(X, U j)) →+ (∀ j l : ι, Γ(X, U j ⊓ U l)) where
  toFun a j l := sectionRestrict X inf_le_right (a l) - sectionRestrict X inf_le_left (a j)
  map_zero' := by
    funext j l
    simp only [Pi.zero_apply, map_zero, sub_zero]
  map_add' a a' := by
    funext j l
    simp only [Pi.add_apply, map_add]
    abel

@[simp]
theorem pairCoboundary_apply (a : ∀ j : ι, Γ(X, U j)) (j l : ι) :
    pairCoboundary U a j l =
      sectionRestrict X inf_le_right (a l) - sectionRestrict X inf_le_left (a j) :=
  rfl

/-- Coboundaries are cocycles. -/
theorem pairCoboundary_mem_pairCocycles (a : ∀ j : ι, Γ(X, U j)) :
    pairCoboundary U a ∈ pairCocycles U := by
  intro j l m V hj hl hm
  simp only [pairCoboundary_apply, map_sub, sectionRestrict_comp]
  abel

/-- The coboundary map into the pair cocycles. -/
def pairCoboundaryToCocycles : (∀ j : ι, Γ(X, U j)) →+ pairCocycles U :=
  (pairCoboundary U).codRestrict (pairCocycles U) (pairCoboundary_mem_pairCocycles U)

@[simp]
theorem pairCoboundaryToCocycles_coe (a : ∀ j : ι, Γ(X, U j)) :
    (pairCoboundaryToCocycles U a : ∀ j l : ι, Γ(X, U j ⊓ U l)) = pairCoboundary U a :=
  rfl

/-- The pair coboundaries, as a subgroup of the pair cocycles. -/
def pairCoboundaries : AddSubgroup (pairCocycles U) :=
  (pairCoboundaryToCocycles U).range

/-- A pair cocycle is a coboundary if and only if it is `a l - a j` for sections `a j`. -/
theorem mem_pairCoboundaries_iff (b : pairCocycles U) :
    b ∈ pairCoboundaries U ↔ ∃ a : ∀ j : ι, Γ(X, U j), ∀ j l : ι,
      (b : ∀ j l : ι, Γ(X, U j ⊓ U l)) j l =
        sectionRestrict X inf_le_right (a l) - sectionRestrict X inf_le_left (a j) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, fun j l => rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext (funext fun j => funext fun l => (ha j l).symm)⟩

/-- Degree-one pair cohomology: pair cocycles modulo coboundaries. -/
abbrev PairCohomology : Type _ := pairCocycles U ⧸ pairCoboundaries U

end AlgebraicGeometry.Scheme
