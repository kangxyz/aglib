/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.RingTheory.MvPolynomial.CoordinateGrading
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.BigOperators.Pi

/-!
# The original Laurent tuple cosimplicial module

Degree `p` consists of the original degree-`d` coordinate Laurent modules,
one for each tuple `a : Fin (p + 1) → ι`. Its maps are the original coordinate
restriction maps for the actual inclusions of tuple images. The complex is
the native alternating coface-map complex and retains all tuples in all
degrees. No finite-cover normalization or bounded replacement is introduced.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u v

namespace MvPolynomial

variable {ι : Type v} {m n p : ℕ}

/-- The actual finite image of a tuple of coordinate indices. -/
def coordinateTupleSet (a : Fin (n + 1) → ι) : Finset ι := by
  classical
  exact Finset.univ.image a

@[simp]
theorem mem_coordinateTupleSet (a : Fin (n + 1) → ι) (i : ι) :
    i ∈ coordinateTupleSet a ↔ i ∈ Set.range a := by
  classical
  simp [coordinateTupleSet]

/-- Precomposing tuple positions gives the actual inclusion of coordinate images. -/
theorem coordinateTupleSet_comp_subset (a : Fin (n + 1) → ι)
    (f : Fin (m + 1) → Fin (n + 1)) : coordinateTupleSet (a ∘ f) ⊆ coordinateTupleSet a := by
  intro i hi
  rw [mem_coordinateTupleSet] at hi ⊢
  obtain ⟨k, hk⟩ := hi
  exact ⟨f k, hk⟩

variable (R : Type u) [CommRing R]

/-- The actual tuple Laurent cochains in a specified integer degree. -/
abbrev coordinateLaurentTupleCochains (d : ℤ) (n : ℕ) :=
  ∀ a : Fin (n + 1) → ι, coordinateGrading R (coordinateTupleSet a) d

theorem coordinateLaurentDegreeMap_refl (s : Finset ι) (d : ℤ) :
    coordinateLaurentDegreeMap R (Finset.Subset.refl s) d = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact AlgHom.congr_fun (coordinateLaurentMap_refl R s) x.val

theorem coordinateLaurentDegreeMap_comp {s t v : Finset ι} (h : s ⊆ t) (k : t ⊆ v) (d : ℤ) :
    (coordinateLaurentDegreeMap R k d).comp (coordinateLaurentDegreeMap R h d) =
      coordinateLaurentDegreeMap R (h.trans k) d := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact AlgHom.congr_fun (coordinateLaurentMap_comp R h k) x.val

/-- The original scalar-linear Laurent restriction on a map of tuple positions. -/
def coordinateLaurentTuplePositionMap (d : ℤ) (f : Fin (m + 1) → Fin (n + 1)) :
    coordinateLaurentTupleCochains (ι := ι) R d m →ₗ[R]
      coordinateLaurentTupleCochains (ι := ι) R d n where
  toFun x a := coordinateLaurentDegreeMap R (coordinateTupleSet_comp_subset a f) d (x (a ∘ f))
  map_add' x y := by
    funext a
    exact (coordinateLaurentDegreeMap R (coordinateTupleSet_comp_subset a f) d).map_add
      (x (a ∘ f)) (y (a ∘ f))
  map_smul' r x := by
    funext a
    exact (coordinateLaurentDegreeMap R (coordinateTupleSet_comp_subset a f) d).map_smul
      r (x (a ∘ f))

@[simp]
theorem coordinateLaurentTuplePositionMap_id (d : ℤ) :
    coordinateLaurentTuplePositionMap (ι := ι) R d (id : Fin (n + 1) → _) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext a
  exact LinearMap.congr_fun (coordinateLaurentDegreeMap_refl R (coordinateTupleSet a) d) (x a)

@[simp]
theorem coordinateLaurentTuplePositionMap_comp (d : ℤ)
    (f : Fin (m + 1) → Fin (n + 1)) (g : Fin (n + 1) → Fin (p + 1)) :
    (coordinateLaurentTuplePositionMap (ι := ι) R d g).comp
        (coordinateLaurentTuplePositionMap R d f) =
      coordinateLaurentTuplePositionMap R d (g ∘ f) := by
  apply LinearMap.ext
  intro x
  funext a
  exact LinearMap.congr_fun
    (coordinateLaurentDegreeMap_comp R (coordinateTupleSet_comp_subset (a ∘ g) f)
      (coordinateTupleSet_comp_subset a g) d) (x ((a ∘ g) ∘ f))

/-- The sole original Laurent tuple cosimplicial module, with native coordinate
restrictions and no ordering restriction on the tuples. -/
def coordinateLaurentTupleCosimplicial (d : ℤ) :
    CosimplicialObject (ModuleCat.{max u v} R) where
  obj n := ModuleCat.of R (coordinateLaurentTupleCochains (ι := ι) R d n.len)
  map f := ModuleCat.ofHom (coordinateLaurentTuplePositionMap R d f.toOrderHom)
  map_id n := by
    apply ModuleCat.hom_ext
    exact coordinateLaurentTuplePositionMap_id R d
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact (coordinateLaurentTuplePositionMap_comp R d f.toOrderHom g.toOrderHom).symm

/-- The original unbounded full-tuple Laurent complex, using Mathlib's native
alternating coface-map construction. -/
def coordinateLaurentTupleComplex (d : ℤ) : CochainComplex (ModuleCat.{max u v} R) ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).obj
    (coordinateLaurentTupleCosimplicial (ι := ι) R d)

@[simp]
theorem coordinateLaurentTupleComplex_X (d : ℤ) (n : ℕ) :
    (coordinateLaurentTupleComplex (ι := ι) R d).X n =
      ModuleCat.of R (coordinateLaurentTupleCochains (ι := ι) R d n) := rfl

/-- The literal signed deletion differential, retaining the actual graded
Laurent restriction along every deleted tuple coordinate. -/
theorem coordinateLaurentTupleComplex_d_apply (d : ℤ)
    (x : coordinateLaurentTupleCochains (ι := ι) R d n) (a : Fin (n + 2) → ι) :
    (coordinateLaurentTupleComplex (ι := ι) R d).d n (n + 1) x a =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        coordinateLaurentDegreeMap R (coordinateTupleSet_comp_subset a j.succAbove) d
          (x (a ∘ j.succAbove)) := by
  simp only [coordinateLaurentTupleComplex, AlgebraicTopology.alternatingCofaceMapComplex_obj,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD, ModuleCat.hom_sum,
    ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
  change (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
    (fun b : Fin (n + 2) → ι =>
      coordinateLaurentDegreeMap R (coordinateTupleSet_comp_subset b j.succAbove) d
        (x (b ∘ j.succAbove)))) a = _
  simp only [Finset.sum_apply, Pi.smul_apply]

end MvPolynomial
