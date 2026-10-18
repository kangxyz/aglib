/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.List.OfFn

/-!
# Actual matrices between two ordered generating lists

Membership in the original ideal supplies every row of a change-of-generators
matrix. Equality of the two finite lengths gives a square matrix. No
invertibility of that matrix is required by the canonical overlap theorem.
-/

@[expose] public section
noncomputable section

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Two equal-length ordered lists with the indicated ideal inclusion have an actual
square matrix expressing the second list in the first. -/
theorem exists_canonicalGeneratorMatrix {R : Type u} [CommRing R]
    (s t : List R) (hlen : s.length = t.length) (hI : Ideal.ofList t ≤ Ideal.ofList s) :
    ∃ M : Matrix (Fin s.length) (Fin s.length) R,
      t = List.ofFn (fun i => ∑ j, M i j * s.get j) := by
  classical
  have hs : {r : R | r ∈ s} = Set.range s.get := by
    ext r
    exact List.mem_iff_get
  have ht (i : Fin t.length) :
      t.get i ∈ Ideal.span (Set.range s.get) := by
    rw [← hs]
    exact hI (Ideal.subset_span (List.get_mem t i))
  choose rows hrows using fun i => Ideal.mem_span_range_iff_exists_fun.mp (ht i)
  let M : Matrix (Fin s.length) (Fin s.length) R :=
    fun i j => rows (Fin.cast hlen i) j
  refine ⟨M, ?_⟩
  calc
    t = List.ofFn t.get := (List.ofFn_get t).symm
    _ = List.ofFn (fun i : Fin t.length => ∑ j, rows i j * s.get j) :=
      congrArg List.ofFn (funext fun i => (hrows i).symm)
    _ = List.ofFn (fun i => ∑ j, M i j * s.get j) :=
      List.ofFn_congr hlen.symm _

end AlgebraicGeometry.Scheme.Modules
