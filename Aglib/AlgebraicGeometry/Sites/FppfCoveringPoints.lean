/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Sites.Pretopology
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Points of fppf covering sieves

A covering sieve of `Scheme.fppfTopology` contains, through every point, a flat morphism locally
of finite presentation (`Scheme.exists_flat_mem_range_of_mem_fppfTopology`, by induction on the
generation of the topology from `Scheme.fppfPrecoverage`), and likewise for
`Scheme.fppfTopology.over S` (`Scheme.exists_flat_mem_range_of_mem_fppfTopology_over`).
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- A covering sieve of the fppf topology contains, through every point, a flat morphism locally
of finite presentation. The proof is by induction on the generation of the topology from
`Scheme.fppfPrecoverage`. -/
theorem exists_flat_mem_range_of_mem_fppfTopology {Y : Scheme.{u}} {R : Sieve Y}
    (hR : R ∈ Scheme.fppfTopology Y) (y : Y) :
    ∃ (V : Scheme.{u}) (h : V ⟶ Y), R h ∧ Flat h ∧ LocallyOfFinitePresentation h ∧
      y ∈ Set.range h := by
  change Scheme.fppfPrecoverage.Saturate Y R at hR
  induction hR with
  | of Y S hS =>
    have hS' : S ∈ Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation) Y := hS
    obtain ⟨V, h, hh, hy⟩ :=
      (Presieve.mem_comap_jointlySurjectivePrecoverage_iff Scheme.forget).mp hS'.1 y
    have hP : (@Flat ⊓ @LocallyOfFinitePresentation) h := hS'.2 hh
    exact ⟨V, h, Sieve.le_generate S V h hh, hP.1, hP.2, hy⟩
  | top Y => exact ⟨Y, 𝟙 Y, trivial, inferInstance, inferInstance, y, rfl⟩
  | pullback X S _ Y f ih =>
    obtain ⟨V, h, hh, hflat, hlfp, v, hv⟩ := ih (f y)
    obtain ⟨q, -, hq⟩ := Scheme.Pullback.exists_preimage_pullback (f := h) (g := f) v y hv
    refine ⟨pullback h f, pullback.snd h f, ?_, inferInstance, inferInstance, q, hq⟩
    change S (pullback.snd h f ≫ f)
    rw [← pullback.condition]
    exact S.downward_closed hh _
  | transitive X S R _ _ ihS ihR =>
    obtain ⟨V, h, hh, hflat, hlfp, v, rfl⟩ := ihS y
    obtain ⟨W, k, hk, kflat, klfp, w, rfl⟩ := ihR hh v
    exact ⟨W, k ≫ h, hk, inferInstance, inferInstance, w, rfl⟩

/-- The version of `exists_flat_mem_range_of_mem_fppfTopology` for the fppf topology on `Over S`:
the morphism `h` is a morphism over `S` from `Over.mk (h ≫ T.hom)`. -/
theorem exists_flat_mem_range_of_mem_fppfTopology_over {S : Scheme.{u}} {T : Over S}
    {R : Sieve T} (hR : R ∈ (Scheme.fppfTopology.over S) T) (t : T.left) :
    ∃ (V : Scheme.{u}) (h : V ⟶ T.left), R (Over.homMk h : Over.mk (h ≫ T.hom) ⟶ T) ∧ Flat h ∧
      LocallyOfFinitePresentation h ∧ t ∈ Set.range h := by
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨V, h, hh, hflat, hlfp, ht⟩ := exists_flat_mem_range_of_mem_fppfTopology hR t
  rw [Sieve.overEquiv_iff] at hh
  exact ⟨V, h, hh, hflat, hlfp, ht⟩

end AlgebraicGeometry.Scheme
