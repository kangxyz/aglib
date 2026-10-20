/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Reduced closed unions and their ideal sheaves

Source: `R5Lab.Aglib.AlgebraicGeometry.IdealSheaf.ReducedClosedUnion`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `632b00cb119a80486ce246cf44cb151a13c45b2b3e7cc4ecd22c38af56433505`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.IdealSheafData
open Scheme.IdealSheafData

/-- Kernels with a reduced source are radical, section by section. -/
theorem kernel_radical {X Y : Scheme.{u}} [IsReduced Y]
    (f : Y ⟶ X) [QuasiCompact f] : f.ker.radical = f.ker := by
  ext U : 2
  change (f.ker.ideal U).radical = f.ker.ideal U
  rw [Scheme.Hom.ker_apply]
  apply Ideal.radical_eq_iff.mpr
  rw [RingHom.ker_eq_comap_bot]
  exact Ideal.isRadical_bot.comap _

/-- The actual reduced closed image is determined by its topological support. -/
theorem kernel_eq_vanishingIdeal {X Y : Scheme.{u}} [IsReduced Y]
    (f : Y ⟶ X) [QuasiCompact f] : f.ker = vanishingIdeal f.ker.support := by
  rw [vanishingIdeal_support, kernel_radical]

/-- Set-theoretic coverage determines the scheme-theoretic union when all
three closed subschemes are reduced. No Cartier or model premise is used. -/
theorem reduced_closed_union_ideal {X Y C D : Scheme.{u}}
    [IsReduced Y] [IsReduced C] [IsReduced D]
    (f : Y ⟶ X) (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion f] [IsClosedImmersion i] [IsClosedImmersion j]
    (hcover : Set.range i ∪ Set.range j = Set.range f) :
    f.ker = i.ker ⊓ j.ker := by
  have hs : f.ker.support = i.ker.support ⊔ j.ker.support := by
    ext x
    change x ∈ (f.ker.support : Set X) ↔
      x ∈ (i.ker.support : Set X) ∪ (j.ker.support : Set X)
    simp only [Scheme.Hom.support_ker,
      f.isClosedEmbedding.isClosed_range.closure_eq,
      i.isClosedEmbedding.isClosed_range.closure_eq,
      j.isClosedEmbedding.isClosed_range.closure_eq]
    exact (Set.ext_iff.mp hcover x).symm
  rw [kernel_eq_vanishingIdeal f, hs, vanishingIdeal_sup,
    ← kernel_eq_vanishingIdeal i, ← kernel_eq_vanishingIdeal j]


end AlgebraicGeometry.Scheme.IdealSheafData
