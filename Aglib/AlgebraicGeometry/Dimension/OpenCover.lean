/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.Topology.KrullDimension

/-!
# Dimension bounded on an arbitrary open cover

Source: `R5Lab.Aglib.AlgebraicGeometry.Dimension.OpenCover`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `5e1cde0bb1016aa0bf4f4032ed13f0248cf22d87db3eaf94d9d54fd40ff03fb8`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Order
universe u v
namespace AlgebraicGeometry.Scheme

attribute [local instance] specializationOrder in
/-- An arbitrary uniform bound on the dimensions of an open cover bounds its scheme. -/
theorem topologicalKrullDim_le_of_openCover {X : Scheme.{u}}
    (𝒰 : Scheme.OpenCover.{v} X) (d : WithBot ℕ∞)
    (h : ∀ i, topologicalKrullDim (𝒰.X i) ≤ d) : topologicalKrullDim X ≤ d := by
  change krullDim (IrreducibleCloseds X) ≤ d
  rw [krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    krullDim_eq_iSup_coheight]
  refine iSup_le fun x => ?_
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  change (coheight ((𝒰.f i).base y) : WithBot ℕ∞) ≤ d
  rw [coheight_eq_of_isOpenImmersion]
  refine (coheight_le_krullDim y).trans ?_
  rw [← krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := 𝒰.X i))]
  exact h i


end AlgebraicGeometry.Scheme
