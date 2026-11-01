/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties

/-! # An integral affine open of a reduced Noetherian scheme

The original irreducible-component proof constructs an actual nonempty affine
open. Its source scheme is unchanged; no chosen integral model is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

theorem exists_integral_affine_open_of_noetherian_reduced (X : Scheme.{u})
    [IsNoetherian X] [IsReduced X] [Nonempty X] :
    ∃ V : X.Opens, IsAffineOpen V ∧ Nonempty V.toScheme ∧ IsIntegral V.toScheme := by
  let x : X := Classical.choice inferInstance
  obtain ⟨O, hO, ⟨y, hy⟩, hOsub⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x)
  obtain ⟨V, hV, hyV, hVO⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⟨O, hO⟩) hy
  have hVirr : IsIrreducible (V : Set X) :=
    ⟨⟨y, hyV⟩, (irreducibleComponent_mem_irreducibleComponents x).1.2.open_subset
      V.isOpen (hVO.trans hOsub)⟩
  have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace hVirr
  exact ⟨V, hV, ⟨⟨y, hyV⟩⟩, isIntegral_of_irreducibleSpace_of_isReduced _⟩

end AlgebraicGeometry.Scheme
