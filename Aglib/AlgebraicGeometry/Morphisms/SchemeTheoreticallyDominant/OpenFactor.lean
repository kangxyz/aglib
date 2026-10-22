/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.OpenExtension
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Schematic dominance of a factor through an open immersion -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory
universe u

namespace AlgebraicGeometry

/-- Schematic dominance of a composite descends to its first factor when the
second factor is a quasi-compact open immersion. This uses the exact native
restriction of the pushed-forward kernel ideal, not topological density. -/
theorem IsSchemeTheoreticallyDominant.of_comp_left_of_isOpenImmersion
    {T D M : Scheme.{u}} (t : T ⟶ D) (d : D ⟶ M)
    [IsOpenImmersion d] [QuasiCompact d]
    [IsSchemeTheoreticallyDominant (t ≫ d)] : IsSchemeTheoreticallyDominant t := by
  constructor
  calc
    t.ker = (t.ker.map d).comap d :=
      (t.ker.comap_map_of_isOpenImmersion d).symm
    _ = ⊥ := by
      rw [← Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot,
        Scheme.IdealSheafData.comap_bot]

end AlgebraicGeometry
