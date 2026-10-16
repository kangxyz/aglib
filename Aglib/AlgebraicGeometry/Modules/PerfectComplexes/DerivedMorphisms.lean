/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalQuasiIsoLifting
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-!
# Local chain representatives for native derived morphisms

A derived morphism with strict perfect source has an actual chain
representative on a pointed open neighborhood. Native derived fractions
and the original local quasi-isomorphism lift retain the actual
restriction factorization and the chain homotopy equation.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/DerivedMorphisms.lean`.
Frozen dirty Quillen:
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `23964e63cdb44a65757340bc8ad3a8053d15161446d5d79167e813f98a069e75`.
Selected declaration ranges: 100–116.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Complex

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

variable {X : Scheme.{u}}

theorem exists_local_chain_representative {P L : CochainComplex X.Modules ℤ}
    (hP : strictPerfect X P)
    (φ : (DerivedCategory.Q (C := X.Modules)).obj P ⟶ (DerivedCategory.Q (C := X.Modules)).obj L)
      (x : X) :
    ∃ (Y : Scheme.{u}) (j : Y ⟶ X) (hj : IsOpenImmersion j) (y : Y), j y = x ∧
      ∃ g : (@restrict Y X j hj).obj P ⟶ (@restrict Y X j hj).obj L,
        @restrictDerivedHom X Y j hj P L φ = (DerivedCategory.Q (C := Y.Modules)).map g := by
  obtain ⟨M, f, s, hsIso, hφFac⟩ := DerivedCategory.left_fac (φ)
  let : IsIso ((DerivedCategory.Q (C := X.Modules)).map s) := hsIso
  have hs : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules s).1 hsIso
  let : QuasiIso s := hs
  have hφ : (φ) ≫ (DerivedCategory.Q (C := X.Modules)).map s =
      (DerivedCategory.Q (C := X.Modules)).map f := by
    rw [hφFac, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  let := hs
  obtain ⟨Y, j, hj, y, hy, g, ⟨h⟩⟩ := exists_local_quasiIso_lift hP s f x
  let := hj
  refine ⟨Y, j, hj, y, hy, g, ?_⟩
  apply (cancel_mono ((DerivedCategory.Q (C := Y.Modules)).map ((restrict j).map s))).1
  have hφ' := congrArg (restrictDerivedHom j) hφ
  rw [restrictDerivedHom_comp, restrictDerivedHom_map, restrictDerivedHom_map] at hφ'
  exact hφ'.trans ((DerivedCategory.Q_map_eq_of_homotopy Y.Modules h).trans
    ((DerivedCategory.Q (C := Y.Modules)).map_comp _ _))

end AlgebraicGeometry.Scheme.Modules.Complex
