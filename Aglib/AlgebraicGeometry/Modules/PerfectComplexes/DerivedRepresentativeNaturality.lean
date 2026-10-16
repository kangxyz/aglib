/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedMorphisms
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.LiftedHom

/-!
# Local chain representatives for every supplied derived lift

The same local chain representative works for every supplied derived
functor and factorization realizing actual open restriction. The statement
retains the factorization as data and does not identify different chosen
lifts by an unstated equality.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/DerivedRepresentativeNaturality.lean`.
Frozen dirty Quillen:
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `371fd87889a354c81f42b4fe21c57fa3e4046c84df2cf2b069b73ed02d181184`.
Selected declaration ranges: 71–90.
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

theorem exists_local_chain_representative_any_lift {P L : CochainComplex X.Modules ℤ}
    (hP : strictPerfect X P)
    (φ : (DerivedCategory.Q (C := X.Modules)).obj P ⟶ (DerivedCategory.Q (C := X.Modules)).obj L)
      (x : X) :
    ∃ (Y : Scheme.{u}) (j : Y ⟶ X) (hj : IsOpenImmersion j) (y : Y), j y = x ∧
      ∃ g : (@restrict Y X j hj).obj P ⟶ (@restrict Y X j hj).obj L,
        ∀ (F : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules)
          (e : DerivedCategory.Q (C := X.Modules) ⋙ F ≅ @restrict Y X j hj ⋙ DerivedCategory.Q
            (C := Y.Modules)),
            liftedDerivedHom e φ = (DerivedCategory.Q (C := Y.Modules)).map g := by
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
  refine ⟨Y, j, hj, y, hy, g, fun F e ↦ ?_⟩
  apply (cancel_mono ((DerivedCategory.Q (C := Y.Modules)).map ((restrict j).map s))).1
  have hφ' := congrArg (liftedDerivedHom e) hφ
  rw [liftedDerivedHom_comp, liftedDerivedHom_map, liftedDerivedHom_map] at hφ'
  exact hφ'.trans ((DerivedCategory.Q_map_eq_of_homotopy Y.Modules h).trans
    ((DerivedCategory.Q (C := Y.Modules)).map_comp _ _))

end AlgebraicGeometry.Scheme.Modules.Complex
