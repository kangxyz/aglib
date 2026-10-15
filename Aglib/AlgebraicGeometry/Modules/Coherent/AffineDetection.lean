/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Restriction
/-! # Detecting zero coherent sheaves on affine charts

A coherent sheaf vanishes if its actual restrictions to all affine open
charts vanish. The proof uses the original stalks and restriction comparison.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- Zero coherent sheaves can be recognized on all actual affine charts. -/
theorem coherent_isZero_of_affineRestrictions {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : FiniteTypeSheaves X)
    (h : ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (a : Spec R ⟶ X)
      [IsOpenImmersion a], IsZero ((finiteTypeSheavesRestriction a).obj M)) : IsZero M := by
  apply IsZero.of_full_of_faithful_of_isZero (finiteTypeSheavesToModules X) M
  apply (Scheme.Modules.isZero_iff_stalks M.obj).mpr
  intro x
  obtain ⟨R, a, ha, y, hy⟩ := Scheme.exists_Spec_apply_eq x
  have : IsOpenImmersion a := ha
  have : IsNoetherianRing R := noetherian_affineChart R a
  have h' : IsZero ((restrictFunctor a).obj M.obj) :=
    (finiteTypeSheavesToModules (Spec R)).map_isZero (h R a)
  have hz := (Scheme.Modules.stalkFunctor (Spec R) y).map_isZero h'
  have hz' : IsZero ((Scheme.Modules.stalkFunctor X (a y)).obj M.obj) :=
    hz.of_iso ((restrictStalkNatIso a y).app M.obj).symm
  simpa only [hy] using hz'

end AlgebraicGeometry.Scheme.Modules.Coherent
