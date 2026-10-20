/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Reducedness of radical closed subschemes

Source: `R5Lab.Aglib.AlgebraicGeometry.IdealSheaf.RadicalSubscheme`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `c03fa43da338713af806544349e095383d155c51dae21c4ccc4efc310f916dd6`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Reducedness of an arbitrary native subscheme whose affine ideals are radical. -/
theorem subscheme_reduced_of_radical {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : I.radical = I) : IsReduced I.subscheme := by
  let : ∀ U, IsReduced (I.subschemeCover.openCover.X U) := fun U => by
    have hr : (I.ideal U).IsRadical := by
      apply Ideal.radical_eq_iff.mp
      exact congrArg (fun J : X.IdealSheafData => J.ideal U) hI
    let := (Ideal.isRadical_iff_quotient_reduced _).mp hr
    exact inferInstanceAs (IsReduced (Spec (.of (Γ(X, (U : X.affineOpens).1) ⧸ I.ideal U))))
  exact IsReduced.of_openCover _ I.subschemeCover.openCover

end AlgebraicGeometry.Scheme.IdealSheafData
