/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.RingTheory.Smooth.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Reducedness of smooth schemes over fields

The actual affine section algebras of a smooth field scheme are reduced.
Their affine scheme presentations and the open-cover criterion give reducedness
of the whole scheme, without a relative-dimension or perfectness assumption.

Extraction source: `R5Lab.AlgebraicGeometry.Geometrically.SmoothIntegral`
at revision `95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, original lines 51–68.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable {F : Type u} [Field F] {X : Scheme.{u}}

/-- A scheme smooth over a field has a reduced structure sheaf. -/
lemma isReduced_of_smooth_over_field (f : X ⟶ Spec (.of F)) [Smooth f] : IsReduced X := by
  suffices ∀ i, IsReduced (X.affineCover.X i) from IsReduced.of_openCover X X.affineCover
  intro i
  let g := X.affineCover.f i ≫ f
  let φ := ((Scheme.ΓSpecIso (.of F)).inv ≫ g.appLE ⊤ ⊤ (by simp)).hom
  have hφ : φ.Smooth := by
    dsimp only [φ]
    rw [CommRingCat.hom_comp, RingHom.Smooth.respectsIso.cancel_left_isIso]
    exact g.smooth_appLE (isAffineOpen_top _) (isAffineOpen_top _) _
  let := φ.toAlgebra
  have : Algebra.Smooth F Γ(X.affineCover.X i, ⊤) := hφ
  have : _root_.IsReduced Γ(X.affineCover.X i, ⊤) :=
    Algebra.Smooth.smooth_isReduced F _
  exact isReduced_of_isAffine_isReduced _

end AlgebraicGeometry.Scheme
