/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.StandardEtaleChart
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Regular stalks under a smooth morphism

The original standard-smooth affine charts give etale polynomial coordinates.
Regularity of the actual target section rings and their polynomial rings then
passes through the original etale stalk maps. Local Noetherianity of the target
remains explicit; it is not inferred from pointwise regularity.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- A smooth morphism over a locally Noetherian scheme with regular stalks
has regular original source stalks, with no relative-dimension bound. -/
theorem regularStalks_of_smooth {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Smooth f] [IsLocallyNoetherian Y]
    (hY : RegularStalks Y) : RegularStalks X := by
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := Smooth.exists_isStandardSmooth f x
  let A := Γ(Y, U)
  let : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : IsRegularRing A := hY.isRegularRing_sections hU
  obtain ⟨n, g, _, hg⟩ := hf.exists_etale_mvPolynomial
  let c := Spec.map (CommRingCat.ofHom g)
  let : Etale c := HasRingHomProperty.Spec_iff.mpr hg
  let q := hV.isoSpec.hom ⟨x, hx⟩
  have hxq : hV.fromSpec q = x := by
    change (hV.isoSpec.hom ≫ hV.fromSpec) ⟨x, hx⟩ = x
    rw [hV.isoSpec_hom_fromSpec]
    rfl
  let : IsRegularLocalRing
      ((Spec (.of (MvPolynomial (Fin n) A))).presheaf.stalk (c q)) :=
    regularStalks_spec (MvPolynomial (Fin n) A) _
  let : IsRegularLocalRing ((Spec Γ(X, V)).presheaf.stalk q) :=
    isRegularLocalRing_stalk_of_etale c q
  let i := (asIso (hV.fromSpec.stalkMap q)).commRingCatIsoToRingEquiv
  have hr : IsRegularLocalRing (X.presheaf.stalk (hV.fromSpec q)) :=
    IsRegularLocalRing.of_ringEquiv i.symm
  exact hxq ▸ hr

end AlgebraicGeometry.Scheme
