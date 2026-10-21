/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Source-neighbourhood etaleness and unramifiedness

ONLY generic EtaleAt/UnramifiedAt and ordinary source-locality. Source0BMB61–82 and126–161
excluded; generic102–125 helpers reuse separate normal_curve_extension actual
normalization/generic map, do not duplicate that owner.

Source: `R5Lab.Aglib.AlgebraicGeometry.Morphisms.Etale.NormalizationCriteria`, frozen R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`5fcdd6f2046dd320493968db06a07ac2407429ce303101742063d2119b465a85`. Selected lines: [[28, 60]].
The actual objects, canonical maps, universes and stated premises are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom
universe u

/-- Etaleness on an actual open neighbourhood of the source point. -/
def etaleAt {Z X : Scheme.{u}} (f : Z ⟶ X) (z : Z) : Prop :=
  ∃ U : Z.Opens, z ∈ U ∧ Etale (U.ι ≫ f)

/-- Unramifiedness on an actual source neighbourhood; finite type is explicit. -/
def unramifiedAt {Z X : Scheme.{u}} (f : Z ⟶ X) (z : Z) : Prop :=
  ∃ U : Z.Opens, z ∈ U ∧ LocallyOfFiniteType (U.ι ≫ f) ∧ FormallyUnramified (U.ι ≫ f)

theorem etaleAt.unramified {Z X : Scheme.{u}} {f : Z ⟶ X} {z : Z}
    (h : etaleAt f z) : unramifiedAt f z := by
  obtain ⟨U, hz, hU⟩ := h
  let := hU
  exact ⟨U, hz, inferInstance, inferInstance⟩

theorem etale_of_forall_etaleAt {Z X : Scheme.{u}} (f : Z ⟶ X)
    (h : ∀ z, etaleAt f z) : Etale f := by
  choose U hz hU using h
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale) U
  · apply top_le_iff.mp
    intro z _
    exact (le_iSup U z) (hz z)
  · exact hU

end AlgebraicGeometry.Scheme.Hom
