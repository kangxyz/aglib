/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.Prod
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed subschemes of the spectrum of two fields

Source: `R5Lab.Aglib.AlgebraicGeometry.IdealSheaf.TwoPointSubscheme`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `b43ffbcac15fa4eb2f8c81f23e5496bc052ad9845f9c270f99cf5192ded4482a`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u v


namespace AlgebraicGeometry.Scheme.TwoPoint

/-- Every ideal of the genuine product of two fields is radical. -/
lemma productField_ideal_radical (k : Type u) [Field k] (I : Ideal (k × k)) :
    I.IsRadical := by
  have hk : ∀ J : Ideal k, J.IsRadical := by
    intro J
    rcases Ideal.eq_bot_or_top J with rfl | rfl
    · exact Ideal.isRadical_bot
    · exact Ideal.radical_eq_iff.mp (Ideal.radical_top k)
  rw [I.ideal_prod_eq]
  exact ((hk _).comap _).inf ((hk _).comap _)

/-- Unlike an arbitrary reduced target, Spec(k × k) has only radical ideals.
This identifies the actual source with an actual quotient, not with its support. -/
lemma reduced_of_closed_into_twoPoints (k : Type u) [Field k]
    {Z : Scheme.{u}} (i : Z ⟶ Spec (.of (k × k))) [IsClosedImmersion i] :
    IsReduced Z := by
  obtain ⟨I, e, _⟩ := IsClosedImmersion.Spec_iff.mp (inferInstance : IsClosedImmersion i)
  let : _root_.IsReduced ((k × k) ⧸ I) :=
    (Ideal.isRadical_iff_quotient_reduced I).mp (productField_ideal_radical k I)
  exact isReduced_of_isOpenImmersion e.hom

end AlgebraicGeometry.Scheme.TwoPoint
