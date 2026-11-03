/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.FlatBaseChange.QuotientChart

/-! # Scheme-theoretic uniqueness of a quotient chart over the same ambient chart

The two actual Cartesian squares give native quotient-source isomorphisms.
Their original quotient-map equations prove equality of the actual ideals,
not merely radicals. No presentation equivalence or comparison is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u
namespace AlgebraicGeometry.Scheme.Modules.ClosedImmersionAffineQuotientChart

variable {X Y : Scheme.{u}} {i : X ⟶ Y} {R : CommRingCat.{u}} {a : Spec R ⟶ Y}

/-- The actual ideals of two quotient charts over the same specified ambient
chart are equal, including their nonreduced scheme structure. -/
theorem ideal_eq (Q Q' : ClosedImmersionAffineQuotientChart i R a) : Q.ideal = Q'.ideal := by
  let e := Q.square.isoIsPullback X (Spec R) Q'.square
  let f : CommRingCat.of (R ⧸ Q'.ideal) ⟶ .of (R ⧸ Q.ideal) := Spec.preimage e.hom
  let g : CommRingCat.of (R ⧸ Q.ideal) ⟶ .of (R ⧸ Q'.ideal) := Spec.preimage e.inv
  let q : R ⟶ .of (R ⧸ Q.ideal) := CommRingCat.ofHom (Ideal.Quotient.mk Q.ideal)
  let q' : R ⟶ .of (R ⧸ Q'.ideal) := CommRingCat.ofHom (Ideal.Quotient.mk Q'.ideal)
  have hf : q' ≫ f = q := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    change Spec.map (Spec.preimage e.hom) ≫ Spec.map q' = Spec.map q
    rw [Spec.map_preimage]
    exact Q.square.isoIsPullback_hom_snd X (Spec R) Q'.square
  have hg : q ≫ g = q' := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    change Spec.map (Spec.preimage e.inv) ≫ Spec.map q = Spec.map q'
    rw [Spec.map_preimage]
    exact Q.square.isoIsPullback_inv_snd X (Spec R) Q'.square
  apply le_antisymm
  · intro r hr
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hz : Ideal.Quotient.mk Q.ideal r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
    have he : g.hom (Ideal.Quotient.mk Q.ideal r) = Ideal.Quotient.mk Q'.ideal r :=
      congrArg (fun k : R ⟶ .of (R ⧸ Q'.ideal) => k.hom r) hg
    rw [hz, map_zero] at he
    exact he.symm
  · intro r hr
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hz : Ideal.Quotient.mk Q'.ideal r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
    have he : f.hom (Ideal.Quotient.mk Q'.ideal r) = Ideal.Quotient.mk Q.ideal r :=
      congrArg (fun k : R ⟶ .of (R ⧸ Q.ideal) => k.hom r) hf
    rw [hz, map_zero] at he
    exact he.symm

/-- Once the actual ideal equality is proved, the original mono identifies
both source maps; the remaining chart fields are propositions. -/
theorem eq_of_same_ambient [Mono i]
    (Q Q' : ClosedImmersionAffineQuotientChart i R a) : Q = Q' := by
  have hI := ideal_eq Q Q'
  rcases Q with ⟨I, s, hs, H⟩
  rcases Q' with ⟨I', s', hs', H'⟩
  change I = I' at hI
  subst I'
  have he : s = s' := (cancel_mono i).mp (H.w.trans H'.w.symm)
  subst s'
  rfl

end AlgebraicGeometry.Scheme.Modules.ClosedImmersionAffineQuotientChart
