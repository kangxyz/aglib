/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts

/-!
# Actual source normalization on a genuine common ideal

The original surjective quotient determines a commuting source ring map.
A source ring isomorphism over the same ambient ring is therefore the
actual quotient transport attached to equality of its ideals. The same
closed square determines the actual source open after this transport.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original surjective quotient determines its actual outgoing ring map. -/
theorem canonicalQuotientHom_ext {A B : CommRingCat.{u}} (I : Ideal A)
    {f g : CommRingCat.of (A ⧸ I) ⟶ B}
    (h : (CommRingCat.ofHom (Ideal.Quotient.mk I) : A ⟶ CommRingCat.of (A ⧸ I)) ≫ f =
      (CommRingCat.ofHom (Ideal.Quotient.mk I) : A ⟶ CommRingCat.of (A ⧸ I)) ≫ g) : f = g := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact congrArg (fun k : A ⟶ B => k a) h

/-- A source ring isomorphism in the original quotient square is the genuine ideal transport. -/
theorem canonicalQuotientIso_ofSquare {A : CommRingCat.{u}} (I J : Ideal A)
    (e : CommRingCat.of (A ⧸ I) ≅ CommRingCat.of (A ⧸ J))
    (h : (CommRingCat.ofHom (Ideal.Quotient.mk I) : A ⟶ CommRingCat.of (A ⧸ I)) ≫ e.hom =
      (CommRingCat.ofHom (Ideal.Quotient.mk J) : A ⟶ CommRingCat.of (A ⧸ J))) :
    ∃ hIJ : I = J, e = (Ideal.quotEquivOfEq hIJ).toCommRingCatIso := by
  let er := e.commRingCatIsoToRingEquiv
  have hx (x : A) : er (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x :=
    congrArg (fun k : A ⟶ CommRingCat.of (A ⧸ J) => k x) h
  have hIJ : I = J := by
    ext x
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro hi
      exact (hx x).symm.trans ((congrArg er hi).trans (map_zero er))
    · intro hj
      apply er.injective
      exact (hx x).trans (hj.trans (map_zero er).symm)
  refine ⟨hIJ, ?_⟩
  apply Iso.ext
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact (hx x).trans (Ideal.quotEquivOfEq_mk hIJ x).symm

/-- The original closed square determines the actual source open after ideal normalization. -/
theorem canonicalQuotientSources_eq {A : CommRingCat.{u}} {X P : Scheme.{u}}
    (i : X ⟶ P) [Mono i] (I : Ideal A) (j : Spec A ⟶ P)
    (a b : Spec (CommRingCat.of (A ⧸ I)) ⟶ X)
    (ha : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ j = a ≫ i)
    (hb : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ j = b ≫ i) : a = b :=
  (cancel_mono i).mp (ha.symm.trans hb)

/-- The original actual quotient-chart source, transported only by equality of its ideal. -/
def canonicalChartSourceAtIdeal
    {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ} {x : X}
    (C : SmoothClosedImmersionLocalChart i p n d x) (I : Ideal C.A)
    (hI : Ideal.ofList C.regularList = I) : Spec (CommRingCat.of (C.A ⧸ I)) ⟶ X := by
  subst I
  exact C.quotientChart.jX

instance canonicalChartSourceAtIdeal_isOpenImmersion
    {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ} {x : X}
    (C : SmoothClosedImmersionLocalChart i p n d x) (I : Ideal C.A)
    (hI : Ideal.ofList C.regularList = I) :
    IsOpenImmersion (canonicalChartSourceAtIdeal C I hI) := by
  subst I
  exact C.quotientChart.openX

/-- The transported source retains the same original actual closed square. -/
theorem canonicalChartSourceAtIdeal_closedSquare
    {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ} {x : X}
    (C : SmoothClosedImmersionLocalChart i p n d x) (I : Ideal C.A)
    (hI : Ideal.ofList C.regularList = I) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ C.jP =
      canonicalChartSourceAtIdeal C I hI ≫ i := by
  subst I
  exact C.quotientChart.closedSquare

/-- Genuine ideal transport is the same original spectral quotient-isomorphism refinement. -/
theorem canonicalChartSourceAtIdeal_spec
    {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ} {x : X}
    (C : SmoothClosedImmersionLocalChart i p n d x) (I : Ideal C.A)
    (hI : Ideal.ofList C.regularList = I) :
    canonicalChartSourceAtIdeal C I hI =
      Spec.map (Ideal.quotEquivOfEq hI).toCommRingCatIso.hom ≫ C.quotientChart.jX := by
  subst I
  have he : (Ideal.quotEquivOfEq (show Ideal.ofList C.regularList =
      Ideal.ofList C.regularList from rfl)).toCommRingCatIso.hom =
      𝟙 (regularListQuotientRing C.regularList) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact Ideal.quotEquivOfEq_mk rfl a
  rw [he, Spec.map_id, Category.id_comp]
  rfl

end AlgebraicGeometry.Scheme.Modules
