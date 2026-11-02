/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Ample.Proper
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing.Trivialization
public import Aglib.AlgebraicGeometry.Dimension.FiniteFibreImage
public import Aglib.AlgebraicGeometry.Dimension.ClosedPoints
public import Aglib.AlgebraicGeometry.Modules.Invertible.LocalRing
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing.GlobalFrame
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.Topology.KrullDimension

/-!
# Zeros of ample sections in positive dimension

An ample section on a proper positive-dimensional field scheme has a closed
zero. A nowhere-vanishing section would give an actual unit isomorphism,
so properness and the already proved trivial-ample criterion would make the
original structure map finite. Its strict specialization map to the field
spectrum bounds the source dimension by zero.

For an integral scheme locally of finite type over a field, a closed zero
also gives the lower dimension bound. On the original local spectrum the
line bundle is trivial; its actual section coefficient defines a principal
quotient. That spectrum embeds into the original vanishing set. The native
principal-ideal bound and closed-point local dimension finish the comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- Every section of an actual ample line bundle on a proper field scheme
of positive dimension vanishes at an actual closed point. -/
theorem LineBundle.IsAmple.exists_closed_zero_of_pos_dimension
    {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
    {L : LineBundle X} (hL : L.IsAmple) (s : Γ(L.val, ⊤))
    (hd : 0 < topologicalKrullDim X) :
    ∃ x : X, x ∉ nonvanishingOpen L s ∧ IsClosed ({x} : Set X) := by
  have hnonempty : ((nonvanishingOpen L s : Set X)ᶜ).Nonempty := by
    by_contra h
    have htop : nonvanishingOpen L s = ⊤ := by
      apply top_unique
      intro x _
      by_contra hx
      exact h ⟨x, hx⟩
    obtain ⟨e⟩ := Nonvanishing.trivial_of_nonvanishingOpen_eq_top L s htop
    have hclass : classOf X L = 0 :=
      Quotient.sound ⟨e ≪≫ (coproductUniqueIso
        (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)).symm⟩
    let : IsFinite p := hL.isFinite_of_isProper_of_classOf_eq_zero p hclass
    have hle := p.topologicalKrullDim_source_le_of_locallyQuasiFinite
    exact (not_lt_of_ge (hle.trans
      (topologicalKrullDim_zero_of_discreteTopology (Spec (.of k))))) hd
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  exact nonempty_inter_closedPoints hnonempty
    (nonvanishingOpen L s).isOpen.isClosed_compl.isLocallyClosed

/-- A closed zero of an actual section on an integral finite-type field
scheme bounds the original scheme dimension by the vanishing-set dimension
plus one. The local spectrum and principal quotient are chosen only inside
the proof; no regularity or catenarity hypothesis is used. -/
theorem topologicalKrullDim_le_vanishingDimension_add_one_of_closed_zero
    (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (L : LineBundle X) (s : Γ(L.val, ⊤)) (x : X)
    (hx : IsClosed ({x} : Set X)) (hs : x ∉ nonvanishingOpen L s) :
    topologicalKrullDim X ≤
      topologicalKrullDim (((nonvanishingOpen L s : Set X)ᶜ) : Set X) + 1 := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let R := X.presheaf.stalk x
  let t := X.fromSpecStalk x
  let L' := pullbackLineBundle t L
  let s' := Nonvanishing.pullbackSection t L.val s
  obtain ⟨e⟩ := nonempty_iso_unit_of_isLocalRing R L'
  let a : Γ(Spec R, ⊤) := e.hom.val.app (Opposite.op ⊤) s'
  let r : R := (Scheme.ΓSpecIso R).hom a
  have hvan : t ⁻¹ᵁ nonvanishingOpen L s = PrimeSpectrum.basicOpen r := by
    have h₁ : nonvanishingOpen L' s' = t ⁻¹ᵁ nonvanishingOpen L s :=
      Nonvanishing.nonvanishingOpen_pullback t L s
    have h₂ : nonvanishingOpen L' s' = (Spec R).basicOpen a :=
      Nonvanishing.nonvanishingOpen_eq_basicOpen_of_unitIso L' e s'
    have h₃ : (Spec R).basicOpen a = PrimeSpectrum.basicOpen r := basicOpen_eq_of_affine' a
    exact h₁.symm.trans (h₂.trans h₃)
  have hr : r ∈ IsLocalRing.maximalIdeal R := by
    have hc : (IsLocalRing.closedPoint R) ∉ PrimeSpectrum.basicOpen r := by
      rw [← hvan]
      change t (IsLocalRing.closedPoint R) ∉ nonvanishingOpen L s
      have htx : t (IsLocalRing.closedPoint R) = x := X.fromSpecStalk_closedPoint
      exact (congrArg (fun z : X => z ∉ nonvanishingOpen L s) htx).mpr hs
    exact not_not.mp hc
  let I : Ideal R := Ideal.span {r}
  let j : Spec (.of (R ⧸ I)) ⟶ Spec R := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _
    Ideal.Quotient.mk_surjective
  let q : Spec (.of (R ⧸ I)) ⟶ X := j ≫ t
  let Z : Set X := (nonvanishingOpen L s : Set X)ᶜ
  have hrzero : Ideal.Quotient.mk I r = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton r))
  have hqZ : ∀ y, q y ∈ Z := by
    intro y hy
    have hb : j y ∈ PrimeSpectrum.basicOpen r := by
      rw [← hvan]
      exact hy
    have hpre : y ∈ j ⁻¹ᵁ PrimeSpectrum.basicOpen r := hb
    change Ideal.Quotient.mk I r ∉ y.asIdeal at hpre
    rw [hrzero] at hpre
    exact hpre y.asIdeal.zero_mem
  have hq : Topology.IsEmbedding q := t.isEmbedding.comp j.isClosedEmbedding.isEmbedding
  have hdim : ringKrullDim (R ⧸ I) ≤ topologicalKrullDim Z := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R ⧸ I)]
    exact (hq.codRestrict Z hqZ).isInducing.topologicalKrullDim_le
  have hR : ringKrullDim R ≤ ringKrullDim (R ⧸ I) + 1 := by
    have hrJ : r ∈ Ring.jacobson R := by
      rw [← Ideal.jacobson_bot]
      exact (IsLocalRing.maximalIdeal_le_jacobson ⊥) hr
    have h := ringKrullDim_le_ringKrullDim_quotient_add_encard ({r} : Set R)
      (Set.singleton_subset_iff.mpr hrJ)
    simpa only [Set.encard_singleton, WithBot.coe_one, I] using h
  rw [← Scheme.ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed k p x hx]
  exact hR.trans (add_le_add hdim le_rfl)

end AlgebraicGeometry.Scheme.Modules.Invertible
