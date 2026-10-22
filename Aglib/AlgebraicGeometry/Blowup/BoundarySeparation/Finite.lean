/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.BoundarySeparation
public import Aglib.AlgebraicGeometry.Blowup.FlatBaseChange
public import Aglib.AlgebraicGeometry.Blowup.AffineCenter.Restriction
public import Aglib.AlgebraicGeometry.Blowup.Construction
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Separation of boundary closures for a family of ideals

Blowing up the sum of an arbitrary family of ideals separates the closures of
their inverse-image supports away from the centre: these closures have empty
intersection. This is the topological part of Conrad's Lemma 1.4 needed in
Lemma 3.2 of `https://virtualmath1.stanford.edu/~conrad/papers/nagatafinal.pdf`.

The proof uses actual blowup charts and open flat base change. It works over
arbitrary rings, including nonreduced rings, and does not identify schematic
strict transforms or assert a nonflat base-change isomorphism. The empty
family is allowed; its sum is the zero ideal and its blowup is empty.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
universe u v

namespace AlgebraicGeometry.Scheme.Blowup

/-- Affine boundary separation for an arbitrary family on any actual blowup representative.
A denominator from one ideal gives an open chart missing that ideal's
boundary closure; charts indexed by the whole family cover the blowup. -/
theorem affine_finite_boundary_separation {A : Type u} [CommRing A]
    {ι : Type v} (I : ι → Ideal A)
    (B : BlowupDatum (affineCenter A (⨆ i, I i))) :
    (⋂ i, closure (B.map ⁻¹'
      (PrimeSpectrum.zeroLocus (I i : Set A) \
        PrimeSpectrum.zeroLocus ((⨆ j, I j : Ideal A) : Set A)))) = ∅ := by
  let H := affineAtlas B
  let g : (Σ i, I i) → (⨆ i, I i : Ideal A) :=
    fun a => ⟨a.2, (le_iSup I a.1) a.2.property⟩
  have hg : Ideal.span (Set.range fun a => (g a : A)) = ⨆ i, I i := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨a, rfl⟩
      exact (g a).property
    · apply iSup_le
      intro i a ha
      exact Ideal.subset_span ⟨⟨i, ⟨a, ha⟩⟩, rfl⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨a, ha⟩ := H.generator_covers g hg x
  exact H.closure_preimage_zeroLocus_diff_subset_compl_chart
    (I a.1) (g a) a.2.property (Set.mem_iInter.mp hx a.1) ha

/-- Blowing up the sum ideal separates the boundary closures outside the
common centre. No Noetherianity, reducedness, or dimension assumption is used. -/
theorem finite_boundary_separation {X : Scheme.{u}} {ι : Type v}
    (I : ι → X.IdealSheafData) (B : BlowupDatum (⨆ i, I i)) :
    (⋂ i, closure (B.map ⁻¹'
      ((I i).support \ (⨆ j, I j).support))) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := B.map x) (U := ⊤) (by trivial)
  let A : CommRingCat := Γ(X, U)
  let u : Spec A ⟶ X := hU.fromSpec
  let K : ι → Ideal A := fun i => (I i).ideal ⟨U, hU⟩
  have hK : (⨆ i, I i).ideal ⟨U, hU⟩ = ⨆ i, K i := by
    simp only [Scheme.IdealSheafData.ideal_iSup, iSup_apply, K]
  have hc : (⨆ i, I i).comap u = affineCenter A (⨆ i, K i) := by
    rw [comap_fromSpec_eq_affineCenter (⨆ i, I i) ⟨U, hU⟩, hK]
  let B₀ := affineProjBlowupDatum (⨆ i, K i)
  let b : B₀.Y ⟶ B.Y := BaseChange.map u hc B B₀
  have hb : IsPullback b B₀.map B.map u :=
    BaseChange.isPullback_of_flat u inferInstance hc B B₀
  let : IsOpenImmersion b := MorphismProperty.of_isPullback hb.flip inferInstance
  have hbrange : Set.range b = B.map ⁻¹' Set.range u := by
    rw [← hb.isoPullback_hom_fst, Scheme.Hom.Range.range_iso_comp,
      Scheme.Pullback.range_fst]
  have hxrange : x ∈ Set.range b := by
    rw [hbrange]
    change B.map x ∈ Set.range hU.fromSpec
    rw [hU.range_fromSpec]
    exact hxU
  obtain ⟨x₀, rfl⟩ := hxrange
  have hpre (i : ι) :
      u ⁻¹' ((I i).support \ (⨆ j, I j).support) =
        PrimeSpectrum.zeroLocus (K i : Set A) \
          PrimeSpectrum.zeroLocus ((⨆ j, K j : Ideal A) : Set A) := by
    ext y
    change (u y ∈ (I i).support ∧ u y ∉ (⨆ j, I j).support) ↔ _
    have hi := Scheme.IdealSheafData.fromSpec_mem_support_iff (I i) ⟨U, hU⟩ y
    have hk := Scheme.IdealSheafData.fromSpec_mem_support_iff (⨆ j, I j) ⟨U, hU⟩ y
    rw [hK] at hk
    exact and_congr hi (not_congr hk)
  have hclosure (i : ι) :
      b ⁻¹' closure (B.map ⁻¹' ((I i).support \ (⨆ j, I j).support)) =
        closure (B₀.map ⁻¹' (PrimeSpectrum.zeroLocus (K i : Set A) \
          PrimeSpectrum.zeroLocus ((⨆ j, K j : Ideal A) : Set A))) := by
    rw [b.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage b.continuous]
    refine Eq.trans ?_ (congrArg
      (fun s : Set (Spec A) => closure (B₀.map ⁻¹' s)) (hpre i))
    exact congrArg (fun f : B₀.Y ⟶ X =>
      closure (f ⁻¹' (((I i).support : Set X) \ (⨆ j, I j).support))) hb.w
  have hx₀ : x₀ ∈ ⋂ i, closure (B₀.map ⁻¹'
      (PrimeSpectrum.zeroLocus (K i : Set A) \
        PrimeSpectrum.zeroLocus ((⨆ j, K j : Ideal A) : Set A))) := by
    apply Set.mem_iInter.mpr
    intro i
    rw [← hclosure i]
    exact Set.mem_iInter.mp hx i
  rw [affine_finite_boundary_separation K B₀] at hx₀
  exact hx₀

end AlgebraicGeometry.Scheme.Blowup
