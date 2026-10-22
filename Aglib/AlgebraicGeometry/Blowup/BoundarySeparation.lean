/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AffineAtlas
public import Aglib.AlgebraicGeometry.Blowup.GeneratorAtlas
public import Aglib.AlgebraicGeometry.Blowup.UnitLocus
public import Aglib.RingTheory.Blowup.BoundarySeparation

/-!
# Boundary-chart coverage for affine blowups

The topological chart-cover part of Conrad's Lemma 1.4, used in Lemma 1.5:
https://virtualmath1.stanford.edu/~conrad/papers/nagatafinal.pdf.
In the blowup of `I₁ ⊔ I₂`, the closure of the inverse image of
`V(I₁) \ V(I₁ ⊔ I₂)` is covered by the charts indexed by `I₂`.
The proof uses the actual saturated-chart relation `a * (b/a) = b`, and
openness of the original chart maps. It needs neither a reduced base nor
flatness or a bound on dimension.

The closure here is explicitly topological. No identification with a
scheme-theoretic strict transform, nor the full global separation theorem,
is asserted. In particular, the square-ideal schematic containment in
Conrad's Lemma 1.5 remains a separate input to the local separation algebra.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
universe u v

namespace AlgebraicGeometry.Scheme.Blowup.AffineAtlas

variable {A : Type u} [CommRing A] {K : Ideal A}
variable {B : BlowupDatum (affineCenter A K)}

/-- A chart indexed by an element of `I` misses the inverse image of
`V(I)` outside the centre. This holds even when the denominator is nilpotent. -/
lemma preimage_zeroLocus_diff_subset_compl_chart (H : AffineAtlas A K B)
    (I : Ideal A) (a : K) (ha : (a : A) ∈ I) :
    B.map ⁻¹' (PrimeSpectrum.zeroLocus (I : Set A) \ PrimeSpectrum.zeroLocus (K : Set A)) ⊆
      (Set.range (H.chart a))ᶜ := by
  intro x hx hchart
  obtain ⟨y, rfl⟩ := hchart
  have hbase : PrimeSpectrum.comap (algebraMap A (affineBlowupAlgebra A K a)) y ∈
      PrimeSpectrum.zeroLocus (I : Set A) \ PrimeSpectrum.zeroLocus (K : Set A) := by
    change (H.chart a ≫ B.map) y ∈
      (PrimeSpectrum.zeroLocus (I : Set A) \ PrimeSpectrum.zeroLocus (K : Set A)) at hx
    rwa [H.triangle] at hx
  apply hbase.2
  intro b hb
  change algebraMap A (affineBlowupAlgebra A K a) b ∈ y.asIdeal
  have ha' : algebraMap A (affineBlowupAlgebra A K a) a ∈ y.asIdeal := hbase.1 ha
  rw [← UnitLocus.ratio_mul_den K a ⟨b, hb⟩]
  exact y.asIdeal.mul_mem_left _ ha'

/-- The same chart misses the topological closure, because its range is open. -/
lemma closure_preimage_zeroLocus_diff_subset_compl_chart (H : AffineAtlas A K B)
    (I : Ideal A) (a : K) (ha : (a : A) ∈ I) :
    closure (B.map ⁻¹'
      (PrimeSpectrum.zeroLocus (I : Set A) \ PrimeSpectrum.zeroLocus (K : Set A))) ⊆
        (Set.range (H.chart a))ᶜ := by
  let := H.openImmersion a
  exact closure_minimal (H.preimage_zeroLocus_diff_subset_compl_chart I a ha)
    (IsOpenImmersion.isOpen_range (H.chart a)).isClosed_compl

/-- The closure of the first boundary away from the centre is covered by
the second-ideal charts of the actual atlas of the sum-ideal blowup. -/
lemma closure_preimage_zeroLocus_diff_covered_by_right
    (I₁ I₂ : Ideal A) {B : BlowupDatum (affineCenter A (I₁ ⊔ I₂))}
    (H : AffineAtlas A (I₁ ⊔ I₂) B) (x : B.Y)
    (hx : x ∈ closure (B.map ⁻¹'
      (PrimeSpectrum.zeroLocus (I₁ : Set A) \
        PrimeSpectrum.zeroLocus ((I₁ ⊔ I₂ : Ideal A) : Set A)))) :
    ∃ b : I₂, x ∈ Set.range (H.chart ⟨b, Ideal.mem_sup_right b.property⟩) := by
  let g : I₁ ⊕ I₂ → (I₁ ⊔ I₂ : Ideal A) := Sum.elim
    (fun a => ⟨a, Ideal.mem_sup_left a.property⟩)
    (fun b => ⟨b, Ideal.mem_sup_right b.property⟩)
  have hg : Ideal.span (Set.range fun i => (g i : A)) = I₁ ⊔ I₂ := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact (g i).property
    · apply sup_le
      · intro a ha
        exact Ideal.subset_span ⟨Sum.inl ⟨a, ha⟩, rfl⟩
      · intro b hb
        exact Ideal.subset_span ⟨Sum.inr ⟨b, hb⟩, rfl⟩
  obtain ⟨i, hi⟩ := H.generator_covers g hg x
  rcases i with a | b
  · exact False.elim
      (H.closure_preimage_zeroLocus_diff_subset_compl_chart I₁
        (g (Sum.inl a)) a.property hx hi)
  · exact ⟨b, hi⟩

end AlgebraicGeometry.Scheme.Blowup.AffineAtlas

namespace AlgebraicGeometry.Scheme.Blowup

variable {A : Type u} [CommRing A]

/-- Coverage for a protected boundary subset `T`, on the canonical actual
atlas of any universal affine blowup representative. The two hypotheses say
that `T` lies in the first boundary and is disjoint from the blowup centre. -/
lemma closure_preimage_boundary_covered_by_right (I₁ I₂ : Ideal A)
    (B : BlowupDatum (affineCenter A (I₁ ⊔ I₂))) (T : Set (PrimeSpectrum A))
    (hT : T ⊆ PrimeSpectrum.zeroLocus (I₁ : Set A))
    (havoid : Disjoint T (PrimeSpectrum.zeroLocus ((I₁ ⊔ I₂ : Ideal A) : Set A)))
    (x : B.Y) (hx : x ∈ closure (B.map ⁻¹' T)) :
    ∃ b : I₂, x ∈ Set.range ((affineAtlas B).chart ⟨b, Ideal.mem_sup_right b.property⟩) := by
  apply (affineAtlas B).closure_preimage_zeroLocus_diff_covered_by_right I₁ I₂ x
  apply closure_mono (s := B.map ⁻¹' T) ?_ hx
  intro y hy
  exact ⟨hT hy, fun hz => Set.disjoint_left.mp havoid hy hz⟩

/-- The local closure-separation step after arbitrary affine base change.
The subset `Y` is contained in the original closed subscheme `V(J)` and
avoids the second boundary. Denominator invertibility on `Y` is proved from
the actual chart relations, not assumed. The ideal containment remains
scheme-theoretic, with the essential square `I₁²`. -/
lemma chart_boundary_inter_closure_eq_empty {C : Type v} [CommRing C] [Algebra A C]
    (I₁ I₂ : Ideal A) (s₂ : A) (hs₂ : s₂ ∈ I₂)
    (φ : Localization.Away.saturatedChart A (I₁ ⊔ I₂) s₂ →ₐ[A] C)
    (J : Ideal C)
    (hcontain : I₂.map (algebraMap A C) ≤ (I₁ ^ 2).map (algebraMap A C) ⊔ J)
    (Y : Set (PrimeSpectrum C)) (hYJ : Y ⊆ PrimeSpectrum.zeroLocus (J : Set C))
    (hYavoid : ∀ x ∈ Y, PrimeSpectrum.comap (algebraMap A C) x ∉
      PrimeSpectrum.zeroLocus (I₂ : Set A)) :
    PrimeSpectrum.zeroLocus (I₁.map (algebraMap A C) : Set C) ∩ closure Y = ∅ := by
  let e := algebraMap C (Localization.Away (algebraMap A C s₂))
  have hY : Y ⊆ PrimeSpectrum.comap e ''
      PrimeSpectrum.zeroLocus (J.map e : Set (Localization.Away (algebraMap A C s₂))) := by
    intro x hx
    have hs : algebraMap A C s₂ ∉ x.asIdeal := by
      intro hs
      apply hYavoid x hx
      have hden : Ideal.span {algebraMap A C s₂} ≤ x.asIdeal :=
        Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hs)
      have hI₂ : I₂.map (algebraMap A C) ≤ x.asIdeal :=
        (Ideal.map_mono le_sup_right).trans
          ((Localization.Away.map_le_span_denominator _ _ φ).trans hden)
      intro b hb
      exact hI₂ (Ideal.mem_map_of_mem _ hb)
    have hxrange : x ∈ Set.range (PrimeSpectrum.comap e) := by
      rw [PrimeSpectrum.localization_away_comap_range
        (Localization.Away (algebraMap A C s₂)) (algebraMap A C s₂)]
      exact hs
    obtain ⟨z, hz⟩ := hxrange
    refine ⟨z, ?_, hz⟩
    change J.map e ≤ z.asIdeal
    rw [Ideal.map_le_iff_le_comap]
    change J ≤ (PrimeSpectrum.comap e z).asIdeal
    rw [hz]
    exact hYJ hx
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx' : x ∈ PrimeSpectrum.zeroLocus (I₁.map (algebraMap A C) : Set C) ∩
      closure (PrimeSpectrum.comap e '' PrimeSpectrum.zeroLocus
        (J.map e : Set (Localization.Away (algebraMap A C s₂)))) :=
    ⟨hx.1, closure_mono hY hx.2⟩
  rw [Localization.Away.boundary_inter_closure_localized_zeroLocus_eq_empty
    I₁ I₂ s₂ hs₂ φ J hcontain] at hx'
  exact hx'

end AlgebraicGeometry.Scheme.Blowup
