/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.BoundarySeparation
public import Aglib.AlgebraicGeometry.Blowup.AffineCenter.Support
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Assembly of boundary separation on the actual pullback

The affine-base assembly of Conrad's Lemma 1.5 uses literal tensor-product
charts of the pullback of the original blowup, not a blowup of the pulled-back
ideal. The latter need not agree without flatness. Closure is localized along
the actual open chart morphisms. All ideal containments retain `I₁²`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
universe u

namespace AlgebraicGeometry.Scheme.Blowup

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]
variable {K : Ideal A} {B : BlowupDatum (affineCenter A K)}

/-- The actual tensor-product chart in the pullback of a universal affine
blowup. No flatness of the base map is required. -/
def affineBaseChangeChart (H : AffineAtlas A K B) (a : K) :
    Spec (.of (R ⊗[A] affineBlowupAlgebra A K a)) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap A R))) B.map :=
  (pullbackSpecIso A R (affineBlowupAlgebra A K a)).inv ≫
    pullback.map _ _ _ _ (𝟙 _) (H.chart a) (𝟙 _)
      (by simp) (by simpa only [Category.comp_id, affineChartMap] using (H.triangle a).symm)

instance affineBaseChangeChart_isOpenImmersion (H : AffineAtlas A K B) (a : K) :
    IsOpenImmersion (affineBaseChangeChart (R := R) H a) := by
  let := H.openImmersion a
  unfold affineBaseChangeChart
  infer_instance

@[reassoc (attr := simp)]
lemma affineBaseChangeChart_fst (H : AffineAtlas A K B) (a : K) :
    affineBaseChangeChart (R := R) H a ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (R ⊗[A] affineBlowupAlgebra A K a))) := by
  simp only [affineBaseChangeChart, Category.assoc, pullback.lift_fst,
    Category.comp_id, pullbackSpecIso_inv_fst']

@[reassoc (attr := simp)]
lemma affineBaseChangeChart_snd (H : AffineAtlas A K B) (a : K) :
    affineBaseChangeChart (R := R) H a ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom :
          affineBlowupAlgebra A K a →+* R ⊗[A] affineBlowupAlgebra A K a)) ≫
        H.chart a := by
  simp only [affineBaseChangeChart, Category.assoc, pullback.lift_snd,
    pullbackSpecIso_inv_snd_assoc, AlgHom.toRingHom_eq_coe]

/-- Exact chart range in the pullback, proved using the native range theorem. -/
lemma affineBaseChangeChart_range (H : AffineAtlas A K B) (a : K) :
    Set.range (affineBaseChangeChart (R := R) H a) =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A R))) B.map ⁻¹'
        Set.range (H.chart a) := by
  unfold affineBaseChangeChart
  rw [show Set.range ((pullbackSpecIso A R (affineBlowupAlgebra A K a)).inv ≫ _) =
      Set.range _ from
    Scheme.Hom.Range.range_iso_comp (pullbackSpecIso A R (affineBlowupAlgebra A K a)).symm _,
    Scheme.Pullback.range_map]
  simp

@[reassoc]
lemma affineBaseChangeChart_base (H : AffineAtlas A K B) (a : K) :
    affineBaseChangeChart (R := R) H a ≫ pullback.snd _ _ ≫ B.map =
      Spec.map (CommRingCat.ofHom
        (algebraMap A (R ⊗[A] affineBlowupAlgebra A K a))) := by
  rw [← pullback.condition, ← Category.assoc, affineBaseChangeChart_fst,
    ← Spec.map_comp]
  congr 1

/-- End-to-end affine boundary separation on the actual scheme pullback.
`S` lies in the original closed subscheme `V(J)` and avoids `V(I₂)`; `T`
is the protected boundary. The schematic input is the original-ring
containment `I₂ R ≤ I₁² R + J`, before any base change. -/
theorem affine_boundary_separation (I₁ I₂ : Ideal A)
    (B : BlowupDatum (affineCenter A (I₁ ⊔ I₂))) (J : Ideal R)
    (hcontain : I₂.map (algebraMap A R) ≤ (I₁ ^ 2).map (algebraMap A R) ⊔ J)
    (S : Set (PrimeSpectrum R)) (hSJ : S ⊆ PrimeSpectrum.zeroLocus (J : Set R))
    (hSavoid : ∀ x ∈ S, PrimeSpectrum.comap (algebraMap A R) x ∉
      PrimeSpectrum.zeroLocus (I₂ : Set A))
    (T : Set (PrimeSpectrum A)) (hT : T ⊆ PrimeSpectrum.zeroLocus (I₁ : Set A))
    (hTavoid : Disjoint T (PrimeSpectrum.zeroLocus ((I₁ ⊔ I₂ : Ideal A) : Set A))) :
    Disjoint
      (closure (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A R))) B.map ⁻¹' S))
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A R))) B.map ⁻¹'
        closure (B.map ⁻¹' T)) := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap A R))
  let H := affineAtlas B
  apply Set.disjoint_left.mpr
  intro z hz hzT
  obtain ⟨a, ha⟩ := closure_preimage_boundary_covered_by_right I₁ I₂ B T hT hTavoid
    (pullback.snd p B.map z) hzT
  let a' : (I₁ ⊔ I₂ : Ideal A) := ⟨a, Ideal.mem_sup_right a.property⟩
  let C := R ⊗[A] affineBlowupAlgebra A (I₁ ⊔ I₂) a'
  let c := affineBaseChangeChart (R := R) H a'
  have hzrange : z ∈ Set.range c := by
    rw [affineBaseChangeChart_range]
    exact ha
  obtain ⟨w, rfl⟩ := hzrange
  have hwclosure : w ∈ closure
      (PrimeSpectrum.comap (algebraMap R C) ⁻¹' S) := by
    have he := c.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      c.continuous (pullback.fst p B.map ⁻¹' S)
    have hw : w ∈ closure (c ⁻¹' (pullback.fst p B.map ⁻¹' S)) := by
      rw [← he]
      exact hz
    change w ∈ closure ((c ≫ pullback.fst p B.map) ⁻¹' S) at hw
    rw [affineBaseChangeChart_fst] at hw
    exact hw
  have hwboundary : w ∈ PrimeSpectrum.zeroLocus (I₁.map (algebraMap A C) : Set C) := by
    have hclosed : closure (B.map ⁻¹' T) ⊆
        B.map ⁻¹' PrimeSpectrum.zeroLocus (I₁ : Set A) :=
      closure_minimal (Set.preimage_mono hT)
        ((PrimeSpectrum.isClosed_zeroLocus _).preimage B.map.continuous)
    have hw := hclosed hzT
    change (c ≫ pullback.snd p B.map ≫ B.map) w ∈
      PrimeSpectrum.zeroLocus (I₁ : Set A) at hw
    rw [affineBaseChangeChart_base] at hw
    change I₁.map (algebraMap A C) ≤ w.asIdeal
    rw [Ideal.map_le_iff_le_comap]
    exact hw
  have hcontain' : I₂.map (algebraMap A C) ≤
      (I₁ ^ 2).map (algebraMap A C) ⊔ J.map (algebraMap R C) := by
    have h := Ideal.map_mono (f := algebraMap R C) hcontain
    simpa only [Ideal.map_sup, Ideal.map_map, ← IsScalarTower.algebraMap_eq A R C] using h
  have hSJ' : PrimeSpectrum.comap (algebraMap R C) ⁻¹' S ⊆
      PrimeSpectrum.zeroLocus (J.map (algebraMap R C) : Set C) := by
    intro x hx
    change J.map (algebraMap R C) ≤ x.asIdeal
    rw [Ideal.map_le_iff_le_comap]
    exact hSJ hx
  have hSavoid' : ∀ x ∈ PrimeSpectrum.comap (algebraMap R C) ⁻¹' S,
      PrimeSpectrum.comap (algebraMap A C) x ∉ PrimeSpectrum.zeroLocus (I₂ : Set A) := by
    intro x hx
    rw [IsScalarTower.algebraMap_eq A R C, PrimeSpectrum.comap_comp_apply]
    exact hSavoid _ hx
  have hsep := chart_boundary_inter_closure_eq_empty I₁ I₂ a a.property
    (Algebra.TensorProduct.includeRight :
      affineBlowupAlgebra A (I₁ ⊔ I₂) a' →ₐ[A] C)
    (J.map (algebraMap R C)) hcontain'
    (PrimeSpectrum.comap (algebraMap R C) ⁻¹' S) hSJ' hSavoid'
  have hw : w ∈ PrimeSpectrum.zeroLocus (I₁.map (algebraMap A C) : Set C) ∩
      closure (PrimeSpectrum.comap (algebraMap R C) ⁻¹' S) := ⟨hwboundary, hwclosure⟩
  rw [hsep] at hw
  exact hw

private lemma spectrumIdeal_affineCenter_eq (I : Ideal A) :
    spectrumIdeal (affineCenter A I) = I := by
  unfold spectrumIdeal affineCenter
  rw [Scheme.IdealSheafData.specMap_kernel_top, Ideal.mk_ker,
    Ideal.map_comap_of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).hom).2]

private lemma spectrumIdeal_sup_eq (I J : (Spec (.of A)).IdealSheafData) :
    spectrumIdeal (I ⊔ J) = spectrumIdeal I ⊔ spectrumIdeal J := by
  exact Ideal.map_sup _ _ _

private lemma spectrumIdeal_pow_eq (I : (Spec (.of A)).IdealSheafData) (n : ℕ) :
    spectrumIdeal (I ^ n) = spectrumIdeal I ^ n := by
  exact Ideal.map_pow _ _ _

private lemma affineCenter_pow_eq (I : Ideal A) (n : ℕ) :
    affineCenter A (I ^ n) = (affineCenter A I) ^ n := by
  rw [← affineCenter_spectrumIdeal ((affineCenter A I) ^ n),
    spectrumIdeal_pow_eq, spectrumIdeal_affineCenter_eq]

/-- Conrad's Lemma 1.5 for the original diagram with affine `X` and `Z`.
The source `Y` need not be affine, and `f` is arbitrary. The containment uses
the original native kernel `f.ker`, while the separation conclusion uses the
actual base-changed source.
No Noetherian, reducedness, dimension, or flatness assumption is used. -/
theorem affine_originalDiagram_boundary_separation {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R))
    (U V : (Spec (.of A)).Opens) (hUV : U ≤ V)
    (hfU : ∀ y, (f ≫ Spec.map (CommRingCat.ofHom (algebraMap A R))) y ∈ U)
    (I₁ I₂ : Ideal A)
    (hI₁ : (V : Set (Spec (.of A))) \ (U : Set (Spec (.of A))) ⊆
      PrimeSpectrum.zeroLocus (I₁ : Set A))
    (_hI₁U : PrimeSpectrum.zeroLocus (I₁ : Set A) ⊆ (U : Set (Spec (.of A)))ᶜ)
    (hI₂ : PrimeSpectrum.zeroLocus (I₂ : Set A) ⊆
      PrimeSpectrum.zeroLocus (I₁ : Set A) ∩ (V : Set (Spec (.of A)))ᶜ)
    (hcontain : (affineCenter A I₂).comap
        (Spec.map (CommRingCat.ofHom (algebraMap A R))) ≤
      ((affineCenter A I₁) ^ 2).comap
        (Spec.map (CommRingCat.ofHom (algebraMap A R))) ⊔ f.ker)
    (B : BlowupDatum (affineCenter A (I₁ ⊔ I₂))) :
    Disjoint
      (closure (Set.range (pullback.snd f
        (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A R))) B.map))))
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A R))) B.map ⁻¹'
        closure (B.map ⁻¹' ((V : Set (Spec (.of A))) \ (U : Set (Spec (.of A)))))) := by
  have hring : I₂.map (algebraMap A R) ≤
      (I₁ ^ 2).map (algebraMap A R) ⊔ spectrumIdeal f.ker := by
    rw [← affineCenter_pow_eq, BaseChange.affineCenter_comap,
      BaseChange.affineCenter_comap] at hcontain
    have h := Ideal.map_mono
      (f := (Scheme.ΓSpecIso (.of R)).hom.hom)
      (hcontain ⟨⊤, isAffineOpen_top _⟩)
    change spectrumIdeal (affineCenter R (I₂.map (algebraMap A R))) ≤
      spectrumIdeal (affineCenter R ((I₁ ^ 2).map (algebraMap A R)) ⊔ f.ker) at h
    simpa only [spectrumIdeal_sup_eq, spectrumIdeal_affineCenter_eq] using h
  have hSJ : Set.range f ⊆ PrimeSpectrum.zeroLocus (spectrumIdeal f.ker : Set R) := by
    rw [← support_affineCenter, affineCenter_spectrumIdeal]
    exact f.range_subset_ker_support
  have hSavoid : ∀ x ∈ Set.range f, PrimeSpectrum.comap (algebraMap A R) x ∉
      PrimeSpectrum.zeroLocus (I₂ : Set A) := by
    rintro _ ⟨y, rfl⟩ hy
    exact (hI₂ hy).2 (hUV (hfU y))
  have hTavoid : Disjoint ((V : Set (Spec (.of A))) \ (U : Set (Spec (.of A))))
      (PrimeSpectrum.zeroLocus ((I₁ ⊔ I₂ : Ideal A) : Set A)) := by
    apply Set.disjoint_left.mpr
    intro x hx hxI
    have hxI₂ : x ∈ PrimeSpectrum.zeroLocus (I₂ : Set A) :=
      fun b hb => hxI (Ideal.mem_sup_right hb)
    exact (hI₂ hxI₂).2 hx.1
  rw [Scheme.Pullback.range_snd]
  exact affine_boundary_separation I₁ I₂ B (spectrumIdeal f.ker) hring
    (Set.range f) hSJ hSavoid ((V : Set (Spec (.of A))) \ (U : Set (Spec (.of A)))) hI₁ hTavoid

end AlgebraicGeometry.Scheme.Blowup
