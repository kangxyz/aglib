/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AffineConstruction
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.SpecKernel
public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.Affine
public import Aglib.AlgebraicGeometry.IdealSheaf.LocallyClosed
public import Aglib.RingTheory.Localization.Away.SaturatedChartLift

/-!
# Affine pivot charts for a Cartier inverse-image ideal

The ideal is the actual image of the original centre. Local rank one supplies a
regular generator; its quotient coefficients generate the unit ideal. Their basic
opens therefore choose pivots from the original ideal, without a finiteness or
Noetherian hypothesis. This is a new proof on the native image-ideal objects.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Blowup

private lemma quotientCoefficients_span {A S : Type u} [CommRing A] [CommRing S]
    (I : Ideal A) (f : A →+* S) (r : S) (hr : IsRegular r)
    (hI : I.map f = Ideal.span {r}) :
    ∃ q : I → S, (∀ b : I, f b = r * q b) ∧ Ideal.span (Set.range q) = ⊤ := by
  have hdiv (b : I) : ∃ s : S, f b = r * s := by
    have hb : f b ∈ Ideal.span {r} := hI ▸ Ideal.mem_map_of_mem f b.property
    simpa only [Ideal.mem_span_singleton, dvd_def] using hb
  choose q hq using hdiv
  refine ⟨q, hq, ?_⟩
  let J : Ideal S := Ideal.span (Set.range q)
  have hmul : ∀ x ∈ I.map f, ∃ s ∈ J, x = r * s := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨q ⟨b, hb⟩, Ideal.subset_span ⟨⟨b, hb⟩, rfl⟩, hq ⟨b, hb⟩⟩
    | zero => exact ⟨0, J.zero_mem, (mul_zero r).symm⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, rfl⟩ := hx
      obtain ⟨t, ht, rfl⟩ := hy
      exact ⟨s + t, J.add_mem hs ht, (mul_add r s t).symm⟩
    | smul c x _ hx =>
      obtain ⟨s, hs, rfl⟩ := hx
      exact ⟨c * s, J.mul_mem_left c hs, by simp [smul_eq_mul, mul_left_comm]⟩
  obtain ⟨s, hs, hrs⟩ := hmul r (hI ▸ Ideal.mem_span_singleton_self r)
  have hs1 : s = 1 := hr.left (by simpa using hrs.symm)
  exact Ideal.eq_top_of_isUnit_mem J (hs1 ▸ hs) isUnit_one

/-- The actual scalar map on an affine open of a scheme over `Spec A`. -/
def affineBaseMap {A : Type u} [CommRing A] {T : Scheme.{u}}
    (f : T ⟶ Spec (.of A)) (U : T.Opens) : A →+* Γ(T, U) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ U (by simp)).hom

/-- On every affine source open, the inverse-image centre is the literal mapped ideal. -/
lemma affineCenter_comap_ideal {A : Type u} [CommRing A] (I : Ideal A)
    {T : Scheme.{u}} (f : T ⟶ Spec (.of A)) (U : T.affineOpens) :
    ((affineCenter A I).comap f).ideal U = I.map (affineBaseMap f U) := by
  rw [Scheme.IdealSheafData.ideal_comap_eq_map_appLE _ f
    ⟨⊤, isAffineOpen_top _⟩ U (by simp)]
  change (((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker).ideal
    ⟨⊤, isAffineOpen_top _⟩).map _ = _
  rw [Scheme.IdealSheafData.specMap_kernel_top, Ideal.mk_ker]
  have he : I.comap (Scheme.ΓSpecIso (.of A)).hom.hom =
      I.map (Scheme.ΓSpecIso (.of A)).inv.hom :=
    (Ideal.map_symm (I := I) (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv).symm
  rw [he, Ideal.map_map]
  rfl

/-- Restriction of the actual base scalar map is the scalar map on the smaller open. -/
lemma affineBaseMap_restrict {A : Type u} [CommRing A] {T : Scheme.{u}}
    (f : T ⟶ Spec (.of A)) {U V : T.Opens} (hVU : V ≤ U) :
    (T.presheaf.map (homOfLE hVU).op).hom.comp (affineBaseMap f U) =
      affineBaseMap f V := by
  dsimp only [affineBaseMap]
  rw [← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.appLE_map]

/-- A Cartier inverse-image ideal has affine neighbourhoods whose regular generator is the
image of an element of the original ideal. Every other original element is divisible by it. -/
theorem exists_affine_pivot {A : Type u} [CommRing A] (I : Ideal A)
    {T : Scheme.{u}} (f : T ⟶ Spec (.of A))
    (hf : cartierPullback (affineCenter A I) f) (x : T) :
    ∃ U : T.affineOpens, x ∈ U.1 ∧ ∃ a : I,
      IsRegular (affineBaseMap f U a) ∧
        ∀ b : I, affineBaseMap f U a ∣ affineBaseMap f U b := by
  obtain ⟨U, hU, hxU, r, hr, hJ⟩ :=
    Scheme.Hom.exists_affine_regular_idealGenerator_of_isLocallyRankOne
      ((affineCenter A I).comap f).subschemeι hf x
  have hgen : I.map (affineBaseMap f U) = Ideal.span {r} := by
    rw [← affineCenter_comap_ideal I f ⟨U, hU⟩]
    exact ((affineCenter A I).comap f).ker_subschemeι_app ⟨U, hU⟩ ▸ hJ
  have hreg : IsRegular r := (Commute.isRegular_iff (Commute.all r)).mpr hr.isLeftRegular
  obtain ⟨q, hq, hqtop⟩ := quotientCoefficients_span I (affineBaseMap f U) r hreg hgen
  rw [← iSup_basicOpen_of_span_eq_top U (Set.range q) hqtop] at hxU
  obtain ⟨s, hs⟩ := Opens.mem_iSup.mp hxU
  obtain ⟨⟨a, rfl⟩, hxa⟩ := Opens.mem_iSup.mp hs
  let V := T.affineBasicOpen (U := ⟨U, hU⟩) (q a)
  let ρ : Γ(T, U) →+* Γ(T, V) :=
    (T.presheaf.map (homOfLE (T.basicOpen_le (q a))).op).hom
  let : Algebra Γ(T, U) Γ(T, V) := ρ.toAlgebra
  let : IsLocalization.Away (q a) Γ(T, V) := hU.isLocalization_basicOpen (q a)
  have hrV : IsRegular (ρ r) :=
    isRegular_iff_mem_nonZeroDivisors.mpr
      (IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers (q a)) Γ(T, V)
        hreg.mem_nonZeroDivisors)
  have hunit : IsUnit (ρ (q a)) := IsLocalization.Away.algebraMap_isUnit (q a)
  have heq (b : I) : affineBaseMap f V b = ρ r * ρ (q b) := by
    calc
      affineBaseMap f V b = ρ (affineBaseMap f U b) :=
        (congrArg (fun F : A →+* Γ(T, V) => F b)
          (affineBaseMap_restrict f (T.basicOpen_le (q a)))).symm
      _ = ρ r * ρ (q b) := (congrArg ρ (hq b)).trans (map_mul ρ r (q b))
  refine ⟨V, hxa, a, ?_, ?_⟩
  · rw [heq a]
    exact hrV.mul hunit.isRegular
  · intro b
    obtain ⟨u, hu⟩ := hunit
    refine ⟨(↑u⁻¹ : Γ(T, V)) * ρ (q b), ?_⟩
    rw [heq a, heq b, ← hu]
    simp [mul_assoc]

/-- The affine open cover produced from the actual Cartier inverse-image ideal. Its charts
carry an original-ideal pivot which is regular and divides every original-ideal image. -/
def affineLiftingCover {A : Type u} [CommRing A] (I : Ideal A)
    {T : Scheme.{u}} (f : T ⟶ Spec (.of A))
    (hf : cartierPullback (affineCenter A I) f) : T.AffineOpenCover where
  I₀ := {p : T.affineOpens × I // IsRegular (affineBaseMap f p.1 p.2) ∧
    ∀ b : I, affineBaseMap f p.1 p.2 ∣ affineBaseMap f p.1 b}
  X p := Γ(T, p.1.1)
  f p := p.1.1.2.fromSpec
  idx x :=
    let h := exists_affine_pivot I f hf x
    ⟨⟨h.choose, h.choose_spec.2.choose⟩, h.choose_spec.2.choose_spec⟩
  covers x := by
    dsimp
    rw [IsAffineOpen.range_fromSpec]
    exact (exists_affine_pivot I f hf x).choose_spec.1

/-- The scalar map on an affine open gives the original scheme map after `Spec`. -/
lemma spec_affineBaseMap {A : Type u} [CommRing A] {T : Scheme.{u}}
    (f : T ⟶ Spec (.of A)) (U : T.affineOpens) :
    Spec.map (CommRingCat.ofHom (affineBaseMap f U)) = U.2.fromSpec ≫ f := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f
    (isAffineOpen_top (Spec (.of A))) U.2 (by simp)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  exact h

/-- The actual local factorization into the pivot's saturated chart in the native Rees Proj. -/
def affinePivotLift {A S : Type u} [CommRing A] [CommRing S]
    (I : Ideal A) (a : I) (f : A →+* S) (hreg : IsRegular (f a))
    (hdiv : ∀ b : I, f a ∣ f b) : Spec (.of S) ⟶ affineProj I :=
  Spec.map (CommRingCat.ofHom
    (Localization.Away.SaturatedChart.ringLift I a f hreg hdiv)) ≫ affineProjChart I a

/-- The local factorization has its literal original base map. -/
@[reassoc]
lemma affinePivotLift_map {A S : Type u} [CommRing A] [CommRing S]
    (I : Ideal A) (a : I) (f : A →+* S) (hreg : IsRegular (f a))
    (hdiv : ∀ b : I, f a ∣ f b) :
    affinePivotLift I a f hreg hdiv ≫ affineProjMap I = Spec.map (CommRingCat.ofHom f) := by
  rw [affinePivotLift, Category.assoc, affineProjChart_map, affineChartMap, ← Spec.map_comp]
  congr 1
  ext b
  exact Localization.Away.SaturatedChart.ringLift_algebraMap I a f hreg hdiv b

/-- Each produced affine source chart has an actual factorization of its original map. -/
def affineLiftingCoverLift {A : Type u} [CommRing A] (I : Ideal A)
    {T : Scheme.{u}} (f : T ⟶ Spec (.of A))
    (hf : cartierPullback (affineCenter A I) f) (p : (affineLiftingCover I f hf).I₀) :
    Spec ((affineLiftingCover I f hf).X p) ⟶ affineProj I :=
  affinePivotLift I p.1.2 (affineBaseMap f p.1.1) p.2.1 p.2.2

@[reassoc]
lemma affineLiftingCoverLift_map {A : Type u} [CommRing A] (I : Ideal A)
    {T : Scheme.{u}} (f : T ⟶ Spec (.of A))
    (hf : cartierPullback (affineCenter A I) f) (p : (affineLiftingCover I f hf).I₀) :
    affineLiftingCoverLift I f hf p ≫ affineProjMap I =
      (affineLiftingCover I f hf).f p ≫ f := by
  rw [affineLiftingCoverLift, affinePivotLift_map, spec_affineBaseMap]
  rfl

end AlgebraicGeometry.Scheme.Blowup
