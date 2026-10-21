/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Charts
public import Aglib.AlgebraicGeometry.Gluing.OpenImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.ProjectiveComponents`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`4e5f946b7f8fbe1602cc88becc50ec7eaa3c9af9a5770d3c3d3fe57fe34da57c`.
General reciprocal Away(X) gluing/descent/section comparisons to the existing fixed homogeneous
  projectiveP1, source12–337 and928–1001. No new projective-line carrier is introduced.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

section ProjectiveLineReciprocal

/-!
# The actual projective line glued from two full reciprocal affine charts

This is the general two-chart construction used by interior components in a
resolved split node. It reuses the permanent standard Proj chart equivalence,
transition calculation, and open-pushout comparison. No component enumeration,
resolution, or desired projective-line isomorphism is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.Scheme.ProjectiveLine.Reciprocal
variable (k : Type u) [CommRing k]

/-- The Laurent polynomial ring obtained by inverting `X` in `k[X]`. -/
abbrev Laurent := Localization.Away (X : k[X])
/-- The affine coordinate line `Spec k[X]` over `k`. -/
abbrev affineLine : Scheme.{u} := Spec (.of k[X])
/-- The common chart overlap `Spec (Localization.Away X)`. -/
abbrev gm : Scheme.{u} := Spec (.of (Laurent k))
/-- The image of the polynomial coordinate `X` in the Laurent polynomial ring. -/
def t : Laurent k := algebraMap k[X] _ X
/-- The inverse of the coordinate `t` in the Laurent polynomial ring. -/
def invT : Laurent k := IsLocalization.Away.invSelf (X : k[X])
@[simp] lemma t_mul_invT : t k * invT k = 1 := IsLocalization.Away.mul_invSelf _
@[simp] lemma invT_mul_t : invT k * t k = 1 := by rw [mul_comm, t_mul_invT]
/-- The Laurent coordinate `t` as a unit, with inverse `invT`. -/
def tUnit : (Laurent k)ˣ := ⟨t k, invT k, t_mul_invT k, invT_mul_t k⟩

/-- The `k`-algebra endomorphism of the Laurent ring sending `t` to `invT`. -/
def inversion : Laurent k →ₐ[k] Laurent k :=
  IsLocalization.Away.liftAlgHom (X : k[X]) (f := aeval (invT k)) (by
    exact IsUnit.of_mul_eq_one (t k) (by simp))
@[simp] lemma inversion_t : inversion k (t k) = invT k := by simp [inversion, t]
@[simp] lemma inversion_invT : inversion k (invT k) = t k := by
  have h := congrArg (inversion k) (t_mul_invT k)
  simp only [map_mul, map_one, inversion_t] at h
  calc
    inversion k (invT k) = (t k * invT k) * inversion k (invT k) := by rw [t_mul_invT, one_mul]
    _ = t k := by rw [mul_assoc, h, mul_one]

/-- The involutive `k`-algebra equivalence exchanging `t` and `invT`. -/
def inversionEquiv : Laurent k ≃ₐ[k] Laurent k :=
  AlgEquiv.ofAlgHom (inversion k) (inversion k)
    (by
      apply IsLocalization.algHom_ext (Submonoid.powers (X : k[X]))
      apply Polynomial.algHom_ext
      change inversion k (inversion k (t k)) = t k
      simp)
    (by
      apply IsLocalization.algHom_ext (Submonoid.powers (X : k[X]))
      apply Polynomial.algHom_ext
      change inversion k (inversion k (t k)) = t k
      simp)

/-- The overlap inclusion into the zero chart, induced by localization at `X`. -/
def toZeroChart : gm k ⟶ affineLine k :=
  Spec.map (CommRingCat.ofHom (algebraMap k[X] (Laurent k)))
/-- The overlap inclusion into the infinity chart, sending its coordinate to `invT`. -/
def toInfinityChart : gm k ⟶ affineLine k :=
  Spec.map (CommRingCat.ofHom (aeval (invT k)).toRingHom)
instance toZeroChart_open : IsOpenImmersion (toZeroChart k) :=
  IsOpenImmersion.of_isLocalization (X : k[X])

lemma toInfinityChart_eq : toInfinityChart k =
    (Scheme.Spec.mapIso (inversionEquiv k).toRingEquiv.toCommRingCatIso.op).hom ≫
      toZeroChart k := by
  change Spec.map (CommRingCat.ofHom (aeval (invT k)).toRingHom) =
    Spec.map (CommRingCat.ofHom (inversion k).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k[X] (Laurent k)))
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  change aeval (invT k) p = inversion k (algebraMap k[X] (Laurent k) p)
  simp [inversion]
instance toInfinityChart_open : IsOpenImmersion (toInfinityChart k) := by
  rw [toInfinityChart_eq]
  infer_instance

lemma zeroChart_range : (toZeroChart k).opensRange = PrimeSpectrum.basicOpen (X : k[X]) :=
  Scheme.Hom.opensRange_localizationAway (R := .of k[X]) _
lemma infinityChart_range :
    (toInfinityChart k).opensRange = PrimeSpectrum.basicOpen (X : k[X]) := by
  simp only [toInfinityChart_eq, Scheme.Hom.opensRange_comp_of_isIso, zeroChart_range]

lemma aeval_t : (aeval (t k)).toRingHom = algebraMap k[X] (Laurent k) := by
  have h : aeval (t k) = IsScalarTower.toAlgHom k k[X] (Laurent k) := by
    apply Polynomial.algHom_ext
    simp [t]
  exact congrArg AlgHom.toRingHom h

@[reassoc] lemma transition : toZeroChart k ≫ chart k 0 = toInfinityChart k ≫ chart k 1 := by
  have h := chart_transition k (Laurent k) (tUnit k)
  change Spec.map (CommRingCat.ofHom (aeval (t k)).toRingHom) ≫ chart k 0 = _ at h
  rw [aeval_t] at h
  exact h

lemma chart_preimage_opposite :
    chart k 0 ⁻¹ᵁ (chart k 1).opensRange = (toZeroChart k).opensRange := by
  rw [chart_opensRange, chart_preimage_linear k 0 _ (MvPolynomial.isHomogeneous_X k 1),
    zeroChart_range]
  simp [dehomogenizePolynomial]

/-- The overlap square is the literal fibre product of the two standard charts. -/
lemma overlap_isPullback :
    IsPullback (toInfinityChart k) (toZeroChart k) (chart k 1) (chart k 0) :=
  IsOpenImmersion.isPullback _ _ _ _ (transition k) (chart_preimage_opposite k)

lemma charts_cover (z : projectiveP1 k) :
    (∃ a, chart k 0 a = z) ∨ ∃ b, chart k 1 b = z := by
  obtain ⟨i, a, ha⟩ := chart_covered k z
  fin_cases i
  · exact Or.inl ⟨a, ha⟩
  · exact Or.inr ⟨a, ha⟩

/-- The scheme obtained by gluing two affine lines along the reciprocal overlap maps. -/
abbrev gluing : Scheme.{u} := pushout (toZeroChart k) (toInfinityChart k)
/-- The morphism from the reciprocal gluing induced by the two standard projective charts. -/
def toProjectiveLine : gluing k ⟶ projectiveP1 k :=
  pushout.desc (chart k 0) (chart k 1) (transition k)
instance toProjectiveLine_isIso : IsIso (toProjectiveLine k) :=
  OpenPushoutIso.desc_isIso _ _ _ _ (transition k) (chart_preimage_opposite k) (charts_cover k)
/-- The isomorphism from the reciprocal gluing to the fixed projective line. -/
def gluingIso : gluing k ≅ projectiveP1 k := asIso (toProjectiveLine k)
@[reassoc, simp] lemma gluingIso_zero :
    pushout.inl (toZeroChart k) (toInfinityChart k) ≫ (gluingIso k).hom = chart k 0 := by
  simp [gluingIso, toProjectiveLine]
@[reassoc, simp] lemma gluingIso_infinity :
    pushout.inr (toZeroChart k) (toInfinityChart k) ≫ (gluingIso k).hom = chart k 1 := by
  simp [gluingIso, toProjectiveLine]

variable {Y : Scheme.{u}} (f0 f1 : affineLine k ⟶ Y)
  (h : toZeroChart k ≫ f0 = toInfinityChart k ≫ f1)
/-- Descent of two actual affine-line morphisms under the reciprocal relation. -/
def descend : projectiveP1 k ⟶ Y := (gluingIso k).inv ≫ pushout.desc f0 f1 h
@[reassoc, simp] lemma chart_zero_descend : chart k 0 ≫ descend k f0 f1 h = f0 := by
  rw [← gluingIso_zero k]
  simp only [descend, Category.assoc, Iso.hom_inv_id_assoc, pushout.inl_desc]
@[reassoc, simp] lemma chart_infinity_descend : chart k 1 ≫ descend k f0 f1 h = f1 := by
  rw [← gluingIso_infinity k]
  simp only [descend, Category.assoc, Iso.hom_inv_id_assoc, pushout.inr_desc]

lemma hom_ext {f g : projectiveP1 k ⟶ Y}
    (h0 : chart k 0 ≫ f = chart k 0 ≫ g) (h1 : chart k 1 ≫ f = chart k 1 ≫ g) : f = g := by
  apply (cancel_epi (gluingIso k).hom).mp
  apply pushout.hom_ext
  · simpa only [← Category.assoc, gluingIso_zero] using h0
  · simpa only [← Category.assoc, gluingIso_infinity] using h1

lemma descend_unique (f : projectiveP1 k ⟶ Y)
    (h0 : chart k 0 ≫ f = f0) (h1 : chart k 1 ≫ f = f1) : f = descend k f0 f1 h := by
  apply hom_ext k
  · simpa only [chart_zero_descend] using h0
  · simpa only [chart_infinity_descend] using h1

end AlgebraicGeometry.Scheme.ProjectiveLine.Reciprocal

end -- noncomputable section
end ProjectiveLineReciprocal


section ProjectiveLineComponents

/-! Actual endpoint sections and the closed-component criterion for the
reciprocal projective-line gluing. The latter takes exact pullback charts,
not an embedding or component-count conclusion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.ProjectiveLine.Reciprocal
variable (k : Type u) [CommRing k]

/-- The structure morphism of the affine coordinate line over `Spec k`. -/
def affineBase : affineLine k ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k k[X]))
/-- The structure morphism of the Laurent overlap over `Spec k`. -/
def gmBase : gm k ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (Laurent k)))
@[reassoc] lemma toZeroChart_over : toZeroChart k ≫ affineBase k = gmBase k := by
  rw [toZeroChart, affineBase, gmBase, ← Spec.map_comp]
  congr 1
@[reassoc] lemma toInfinityChart_over : toInfinityChart k ≫ affineBase k = gmBase k := by
  rw [toInfinityChart, affineBase, gmBase, ← Spec.map_comp]
  congr 1
  ext r
  exact (aeval (invT k)).commutes r

/-- The morphism to `Spec k` descended from the structure maps of the two affine charts. -/
def gluingBase : gluing k ⟶ Spec (.of k) :=
  pushout.desc (affineBase k) (affineBase k) (by rw [toZeroChart_over, toInfinityChart_over])
@[reassoc] lemma gluingIso_over : (gluingIso k).hom ≫ structureMap k = gluingBase k := by
  apply pushout.hom_ext
  · rw [← Category.assoc, gluingIso_zero, chart_over, gluingBase, pushout.inl_desc]
    rfl
  · rw [← Category.assoc, gluingIso_infinity, chart_over, gluingBase, pushout.inr_desc]
    rfl

lemma descend_over {Y : Scheme.{u}} (f0 f1 : affineLine k ⟶ Y)
    (h : toZeroChart k ≫ f0 = toInfinityChart k ≫ f1)
    (π : Y ⟶ Spec (.of k)) (h0 : f0 ≫ π = affineBase k) (h1 : f1 ≫ π = affineBase k) :
    descend k f0 f1 h ≫ π = structureMap k := by
  apply hom_ext k
  · rw [← Category.assoc, chart_zero_descend, h0, chart_over]
    rfl
  · rw [← Category.assoc, chart_infinity_descend, h1, chart_over]
    rfl

/-- The literal origin-evaluation morphism into either affine coordinate line. -/
def affineOrigin : Spec (.of k) ⟶ affineLine k := Spec.map (CommRingCat.ofHom (evalRingHom 0))
/-- The section of the projective line obtained from the origin of the zero chart. -/
def zeroSection : Spec (.of k) ⟶ projectiveP1 k := affineOrigin k ≫ chart k 0
/-- The section of the projective line obtained from the origin of the infinity chart. -/
def infinitySection : Spec (.of k) ⟶ projectiveP1 k := affineOrigin k ≫ chart k 1
@[reassoc] lemma affineOrigin_over : affineOrigin k ≫ affineBase k = 𝟙 _ := by
  rw [affineOrigin, affineBase, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((evalRingHom 0).comp (algebraMap k k[X]))) = _
  have h : (evalRingHom (0 : k)).comp (algebraMap k k[X]) = RingHom.id k := by ext; simp
  rw [h]
  exact Spec.map_id (.of k)
@[reassoc] lemma zeroSection_over : zeroSection k ≫ structureMap k = 𝟙 _ := by
  rw [zeroSection, Category.assoc, chart_over]
  exact affineOrigin_over k
@[reassoc] lemma infinitySection_over : infinitySection k ≫ structureMap k = 𝟙 _ := by
  rw [infinitySection, Category.assoc, chart_over]
  exact affineOrigin_over k

instance zeroSection_closed : IsClosedImmersion (zeroSection k) := by
  have : IsClosedImmersion (zeroSection k ≫ structureMap k) := by
    rw [zeroSection_over]
    infer_instance
  exact IsClosedImmersion.of_comp (zeroSection k) (structureMap k)
instance infinitySection_closed : IsClosedImmersion (infinitySection k) := by
  have : IsClosedImmersion (infinitySection k ≫ structureMap k) := by
    rw [infinitySection_over]
    infer_instance
  exact IsClosedImmersion.of_comp (infinitySection k) (structureMap k)

@[reassoc] lemma zeroSection_descend {Y : Scheme.{u}} (f0 f1 : affineLine k ⟶ Y)
    (h : toZeroChart k ≫ f0 = toInfinityChart k ≫ f1) :
    zeroSection k ≫ descend k f0 f1 h = affineOrigin k ≫ f0 := by
  simp only [zeroSection, Category.assoc, chart_zero_descend]
@[reassoc] lemma infinitySection_descend {Y : Scheme.{u}} (f0 f1 : affineLine k ⟶ Y)
    (h : toZeroChart k ≫ f0 = toInfinityChart k ≫ f1) :
    infinitySection k ≫ descend k f0 f1 h = affineOrigin k ≫ f1 := by
  simp only [infinitySection, Category.assoc, chart_infinity_descend]

lemma zeroSection_not_infinity (p : Spec (.of k)) :
    zeroSection k p ∉ (chart k 1).opensRange := by
  change affineOrigin k p ∉ chart k 0 ⁻¹ᵁ (chart k 1).opensRange
  rw [chart_preimage_opposite, zeroChart_range]
  change ¬ ¬ (evalRingHom (0 : k)) X ∈ p.asIdeal
  simp

lemma infinitySection_not_zero (p : Spec (.of k)) :
    infinitySection k p ∉ (chart k 0).opensRange := by
  change affineOrigin k p ∉ chart k 1 ⁻¹ᵁ (chart k 0).opensRange
  rw [chart_opensRange, chart_preimage_linear k 1 _ (MvPolynomial.isHomogeneous_X k 0)]
  simp only [dehomogenizePolynomial, MvPolynomial.eval₂Hom_X']
  change ¬ ¬ (evalRingHom (0 : k)) X ∈ p.asIdeal
  simp

lemma endpoints_disjoint : Disjoint (Set.range (zeroSection k)) (Set.range (infinitySection k)) :=
  by
  rw [Set.disjoint_iff_forall_ne]
  rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ h
  exact zeroSection_not_infinity k p (h ▸ ⟨affineOrigin k q, rfl⟩)

lemma zeroSection_ne_infinity [Nontrivial k] : zeroSection k ≠ infinitySection k := by
  intro h
  obtain ⟨p⟩ := (inferInstance : Nonempty (Spec (.of k)))
  exact zeroSection_not_infinity k p (by rw [h]; exact ⟨affineOrigin k p, rfl⟩)

/-- The two full affine charts of the actual Proj projective line. -/
def chartCover : (projectiveP1 k).OpenCover where
  I₀ := Fin 2
  X := fun _ => affineLine k
  f := chart k
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨chart_covered k, fun _ => inferInstance⟩

/-- Exact local pullback charts, together with closed affine embeddings, imply
injectivity of the global projective-line map. No global count is involved. -/
lemma injective_of_pullbackCharts {Y : Scheme.{u}} (f : projectiveP1 k ⟶ Y)
    (U : Fin 2 → Scheme.{u}) (j : ∀ i, U i ⟶ Y) [∀ i, IsOpenImmersion (j i)]
    (c : ∀ i, affineLine k ⟶ U i) [∀ i, IsClosedImmersion (c i)]
    (sq : ∀ i, IsPullback (c i) (chart k i) (j i) f) : Function.Injective f := by
  intro x y h
  obtain ⟨i, a, rfl⟩ := chart_covered k x
  have ha : j i (c i a) = f y := by
    rw [← Scheme.Hom.comp_apply, (sq i).w, Scheme.Hom.comp_apply, h]
  obtain ⟨p, hp0, hp1⟩ := Scheme.Pullback.exists_preimage_pullback (c i a) y ha
  let b := (sq i).isoPullback.inv p
  have hb : chart k i b = y := by
    change (chart k i) ((sq i).isoPullback.inv p) = y
    rw [← Scheme.Hom.comp_apply, (sq i).isoPullback_inv_snd]
    exact hp1
  have hab : c i a = c i b := by
    apply (j i).isOpenEmbedding.injective
    rw [ha, ← hb, ← Scheme.Hom.comp_apply, ← (sq i).w, Scheme.Hom.comp_apply]
  rw [(c i).isClosedEmbedding.injective hab, hb]

/-- A descended P1-map into a separated k-scheme is a closed immersion when
its two source charts are exactly pullbacks of open target charts and their
chart maps are closed immersions. Properness is derived from actual P1. -/
lemma closedImmersion_of_pullbackCharts {Y : Scheme.{u}} (f : projectiveP1 k ⟶ Y)
    (π : Y ⟶ Spec (.of k)) [IsSeparated π] («over» : f ≫ π = structureMap k)
    (U : Fin 2 → Scheme.{u}) (j : ∀ i, U i ⟶ Y) [∀ i, IsOpenImmersion (j i)]
    (c : ∀ i, affineLine k ⟶ U i) [∀ i, IsClosedImmersion (c i)]
    (sq : ∀ i, IsPullback (c i) (chart k i) (j i) f) : IsClosedImmersion f := by
  have : IsProper (f ≫ π) := by rw [«over»]; infer_instance
  have : IsProper f := IsProper.of_comp f π
  have : SurjectiveOnStalks f := by
    apply IsZariskiLocalAtSource.of_openCover (P := @SurjectiveOnStalks) (chartCover k)
    intro i
    change SurjectiveOnStalks (chart k i ≫ f)
    rw [← (sq i).w]
    infer_instance
  exact ⟨Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap f.continuous
    (injective_of_pullbackCharts k f U j c sq) f.isClosedMap⟩

lemma descend_closedImmersion {Y : Scheme.{u}} (f0 f1 : affineLine k ⟶ Y)
    (h : toZeroChart k ≫ f0 = toInfinityChart k ≫ f1)
    (π : Y ⟶ Spec (.of k)) [IsSeparated π]
    (h0 : f0 ≫ π = affineBase k) (h1 : f1 ≫ π = affineBase k)
    (U : Fin 2 → Scheme.{u}) (j : ∀ i, U i ⟶ Y) [∀ i, IsOpenImmersion (j i)]
    (c : ∀ i, affineLine k ⟶ U i) [∀ i, IsClosedImmersion (c i)]
    (sq : ∀ i, IsPullback (c i) (chart k i) (j i) (descend k f0 f1 h)) :
    IsClosedImmersion (descend k f0 f1 h) :=
  closedImmersion_of_pullbackCharts k _ π (descend_over k f0 f1 h π h0 h1) U j c sq

end AlgebraicGeometry.Scheme.ProjectiveLine.Reciprocal

end -- noncomputable section
end ProjectiveLineComponents




section ProjectiveLineChartPullbacks

/-! Exact target-chart pullbacks from the actual opposite-chart preimages.
No global pullback square or embedding is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.ProjectiveLine.Reciprocal
universe u
variable (k : Type u) [CommRing k]
  {U0 U1 Y : Scheme.{u}} (j0 : U0 ⟶ Y) (j1 : U1 ⟶ Y)
  [IsOpenImmersion j0] [IsOpenImmersion j1]
  (c0 : affineLine k ⟶ U0) (c1 : affineLine k ⟶ U1)
  (h : toZeroChart k ≫ (c0 ≫ j0) = toInfinityChart k ≫ (c1 ≫ j1))

omit [IsOpenImmersion j1] in
lemma descend_preimage_zero
    (h1 : (c1 ≫ j1) ⁻¹' Set.range j0 = Set.range (toInfinityChart k)) :
    descend k (c0 ≫ j0) (c1 ≫ j1) h ⁻¹ᵁ j0.opensRange = (chart k 0).opensRange := by
  ext x
  change _ ∈ Set.range j0 ↔ x ∈ Set.range (chart k 0)
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ | ⟨a, rfl⟩ := charts_cover k x
    · exact ⟨a, rfl⟩
    · have ha : a ∈ (c1 ≫ j1) ⁻¹' Set.range j0 := by
        change (c1 ≫ j1) a ∈ Set.range j0
        simpa only [← Scheme.Hom.comp_apply, chart_infinity_descend] using hx
      rw [h1] at ha
      obtain ⟨b, rfl⟩ := ha
      refine ⟨toZeroChart k b, ?_⟩
      exact congrArg (fun f : gm k ⟶ projectiveP1 k => f b) (transition k)
  · rintro ⟨a, rfl⟩
    refine ⟨c0 a, ?_⟩
    change (c0 ≫ j0) a = _
    rw [← Scheme.Hom.comp_apply, chart_zero_descend]

omit [IsOpenImmersion j0] in
lemma descend_preimage_infinity
    (h0 : (c0 ≫ j0) ⁻¹' Set.range j1 = Set.range (toZeroChart k)) :
    descend k (c0 ≫ j0) (c1 ≫ j1) h ⁻¹ᵁ j1.opensRange = (chart k 1).opensRange := by
  ext x
  change _ ∈ Set.range j1 ↔ x ∈ Set.range (chart k 1)
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ | ⟨a, rfl⟩ := charts_cover k x
    · have ha : a ∈ (c0 ≫ j0) ⁻¹' Set.range j1 := by
        change (c0 ≫ j0) a ∈ Set.range j1
        simpa only [← Scheme.Hom.comp_apply, chart_zero_descend] using hx
      rw [h0] at ha
      obtain ⟨b, rfl⟩ := ha
      refine ⟨toInfinityChart k b, ?_⟩
      exact congrArg (fun f : gm k ⟶ projectiveP1 k => f b) (transition k).symm
    · exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨c1 a, ?_⟩
    change (c1 ≫ j1) a = _
    rw [← Scheme.Hom.comp_apply, chart_infinity_descend]

omit [IsOpenImmersion j1] in
lemma descend_zero_isPullback
    (h1 : (c1 ≫ j1) ⁻¹' Set.range j0 = Set.range (toInfinityChart k)) :
    IsPullback c0 (chart k 0) j0 (descend k (c0 ≫ j0) (c1 ≫ j1) h) :=
  IsOpenImmersion.isPullback _ _ _ _ (chart_zero_descend k _ _ h)
    (descend_preimage_zero k j0 j1 c0 c1 h h1)

omit [IsOpenImmersion j0] in
lemma descend_infinity_isPullback
    (h0 : (c0 ≫ j0) ⁻¹' Set.range j1 = Set.range (toZeroChart k)) :
    IsPullback c1 (chart k 1) j1 (descend k (c0 ≫ j0) (c1 ≫ j1) h) :=
  IsOpenImmersion.isPullback _ _ _ _ (chart_infinity_descend k _ _ h)
    (descend_preimage_infinity k j0 j1 c0 c1 h h0)

end AlgebraicGeometry.Scheme.ProjectiveLine.Reciprocal

end -- noncomputable section
end ProjectiveLineChartPullbacks
