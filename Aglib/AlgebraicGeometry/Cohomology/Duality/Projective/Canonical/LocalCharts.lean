/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Smooth.RegularKernel
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.SmoothRank
public import Aglib.AlgebraicGeometry.Spec.Localization
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Regular affine charts for a smooth closed source

At each point of a closed immersion between schemes smooth over the same
base, principal refinements give the original affine surjection with a
weakly regular kernel list. Both relative differential frames have the
prescribed smooth dimensions. All chart arrows and their commuting squares
are retained; the construction requires no global inequality of dimensions.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ Y) (n d : ℕ) (x : X)

/-- A regular affine chart of the given closed immersion, with its actual
ambient and source maps to a common affine base. -/
structure SmoothClosedImmersionLocalChart where
  /-- The coordinate ring of the affine base chart. -/
  R : CommRingCat.{u}
  /-- The coordinate ring of the affine ambient chart. -/
  A : CommRingCat.{u}
  /-- The coordinate ring of the affine source chart. -/
  B : CommRingCat.{u}
  /-- The ring map from the base chart to the ambient chart. -/
  α : R ⟶ A
  /-- The surjective ring map from the ambient chart to the source chart. -/
  σ : A ⟶ B
  surjective : Function.Surjective σ
  /-- The open immersion of the affine base chart into `Y`. -/
  jY : Spec R ⟶ Y
  /-- The open immersion of the affine ambient chart into `P`. -/
  jP : Spec A ⟶ P
  /-- The open immersion of the affine source chart into `X`. -/
  jX : Spec B ⟶ X
  openY : IsOpenImmersion jY
  openP : IsOpenImmersion jP
  openX : IsOpenImmersion jX
  ambientSquare : Spec.map α ≫ jY = jP ≫ p
  closedSquare : Spec.map σ ≫ jP = jX ≫ i
  cartesian : IsPullback jX (Spec.map σ) i jP
  /-- The point of `Spec B` mapping to `x` under `jX`. -/
  point : PrimeSpectrum B
  point_eq : jX point = x
  /-- The weakly regular list in `A` generating the kernel of `σ`. -/
  regularList : List A
  weaklyRegular : RingTheory.Sequence.IsWeaklyRegular A regularList
  kernel : Ideal.ofList regularList = RingHom.ker σ.hom
  ambientSmooth : RingHom.IsStandardSmoothOfRelativeDimension n α.hom
  sourceSmooth : RingHom.IsStandardSmoothOfRelativeDimension d (α ≫ σ).hom

namespace SmoothClosedImmersionLocalChart

variable {i p n d x} (C : SmoothClosedImmersionLocalChart i p n d x)

/-- The ambient frame belongs to the original relative differential module. -/
def ambientBasis : Module.Basis (Fin n) C.A (CommRingCat.KaehlerDifferential C.α) := by
  letI := C.α.hom.toAlgebra
  letI := C.ambientSmooth.toAlgebra
  exact KaehlerDifferential.standardSmoothBasis C.R C.A n

/-- The source frame belongs to the original relative differential module. -/
def sourceBasis : Module.Basis (Fin d) C.B (CommRingCat.KaehlerDifferential (C.α ≫ C.σ)) := by
  letI := (C.α ≫ C.σ).hom.toAlgebra
  letI := C.sourceSmooth.toAlgebra
  exact KaehlerDifferential.standardSmoothBasis C.R C.B d

theorem ambientFormallySmooth : C.α.hom.FormallySmooth :=
  C.ambientSmooth.isStandardSmooth.smooth.formallySmooth

theorem sourceFormallySmooth : (C.α ≫ C.σ).hom.FormallySmooth :=
  C.sourceSmooth.isStandardSmooth.smooth.formallySmooth

end SmoothClosedImmersionLocalChart

private theorem exists_local_standard
    {R B : CommRingCat.{u}} (β : R ⟶ B) (d : ℕ)
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d) β.hom)
    (q : PrimeSpectrum B) :
    ∃ b : B, b ∉ q.asIdeal ∧ RingHom.IsStandardSmoothOfRelativeDimension d
      ((algebraMap B (Localization.Away b)).comp β.hom) := by
  obtain ⟨S, hS, hstd⟩ := h
  have hex : ∃ b ∈ S, b ∉ q.asIdeal := by
    by_contra! h
    have hle : Ideal.span S ≤ q.asIdeal := Ideal.span_le.mpr h
    rw [hS] at hle
    exact q.isPrime.ne_top (top_le_iff.mp hle)
  obtain ⟨b, hb, hq⟩ := hex
  exact ⟨b, hq, hstd b hb⟩

private theorem exists_refined_chart
    {R A B : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B)
    (hσ : Function.Surjective σ)
    (hA : RingHom.IsStandardSmoothOfRelativeDimension n α.hom)
    (hB : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d) (α ≫ σ).hom)
    (jY : Spec R ⟶ Y) (jP : Spec A ⟶ P) (jX : Spec B ⟶ X)
    [IsOpenImmersion jY] [IsOpenImmersion jP] [IsOpenImmersion jX]
    (hP : Spec.map α ≫ jY = jP ≫ p)
    (hX : Spec.map σ ≫ jP = jX ≫ i)
    (hcart : IsPullback jX (Spec.map σ) i jP)
    (q : PrimeSpectrum B) (hq : jX q = x) :
    Nonempty (SmoothClosedImmersionLocalChart i p n d x) := by
  let : Algebra R A := α.hom.toAlgebra
  let : Algebra R B := (α ≫ σ).hom.toAlgebra
  let φ : A →ₐ[R] B := ⟨σ.hom, fun _ => rfl⟩
  obtain ⟨b, hb, hbstd⟩ := exists_local_standard (α ≫ σ) d hB q
  obtain ⟨a, rfl⟩ := hσ b
  let A₁ := Localization.Away a
  let B₁ := Localization.Away (φ a)
  let φ₁ : A₁ →ₐ[R] B₁ := IsLocalization.Away.mapₐ A₁ B₁ φ a
  have hφ₁ : Function.Surjective φ₁ :=
    IsLocalization.Away.mapₐ_surjective_of_surjective a hσ
  have hA₁ : RingHom.IsStandardSmoothOfRelativeDimension n (algebraMap R A₁) := by
    rw [IsScalarTower.algebraMap_eq R A A₁]
    exact (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway
      n).right A₁ a α.hom hA
  have hB₁ : RingHom.IsStandardSmoothOfRelativeDimension d (algebraMap R B₁) := by
    rw [IsScalarTower.algebraMap_eq R B B₁, RingHom.algebraMap_toAlgebra]
    exact hbstd
  let : Algebra.Smooth R A₁ :=
    RingHom.smooth_algebraMap.mp hA₁.isStandardSmooth.smooth
  let : Algebra.Smooth R B₁ :=
    RingHom.smooth_algebraMap.mp hB₁.isStandardSmooth.smooth
  obtain ⟨q₁, hq₁⟩ : ∃ q₁ : PrimeSpectrum B₁,
      PrimeSpectrum.comap (algebraMap B B₁) q₁ = q := by
    change q ∈ Set.range (PrimeSpectrum.comap (algebraMap B B₁))
    rw [PrimeSpectrum.localization_away_comap_range B₁ (φ a)]
    exact hb
  obtain ⟨a₁, ha₁, s, hs, hker⟩ :=
    Algebra.Smooth.exists_away_regular_kernel_of_surjective φ₁ hφ₁ q₁
  let A₂ := Localization.Away a₁
  let B₂ := Localization.Away (φ₁ a₁)
  let φ₂ : A₂ →ₐ[R] B₂ := IsLocalization.Away.mapₐ A₂ B₂ φ₁ a₁
  have hφ₂ : Function.Surjective φ₂ :=
    IsLocalization.Away.mapₐ_surjective_of_surjective a₁ hφ₁
  have hA₂ : RingHom.IsStandardSmoothOfRelativeDimension n (algebraMap R A₂) := by
    rw [IsScalarTower.algebraMap_eq R A₁ A₂]
    exact (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway
      n).right A₂ a₁ (algebraMap R A₁) hA₁
  have hB₂ : RingHom.IsStandardSmoothOfRelativeDimension d (algebraMap R B₂) := by
    rw [IsScalarTower.algebraMap_eq R B₁ B₂]
    exact (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway
      d).right B₂ (φ₁ a₁) (algebraMap R B₁) hB₁
  obtain ⟨q₂, hq₂⟩ : ∃ q₂ : PrimeSpectrum B₂,
      PrimeSpectrum.comap (algebraMap B₁ B₂) q₂ = q₁ := by
    change q₁ ∈ Set.range (PrimeSpectrum.comap (algebraMap B₁ B₂))
    rw [PrimeSpectrum.localization_away_comap_range B₂ (φ₁ a₁)]
    exact ha₁
  let a₀₁ : A ⟶ CommRingCat.of A₁ := CommRingCat.ofHom (algebraMap A A₁)
  let a₁₂ : CommRingCat.of A₁ ⟶ CommRingCat.of A₂ := CommRingCat.ofHom (algebraMap A₁ A₂)
  let b₀₁ : B ⟶ CommRingCat.of B₁ := CommRingCat.ofHom (algebraMap B B₁)
  let b₁₂ : CommRingCat.of B₁ ⟶ CommRingCat.of B₂ := CommRingCat.ofHom (algebraMap B₁ B₂)
  let α₂ : R ⟶ CommRingCat.of A₂ := CommRingCat.ofHom (algebraMap R A₂)
  let σ₂ : CommRingCat.of A₂ ⟶ CommRingCat.of B₂ := CommRingCat.ofHom φ₂.toRingHom
  have hα : α ≫ a₀₁ ≫ a₁₂ = α₂ := by
    ext z
    exact (IsScalarTower.algebraMap_apply R A₁ A₂ z).symm
  have hβ : (α₂ ≫ σ₂).hom = algebraMap R B₂ := φ₂.comp_algebraMap
  have hσsquare : σ ≫ b₀₁ ≫ b₁₂ = a₀₁ ≫ a₁₂ ≫ σ₂ := by
    ext z
    change algebraMap B₁ B₂ (algebraMap B B₁ (φ z)) =
      IsLocalization.Away.map A₂ B₂ φ₁.toRingHom a₁
        (algebraMap A₁ A₂ (algebraMap A A₁ z))
    rw [IsLocalization.Away.map, IsLocalization.map_eq]
    change algebraMap B₁ B₂ (algebraMap B B₁ (φ z)) =
      algebraMap B₁ B₂ (IsLocalization.Away.map A₁ B₁ φ.toRingHom a
        (algebraMap A A₁ z))
    rw [IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  refine ⟨{
    R := R
    A := CommRingCat.of A₂
    B := CommRingCat.of B₂
    α := α₂
    σ := σ₂
    surjective := hφ₂
    jY := jY
    jP := Spec.map a₁₂ ≫ Spec.map a₀₁ ≫ jP
    jX := Spec.map b₁₂ ≫ Spec.map b₀₁ ≫ jX
    openY := inferInstance
    openP := inferInstance
    openX := inferInstance
    ambientSquare := ?_
    closedSquare := ?_
    cartesian := ?_
    point := q₂
    point_eq := ?_
    regularList := s
    weaklyRegular := hs.1
    kernel := hker.symm
    ambientSmooth := hA₂
    sourceSmooth := hβ.symm ▸ hB₂ }⟩
  · rw [← hα, Spec.map_comp, Spec.map_comp]
    simp only [Category.assoc, hP]
  · have h := congrArg (fun f => Spec.map f ≫ jP) hσsquare
    simp only [Spec.map_comp, Category.assoc] at h
    simpa only [hX, Category.assoc] using h.symm
  · have hc₁ := (Scheme.isPullback_specMap_localizationAway σ a).flip
    have hc₂ := (Scheme.isPullback_specMap_localizationAway
      (CommRingCat.ofHom φ₁.toRingHom) a₁).flip
    exact hc₂.paste_horiz (hc₁.paste_horiz hcart)
  · change jX (PrimeSpectrum.comap (algebraMap B B₁)
      (PrimeSpectrum.comap (algebraMap B₁ B₂) q₂)) = x
    rw [hq₂, hq₁, hq]

/-- Every point of a smooth closed source has a regular affine chart with the
prescribed ambient and source differential ranks. -/
theorem exists_smoothClosedImmersionLocalChart
    [IsClosedImmersion i] [SmoothOfRelativeDimension n p]
    [SmoothOfRelativeDimension d (i ≫ p)] :
    Nonempty (SmoothClosedImmersionLocalChart i p n d x) := by
  obtain ⟨U, hU, V, hV, hxV, e, hα⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := n) (f := p) (i x)
  let W := i ⁻¹ᵁ V
  have hW : IsAffineOpen W := hV.preimage i
  have hxW : x ∈ W := hxV
  let α := p.appLE U V e
  let σ := i.app V
  have ew : W ≤ (i ≫ p) ⁻¹ᵁ U := by
    intro y hy
    exact e hy
  have hcomp : (i ≫ p).appLE U W ew = α ≫ σ := by
    change (i ≫ p).appLE U W ew = p.appLE U V e ≫ i.app V
    rw [Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE i p U V W e le_rfl).symm
  have hβ : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d)
      (α ≫ σ).hom := by
    rw [← hcomp]
    exact HasRingHomProperty.appLE (@SmoothOfRelativeDimension d) (i ≫ p)
      inferInstance ⟨U, hU⟩ ⟨W, hW⟩ ew
  have hclosed : Spec.map σ ≫ hV.fromSpec = hW.fromSpec ≫ i := by
    change Spec.map (i.app V) ≫ hV.fromSpec = hW.fromSpec ≫ i
    rw [Scheme.Hom.app_eq_appLE]
    exact IsAffineOpen.SpecMap_appLE_fromSpec i hV hW le_rfl
  have hcart : IsPullback hW.fromSpec (Spec.map σ) i hV.fromSpec :=
    (IsOpenImmersion.isPullback (Spec.map σ) hW.fromSpec hV.fromSpec i hclosed.symm
      (by rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec])).flip
  exact exists_refined_chart i p n d x α σ (i.app_surjective V hV) hα hβ
    hU.fromSpec hV.fromSpec hW.fromSpec
    (IsAffineOpen.SpecMap_appLE_fromSpec p hU hV e)
    hclosed hcart
    (hW.primeIdealOf ⟨x, hxW⟩) (hW.fromSpec_primeIdealOf ⟨x, hxW⟩)

/-- A selected regular affine chart; existence is proved from native smoothness. -/
def smoothClosedImmersionLocalChart
    [IsClosedImmersion i] [SmoothOfRelativeDimension n p]
    [SmoothOfRelativeDimension d (i ≫ p)] :
    SmoothClosedImmersionLocalChart i p n d x :=
  Classical.choice (exists_smoothClosedImmersionLocalChart i p n d x)

end AlgebraicGeometry.Scheme.Modules.Differentials
