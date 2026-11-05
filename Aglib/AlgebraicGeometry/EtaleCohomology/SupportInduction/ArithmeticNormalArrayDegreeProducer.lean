/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.ArithmeticNormalHigherProducer
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.AffineFixedCoefficientStageReturn
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.AffineChartResidueSupport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.CoefficientCartesianTargetZero
public import Aglib.AlgebraicGeometry.Limits.ConnectedCoproduct
public import Aglib.AlgebraicGeometry.Morphisms.Finite.Coproduct
public import Aglib.CategoryTheory.Limits.Shapes.TwoAxisPullbackFamily

/-! # Actual pointed return from a finite family of normal arrows

One genuine coefficient and its actual finite detector are chosen on the
whole coefficient coproduct. Every component uses the etale restriction of
that same coefficient. The normal-domain producer supplies the component
zero internally, and the canonical whole finite-source return recovers the
original class. No local zero or component vanishing producer is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients TwoFieldEffacement
open AlgebraicGeometry.Scheme.EtaleCohomology.Finite
open AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u eY

attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- A finite normal-arrow family gives actual original-class target zero.
The actual higher producer uses only lower-degree and smaller-rank induction. -/
theorem exists_arithmetic_normal_array_affine_stage_degree_zero_of_lower_rank
    (k : ℕ) (hk : 2 ≤ k)
    (houter : ∀ r : ℕ, 1 ≤ r → r < k → ArithmeticCurveModuleInjectiveVanishing.{u} r)
    (d : ℕ) (ih : ∀ r < d, ArithmeticPointedCurveModuleEffacement.{u} k r)
    (A B : Type u) [CommRing A] [CommRing B]
    {ι : Type u} [Finite ι] (R S : ι → Type u)
    [∀ i, CommRing (R i)] [∀ i, Algebra.FiniteType ℤ (R i)]
    [∀ i, CommRing (S i)] [∀ i, IsDomain (S i)] [∀ i, IsIntegrallyClosed (S i)]
    [∀ i, Algebra.FiniteType ℤ (S i)]
    (hd : ∀ i, ringKrullDim (S i) ≤ (d : ℕ))
    (r : ∀ i, R i →+* S i)
    (s : ∀ i, A →+* R i) (t : ∀ i, B →+* S i)
    (hfinite : ∀ i, (s i).Finite)
    {X Y : Scheme.{u}} (p : X ⟶ Spec (.of A))
    [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
    [QuasiCompact p] [QuasiSeparated p]
    (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ p = 𝟙 _)
    (haff : ∀ (F : Type u) [Field F] (z : Spec (.of F) ⟶ Spec (.of A)),
      IsAffine (pullback p z : Scheme.{u}))
    (bmap : A →+* B)
    (hsquare : ∀ i, (r i).comp (s i) = (t i).comp bmap)
    (a : Y ⟶ X) (b : Y ⟶ Spec (.of B))
    (H : IsPullback a b p (Spec.map (CommRingCat.ofHom bmap)))
    (hgfinite : IsFinite (Sigma.desc (fun i => Spec.map (CommRingCat.ofHom (t i)))))
    (hgsurj : Surjective (Sigma.desc (fun i => Spec.map (CommRingCat.ofHom (t i)))))
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : A))
    (I : ModuleSheaf (Spec (.of B)) (ULift.{u + 1} (ZMod n))) [Injective I]
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    (c : Sheaf.H.{eY} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (.of B))
        (ULift.{u + 1} (ZMod n)))).obj I)) k)
    (R₀ Ω : Type u) [CommRing R₀] [Field Ω] [Algebra R₀ Ω] [IsSepClosed Ω]
    (e : Spec (.of R₀) ⟶ X)
    (hpoint : (Spec.algebraMap R₀ Ω ≫ e) (IsLocalRing.closedPoint Ω) ∈ Set.range σ) :
    ∃ V : GeometricEtaleNeighborhood R₀ Ω,
      cohomologyPullback.{u, eY, u + 2}
        (pullback.snd (Spec.algebraMap R₀ V.algebra ≫ e) a) _ k c = 0 := by
  classical
  let rs (i : ι) := Spec.map (CommRingCat.ofHom (s i))
  let ts (i : ι) := Spec.map (CommRingCat.ofHom (t i))
  let ns (i : ι) := Spec.map (CommRingCat.ofHom (r i))
  have hsq (i : ι) : ns i ≫ rs i = ts i ≫ Spec.map (CommRingCat.ofHom bmap) := by
    simp only [rs, ts, ns, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (hsquare i))
  let G (i : ι) := pullback p (rs i)
  let q (i : ι) : G i ⟶ Spec (.of (R i)) := pullback.snd p (rs i)
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{u} 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  let : ∀ i, SmoothOfRelativeDimension 1 (q i) := fun i =>
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension.{u} 1)
      (IsPullback.of_hasPullback p (rs i)) (inferInstance : SmoothOfRelativeDimension 1 p)
  let f : (∐ G) ⟶ X := Sigma.desc (fun i => pullback.fst p (rs i))
  let g : (∐ fun i => Spec (.of (S i))) ⟶ Spec (.of B) := Sigma.desc ts
  let v := TwoAxisPullbackFamily.targetMap H rs ts ns hsq
  have hv : v ≫ f = pullback.snd g b ≫ a :=
    TwoAxisPullbackFamily.targetMap_over H rs ts ns hsq
  let : ∀ i, IsFinite (rs i) := fun i => (IsFinite.SpecMap_iff _).mpr (hfinite i)
  let : IsFinite f := AlgebraicGeometry.isFinite_sigmaDesc G
    (fun i => pullback.fst p (rs i))
  let : IsFinite g := hgfinite
  let : Surjective g := hgsurj
  obtain ⟨J, hJ, α, hdetect⟩ :=
    exists_moduleInjective_finite_refinement_detector.{u, u + 2, u + 2}
    g (ULift.{u + 1} (ZMod n)) I
  let : Injective J := hJ
  let cJ := moduleFiniteImageClass.{u, eY, u + 2} g (pullback.snd g b) b
    (pullback.fst g b) (pullback.condition (f := g) (g := b)).symm
    (ULift.{u + 1} (ZMod n)) I J α k c
  let fO := pullback.snd f e
  let L := limitSourceRing R₀ Ω fO
  let := limitSourceAlgebra R₀ Ω fO
  let : Module.Finite (GeometricEtaleColimit R₀ Ω) L :=
    limitSource_moduleFinite R₀ Ω fO
  let : ∀ i : MaximalSpectrum L,
      IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal)) :=
    fun i => HenselianLocalRing.residueField_isSepClosed_localizationAtPrime
      (GeometricEtaleColimit R₀ Ω) L i.asIdeal
  have hcharts (i : MaximalSpectrum L) :
      ∃ (U : (∐ G).Etale)
        (z : Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶ U.left),
        z ≫ U.hom = limitResidueMap R₀ Ω fO i ≫ pullback.fst f e ∧
        cohomologyPullback.{u, u + 2, u + 2} (pullback.snd U.hom v) _ k cJ = 0 := by
    let κ := IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal)
    let y : Spec (.of κ) ⟶ ∐ G := limitResidueMap R₀ Ω fO i ≫ pullback.fst f e
    obtain ⟨j, yj, hyj⟩ := Scheme.Hom.exists_factor_sigma_of_connected G y
    let σj := normalModelSection p σ hσ (rs j)
    have hσj : σj ≫ q j = 𝟙 _ := normalModelSection_over p σ hσ (rs j)
    have hySupport : Set.range (yj ≫ pullback.fst p (rs j)) ⊆ Set.range σ := by
      have hh : yj ≫ pullback.fst p (rs j) = y ≫ f := by
        rw [← hyj, Category.assoc, Sigma.ι_comp_desc]
      rw [hh]
      exact finiteChartLimitResidueMap_range_subset R₀ Ω f e (Set.range σ) hpoint i
    have hysection : yj = (yj ≫ q j) ≫ σj := by
      apply pullback.hom_ext
      · rw [Category.assoc, normalModelSection_source]
        simpa only [Category.assoc] using
          pullback_section_condition_of_reduced_range_subset p (rs j) σ hσ yj hySupport
      · rw [Category.assoc, hσj, Category.comp_id]
    let cj := TwoAxisPullbackFamily.componentInclusion H rs ts ns hsq j
    let bj := pullback.snd (q j) (ns j)
    let aj := pullback.fst (q j) (ns j)
    let ιj := Sigma.ι (fun j => Spec (.of (S j))) j
    have hw : cj ≫ pullback.fst g b = bj ≫ ιj :=
      TwoAxisPullbackFamily.componentInclusion_fst H rs ts ns hsq j
    let Jj := (moduleInverseImage ιj (ULift.{u + 1} (ZMod n))).obj J
    let : Injective Jj := moduleInverseImage_etale_injective ιj _ J
    let dj := moduleCoefficientComponentClass.{u, u + 2, u + 2}
      ιj cj (pullback.fst g b) bj hw (ULift.{u + 1} (ZMod n)) J k cJ
    have hunitj : IsUnit (n : R j) := by
      simpa only [map_natCast] using hunit.map (s j)
    have haffj (F : Type u) [Field F] (z : Spec (.of F) ⟶ Spec (.of (R j))) :
        IsAffine (pullback (q j) z : Scheme.{u}) := by
      let : IsAffine (pullback p (z ≫ rs j) : Scheme.{u}) := haff F (z ≫ rs j)
      exact IsAffine.of_isIso (pullbackLeftPullbackSndIso p (rs j) z).hom
    obtain ⟨U, z, hz, hc⟩ := exists_arithmetic_normal_coefficient_higher_refinement_of_lower_rank
      k hk houter d ih (R j) (S j) (hd j)
      (q j) σj hσj haffj (ns j) aj bj (.of_hasPullback (q j) (ns j))
      n hn hunitj Jj dj κ (yj ≫ q j)
    let : Etale U.hom := U.prop
    let U' : (∐ G).Etale := Scheme.Etale.mk (U.hom ≫ Sigma.ι G j)
    refine ⟨U', z, ?_, ?_⟩
    · change z ≫ (U.hom ≫ Sigma.ι G j) = y
      rw [← Category.assoc, hz, ← hysection, hyj]
    · exact moduleCoefficientComponentClass_target_zero
        ιj cj (pullback.fst g b) bj hw (Sigma.ι G j) v aj
        (TwoAxisPullbackFamily.targetComponentSquare H rs ts ns hsq j)
        U.hom (ULift.{u + 1} (ZMod n)) J k cJ hc
  choose U z hz hc using hcharts
  obtain ⟨V, _, _, _, hV⟩ := exists_affine_stage_zero_of_fixed_coefficient
    R₀ Ω f e g b a v hv (ULift.{u + 1} (ZMod n)) I J α
    (fun k b₀ b₁ H q d hd => hdetect k b₀ b₁ H q d hd) U z hz k c hc
  exact ⟨V, hV⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
