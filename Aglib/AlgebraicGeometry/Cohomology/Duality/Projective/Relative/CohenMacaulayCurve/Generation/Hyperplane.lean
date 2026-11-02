/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.HomFunctor
public import Aglib.AlgebraicGeometry.ProjectiveSpace.GeneralHyperplane.ThroughRationalPoint
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.FieldExtension
public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.Affine
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Regular
public import Aglib.RingTheory.KrullDimension.RegularQuotient
public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.ClosedImmersion
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Stalk
public import Aglib.AlgebraicGeometry.Modules.Invertible.DualTensorEquivalence
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.IntegralFibre
public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.Affine
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.Naturality
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Pairing
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit

/-!
# Regular hyperplanes on coefficient curves

The closed-stalk parameter condition is used on the actual curve, not on its
projective ambient space. A regular Cartier zero scheme has dimension zero even
on a nonreduced curve. Properness then makes the original zero scheme finite.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Association descends from restriction of scalars through an actual
surjective coefficient map. The associated prime retains its original comap. -/
theorem IsAssociatedPrime.of_comap_of_surjective
    {R S N : Type*} [CommRing R] [IsNoetherianRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (hRS : Function.Surjective (algebraMap R S)) (P : Ideal S) (hP : P.IsPrime)
    (h : IsAssociatedPrime (P.under R) N) : IsAssociatedPrime P N := by
  let : IsNoetherianRing S := isNoetherianRing_of_surjective R S (algebraMap R S) hRS
  obtain ⟨_, x, hx⟩ := isAssociatedPrime_iff.mp h
  apply isAssociatedPrime_iff.mpr
  refine ⟨hP, x, ?_⟩
  apply Ideal.comap_injective_of_surjective (algebraMap R S) hRS
  change P.under R = _
  rw [hx]
  ext r
  simp only [Ideal.mem_comap, Submodule.mem_colon_singleton, Submodule.mem_bot,
    algebraMap_smul]

namespace AlgebraicGeometry.Scheme.Hom

/-- A Cartier closed subscheme of a locally Noetherian scheme of dimension at
most one is locally Artinian. Neither smoothness nor reducedness is required. -/
theorem isLocallyArtinian_of_cartier_of_dimension_le_one
    {X D : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i)) (hdim : topologicalKrullDim X ≤ 1) :
    IsLocallyArtinian D := by
  have hlocal (x : D) : ∃ U : X.Opens, IsAffineOpen U ∧ i x ∈ U ∧
      IsArtinianRing Γ(D, i ⁻¹ᵁ U) := by
    obtain ⟨U, hU, hxU, a, ha, hker⟩ :=
      exists_affine_regular_idealGenerator_of_isLocallyRankOne i hI (i x)
    have hdimU : ringKrullDim Γ(X, U) ≤ 1 := by
      rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
      change topologicalKrullDim (Spec Γ(X, U)) ≤ 1
      rw [← IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph]
      exact (topologicalKrullDim_subspace_le X U).trans hdim
    let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    exact ⟨U, hU, hxU,
      _root_.RingHom.quotient_isArtinianRing_of_regular_kernel_element (i.app U).hom
        (i.app_surjective U hU) hdimU a ha
        (RingHom.mem_ker.mp (hker ▸ Ideal.mem_span_singleton_self a))⟩
  choose U hU hxU hArt using hlocal
  have hcover : IsOpenCover (fun x : D ↦ i ⁻¹ᵁ U x) := .mk (by
    apply top_unique
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x, hxU x⟩)
  exact (isLocallyArtinian_iff_of_isOpenCover hcover (fun x ↦ (hU x).preimage i)).mpr hArt

/-- The original Cartier zero scheme on a proper curve is finite; its dimension
bound comes from the original closed-stalk parameters, not a smoothness premise. -/
theorem finite_cartier_of_closed_parameters
    (k : Type u) [Field k] {C D : Scheme.{u}} (p : C ⟶ Spec (.of k)) [IsProper p]
    [CompactSpace C] [IsLocallyNoetherian C]
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
        IsSMulRegular (C.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x))
    (i : D ⟶ C) [IsClosedImmersion i] (hI : IsLocallyRankOne C (idealModule i)) :
    IsFinite (i ≫ p) := by
  let : IsLocallyArtinian D := isLocallyArtinian_of_cartier_of_dimension_le_one i hI
    (Scheme.dimension_le_one_of_closed_parameters C hCM)
  let : LocallyQuasiFinite (i ≫ p) :=
    locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr (fun _ => DiscreteTopology.isDiscrete)
  exact IsFinite.of_isProper_of_locallyQuasiFinite (i ≫ p)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- A monic map from an actual line to the structure sheaf on the parameter
curve has its original finite zero scheme. This uses the image ideal of that
same map, not a separately chosen Cartier presentation. -/
theorem finite_zeroInclusion_of_closed_parameters
    (k : Type u) [Field k] {C : Scheme.{u}} (p : C ⟶ Spec (.of k)) [IsProper p]
    [CompactSpace C] [IsLocallyNoetherian C]
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
        IsSMulRegular (C.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x))
    (L : LineBundle C) (φ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono φ] :
    IsFinite (Scheme.Modules.Hom.zeroInclusion φ ≫ p) :=
  Scheme.Hom.finite_cartier_of_closed_parameters k p hCM (Scheme.Modules.Hom.zeroInclusion φ)
    (zeroIdealLineBundle L φ).property

end AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Hom

set_option backward.isDefEq.respectTransparency false in
/-- The ambient affine prime of a closed curve point is not associated to the
original pushforward structure module when the original curve stalk has a
regular nonunit. The ambient projective/local ring need not be regular. -/
theorem not_associatedPrime_pushforward_unit_of_stalk_regular
    {C X : Scheme.{u}} [IsLocallyNoetherian X] (j : C ⟶ X) [IsClosedImmersion j]
    (x : C) (U : X.Opens) (hU : IsAffineOpen U) (hx : j x ∈ U)
    (hparam : ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
      IsSMulRegular (C.presheaf.stalk x) b) :
    (hU.primeIdealOf ⟨j x, hx⟩).asIdeal ∉
      associatedPrimes Γ(X, U)
        Γ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit C.ringCatSheaf), U) := by
  let A := Γ(X, U)
  let B := Γ(C, j ⁻¹ᵁ U)
  let : Algebra A B := (j.app U).hom.toAlgebra
  let : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hV : IsAffineOpen (j ⁻¹ᵁ U) := hU.preimage j
  let Q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : Q.IsPrime := (hV.primeIdealOf ⟨x, hx⟩).isPrime
  have hcomap : Q.under A = (hU.primeIdealOf ⟨j x, hx⟩).asIdeal := by
    have he := congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE (f := j) U hU (j ⁻¹ᵁ U) hV le_rfl hx)
    change Ideal.comap (j.app U).hom Q = _
    simpa only [Scheme.Hom.appLE_eq_app, PrimeSpectrum.comap_asIdeal] using he
  intro h
  have hA : IsAssociatedPrime (Q.under A) B := by
    rw [hcomap]
    exact h
  have hB : IsAssociatedPrime Q B :=
    IsAssociatedPrime.of_comap_of_surjective (j.app_surjective U hU) Q inferInstance hA
  let : Algebra B (C.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk C.presheaf ⟨x, hx⟩
  let : IsLocalization Q.primeCompl (C.presheaf.stalk x) :=
    hV.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨b, hb, hreg⟩ := hparam
  exact IsSMulRegular.not_mem_associatedPrimes_of_isLocalizedModule_atPrime
    Q (Algebra.linearMap B (C.presheaf.stalk x)) hreg hb hB

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Modules

/-- The original coefficient-map naturality square of the closed projection
formula, specialized to the original structure sheaf. This is the square used
to transport polynomial-section regularity to the curve. -/
theorem closedProjectionFormula_unit_coefficient_square
    {C X : Scheme.{u}} (j : C ⟶ X) [IsClosedImmersion j]
    {E E' : X.Modules} (g : E ⟶ E') :
    (moduleTensorCoefficientMap X g).app
        ((pushforward j).obj (SheafOfModules.unit C.ringCatSheaf)) ≫
      (closedImmersionProjectionFormulaIso j E' (SheafOfModules.unit C.ringCatSheaf)).hom =
    (closedImmersionProjectionFormulaIso j E (SheafOfModules.unit C.ringCatSheaf)).hom ≫
      (pushforward j).map ((moduleTensorCoefficientMap C ((Scheme.Modules.pullback j).map g)).app
        (SheafOfModules.unit C.ringCatSheaf)) :=
  closedImmersionProjectionFormulaIso_naturality_left j g _

set_option backward.isDefEq.respectTransparency false in
/-- Monicity of the original coefficient map on the original closed pushforward
structure sheaf implies monicity of its actual geometric pullback. -/
theorem mono_pullback_of_mono_coefficient_on_pushforward_unit
    {C X : Scheme.{u}} (j : C ⟶ X) [IsClosedImmersion j]
    {E E' : X.Modules} (g : E ⟶ E')
    [Mono ((moduleTensorCoefficientMap X g).app
      ((pushforward j).obj (SheafOfModules.unit C.ringCatSheaf)))] :
    Mono ((Scheme.Modules.pullback j).map g) := by
  let O := SheafOfModules.unit C.ringCatSheaf
  let gC := (Scheme.Modules.pullback j).map g
  let T := (moduleTensorCoefficientMap C gC).app O
  let F := pushforward j
  let : F.Faithful := (fullyFaithfulPushforwardOfClosedImmersion j).faithful
  have he : F.map T =
      (closedImmersionProjectionFormulaIso j E O).inv ≫
        (moduleTensorCoefficientMap X g).app (F.obj O) ≫
          (closedImmersionProjectionFormulaIso j E' O).hom := by
    rw [closedProjectionFormula_unit_coefficient_square, Iso.inv_hom_id_assoc]
  have : Mono (F.map T) := by rw [he]; infer_instance
  have : Mono T := F.mono_of_mono_map inferInstance
  let e := SheafOfModulesOfCommRing.tensorRightUnitIso C.sheaf
  have hn : T ≫ (e.app _).hom = (e.app _).hom ≫ gC := e.hom.naturality gC
  have hg : gC = (e.app _).inv ≫ T ≫ (e.app _).hom := by
    rw [hn, Iso.inv_hom_id_assoc]
  rw [show (Scheme.Modules.pullback j).map g = gC from rfl, hg]
  infer_instance

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

variable (k : Type u) [Field k] (ι : Type u)

set_option backward.isDefEq.respectTransparency false in
/-- The chart-sections ring isomorphism retains the original affine chart map. -/
theorem coordinateRingEquivSections_Spec_map (i : ι) :
    Spec.map (CommRingCat.ofHom (coordinateRingEquivSections k ι i).toRingHom) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one =
      (isAffineOpen_coordinateOpen k ι i).fromSpec := by
  apply (cancel_epi (isAffineOpen_coordinateOpen k ι i).isoSpec.hom).mp
  rw [IsAffineOpen.isoSpec_hom_fromSpec]
  change (coordinateOpen k ι i).toSpecΓ ≫
    (Spec.map (Proj.awayToSection (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one) = _
  rw [← Category.assoc]
  change (Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one).hom ≫
      ((Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one).inv ≫ _) = _
  exact Iso.hom_inv_id_assoc _ _

set_option backward.isDefEq.respectTransparency false in
/-- The evaluation functional of the constrained linear system induces the
original rational-point morphism on the original chart. -/
theorem coordinateSectionEvaluate_fromSpec [Finite ι]
    (a : ι → k) (i : ι) (hi : a i ≠ 0) :
    Spec.map (CommRingCat.ofHom (coordinateSectionEvaluate k ι a i)) ≫
      (isAffineOpen_coordinateOpen k ι i).fromSpec =
        BinaryFormProduct.Field.point (RingHom.id k) a i hi := by
  rw [coordinateRingEvaluate_point k ι a i hi,
    ← coordinateRingEquivSections_Spec_map k ι i]
  let e := Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one
  change Spec.map (e.inv ≫ CommRingCat.ofHom (coordinateRingEvaluate k ι a i)) ≫
    (Spec.map e.hom ≫ _) = _
  rw [Spec.map_comp]
  simp only [Category.assoc, ← Spec.map_comp_assoc, e.hom_inv_id, Spec.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The actual rational-point prime on the chart is exactly the original
section-evaluation kernel used by constrained hyperplane avoidance. -/
theorem primeIdealOf_rationalPoint_eq_kernel [Finite ι]
    (a : ι → k) (i : ι) (hi : a i ≠ 0) (z : Spec (.of k)) :
    ((isAffineOpen_coordinateOpen k ι i).primeIdealOf
      ⟨BinaryFormProduct.Field.point (RingHom.id k) a i hi z,
        BinaryFormProduct.Field.point_preimage_selected (RingHom.id k) a i hi trivial⟩).asIdeal =
      RingHom.ker (coordinateSectionEvaluate k ι a i) := by
  let hU := isAffineOpen_coordinateOpen k ι i
  have hpt := congrArg (fun f : Spec (.of k) ⟶ ProjectiveSpace k ι => f z)
    (coordinateSectionEvaluate_fromSpec k ι a i hi)
  have hp : hU.primeIdealOf
      ⟨BinaryFormProduct.Field.point (RingHom.id k) a i hi z,
        BinaryFormProduct.Field.point_preimage_selected (RingHom.id k) a i hi trivial⟩ =
      Spec.map (CommRingCat.ofHom (coordinateSectionEvaluate k ι a i)) z := by
    apply hU.fromSpec.isOpenEmbedding.injective
    exact (hU.fromSpec_primeIdealOf _).trans hpt.symm
  rw [hp]
  change Ideal.comap (coordinateSectionEvaluate k ι a i) z.asIdeal = _
  rw [Ideal.eq_bot_of_prime z.asIdeal]
  rfl

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.Cohomology

open Scheme.Modules.QuasiCoherent

variable (k : Type u) [Field k] (ι : Type u)
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]

/-- The actual pullback of the original degree-one projective twist. -/
def curveHyperplaneLine : LineBundle C :=
  pullbackLineBundle j (twistingLineBundle k ι (((1 : ℕ) : ℤ) + 0))

/-- The section on the original curve is the actual geometric pullback of
multiplication by the same polynomial section, with the native zero-twist and
pullback-unit identifications. -/
def curveHyperplaneSection (c : ι →₀ k) :
    SheafOfModules.unit C.ringCatSheaf ⟶ (curveHyperplaneLine k ι j).val :=
  (((Scheme.Modules.pullback j).mapIso (twistingZeroIso k ι)) ≪≫ pullbackUnitIso j).inv ≫
    (Scheme.Modules.pullback j).map
      (twistingMultiplyGlobal k ι ((1 : ℕ) : ℤ) 0 (linearFormSection k ι c))

/-- Its original dual section map defines the hyperplane ideal. -/
def curveHyperplaneIdealMap (c : ι →₀ k) :
    (dualLineBundle C (curveHyperplaneLine k ι j)).val ⟶
      SheafOfModules.unit C.ringCatSheaf :=
  sectionContraction (curveHyperplaneLine k ι j) (curveHyperplaneSection k ι j c)

/-- Monicity from the actual ambient regularity criterion is transported through
the original projection-formula square, not assumed for the pulled section. -/
theorem curveHyperplaneSection_mono (c : ι →₀ k)
    (hreg : ∀ (i : ι) (U : (ProjectiveSpace k ι).Opens) (hU : U ≤ coordinateOpen k ι i),
      IsSMulRegular Γ((Scheme.Modules.pushforward j).obj
        (SheafOfModules.unit C.ringCatSheaf), U)
        (frameCoefficient k ι (linearFormSection k ι c) i hU)) :
    Mono (curveHyperplaneSection k ι j c) := by
  let F := (Scheme.Modules.pushforward j).obj (SheafOfModules.unit C.ringCatSheaf)
  have hm := mono_twistingTensorMultiply_of_isSMulRegular k ι (linearFormSection k ι c) F hreg
  have hmTensor : Mono ((twistingTensorMultiply k ι ((1 : ℕ) : ℤ) 0
      (linearFormSection k ι c)).app F) :=
    (mono_comp_iff_of_isIso _ _).mp hm
  have : Mono ((moduleTensorCoefficientMap (ProjectiveSpace k ι)
      (twistingMultiplyGlobal k ι ((1 : ℕ) : ℤ) 0 (linearFormSection k ι c))).app F) := hmTensor
  have : Mono ((Scheme.Modules.pullback j).map
      (twistingMultiplyGlobal k ι ((1 : ℕ) : ℤ) 0 (linearFormSection k ι c))) :=
    mono_pullback_of_mono_coefficient_on_pushforward_unit j _
  unfold curveHyperplaneSection
  infer_instance

omit [IsClosedImmersion j] in
/-- Tensor by the actual inverse line transports monicity of the original
section to monicity of the original contraction defining its zero scheme. -/
theorem curveHyperplaneIdealMap_mono (c : ι →₀ k)
    [Mono (curveHyperplaneSection k ι j c)] : Mono (curveHyperplaneIdealMap k ι j c) := by
  let E := lineBundleDualTensorEquivalence C (curveHyperplaneLine k ι j)
  have : E.functor.IsEquivalence := Equivalence.isEquivalence_functor E
  have : Mono (E.functor.map (curveHyperplaneSection k ι j c)) := inferInstance
  have : Mono (tensorSheafMap C (𝟙 (dualLineBundle C (curveHyperplaneLine k ι j)).val)
      (curveHyperplaneSection k ι j c)) :=
    inferInstanceAs (Mono (E.functor.map (curveHyperplaneSection k ι j c)))
  unfold curveHyperplaneIdealMap sectionContraction
  infer_instance

/-- The actual closed-stalk CM hypothesis produces a regular original linear
hyperplane through any actual rational point. No extra associated-point or
closed-point rationality premise is used. -/
theorem exists_curveHyperplane_regular_through_rationalPoint [Infinite k] [Finite ι]
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
        IsSMulRegular (C.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x))
    (r : Spec (.of k) ⟶ C) (hr : r ≫ (j ≫ toSpec k ι) = 𝟙 _) :
    ∃ (a : ι → k) (i₀ : ι) (hi₀ : a i₀ ≠ 0) (c : ι →₀ k),
      BinaryFormProduct.Field.point (RingHom.id k) a i₀ hi₀ = r ≫ j ∧
      Finsupp.linearCombination k a c = 0 ∧
      (∀ (i : ι) (U : (ProjectiveSpace k ι).Opens) (hU : U ≤ coordinateOpen k ι i),
        IsSMulRegular Γ((Scheme.Modules.pushforward j).obj
          (SheafOfModules.unit C.ringCatSheaf), U)
          (frameCoefficient k ι (linearFormSection k ι c) i hU)) ∧
      Mono (curveHyperplaneSection k ι j c) ∧ Mono (curveHyperplaneIdealMap k ι j c) := by
  have hr' : (r ≫ j) ≫ toSpec k ι = Spec.map (CommRingCat.ofHom (RingHom.id k)) := by
    simpa only [Category.assoc, CommRingCat.ofHom_id, Spec.map_id] using hr
  obtain ⟨a, i₀, hi₀, ha⟩ := BinaryFormProduct.Field.exists_point (RingHom.id k) (r ≫ j) hr'
  let z : Spec (.of k) := ⟨⊥, inferInstance⟩
  let : IsClosedImmersion r := isClosedImmersion_of_comp_eq_id (j ≫ toSpec k ι) r hr
  have hxclosed : IsClosed ({r z} : Set C) := by
    simpa only [Set.image_singleton] using r.isClosedEmbedding.isClosedMap {z} isClosed_singleton
  let F := (Scheme.Modules.pushforward j).obj (SheafOfModules.unit C.ringCatSheaf)
  have hF : affineLocallyFiniteType (ProjectiveSpace k ι) F :=
    FiniteMorphism.affineLocallyFiniteType_pushforward j (affineLocallyFiniteType_structureModule C)
  have havoid (i : ι) (hi : a i ≠ 0) :
      RingHom.ker (coordinateSectionEvaluate k ι a i) ∉
        associatedPrimes Γ(ProjectiveSpace k ι, coordinateOpen k ι i)
          Γ(F, coordinateOpen k ι i) := by
    have he : BinaryFormProduct.Field.point (RingHom.id k) a i hi = r ≫ j :=
      (BinaryFormProduct.Field.point_eq_of_scale (RingHom.id k) a a i i₀ hi hi₀ 1 one_ne_zero
        (fun _ => (one_mul _).symm)).trans ha
    have hx : j (r z) ∈ coordinateOpen k ι i := by
      have hm := BinaryFormProduct.Field.point_preimage_selected (RingHom.id k) a i hi
        (show z ∈ (⊤ : (Spec (.of k)).Opens) from trivial)
      rw [he] at hm
      exact hm
    have hp : ((isAffineOpen_coordinateOpen k ι i).primeIdealOf ⟨j (r z), hx⟩).asIdeal =
        RingHom.ker (coordinateSectionEvaluate k ι a i) := by
      simpa only [he, Scheme.Hom.comp_apply] using primeIdealOf_rationalPoint_eq_kernel k ι a i hi z
    rw [← hp]
    obtain ⟨b, hb, hreg, _⟩ := hCM (r z) hxclosed
    exact j.not_associatedPrime_pushforward_unit_of_stalk_regular (r z)
      (coordinateOpen k ι i) (isAffineOpen_coordinateOpen k ι i) hx ⟨b, hb, hreg⟩
  obtain ⟨c, hc, hreg⟩ := exists_linearFormSection_through_isSMulRegular k ι a
    (fun _ : PUnit.{u + 1} => F) (fun _ => hF) (fun _ i hi => havoid i hi)
  have hm := curveHyperplaneSection_mono k ι j c (hreg PUnit.unit)
  let := hm
  exact ⟨a, i₀, hi₀, c, ha, hc, hreg PUnit.unit, hm, curveHyperplaneIdealMap_mono k ι j c⟩

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The section produced through the original rational point has its own finite
zero scheme on the full curve. The original embedding supplies properness and
local Noetherianity; the original closed parameters supply dimension at most one. -/
theorem exists_finite_curveHyperplane_through_rationalPoint
    (k : Type u) [Field k] [Infinite k] (ι : Type u) [Finite ι]
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
        IsSMulRegular (C.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x))
    (r : Spec (.of k) ⟶ C) (hr : r ≫ (j ≫ toSpec k ι) = 𝟙 _) :
    ∃ (a : ι → k) (i : ι) (hi : a i ≠ 0) (c : ι →₀ k),
      BinaryFormProduct.Field.point (RingHom.id k) a i hi = r ≫ j ∧
      coordinateSectionEvaluate k ι a i
        (frameCoefficient k ι (linearFormSection k ι c) i le_rfl) = 0 ∧
      Mono (curveHyperplaneSection k ι j c) ∧ Mono (curveHyperplaneIdealMap k ι j c) ∧
      IsFinite (Scheme.Modules.Hom.zeroInclusion (curveHyperplaneIdealMap k ι j c) ≫
        (j ≫ toSpec k ι)) := by
  obtain ⟨a, i, hi, c, ha, hc, _, hm, hφ⟩ :=
    exists_curveHyperplane_regular_through_rationalPoint k ι j hCM r hr
  let := hφ
  let p := j ≫ toSpec k ι
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian p
  exact ⟨a, i, hi, c, ha, coordinateSectionEvaluate_frameCoefficient k ι a i hi c hc, hm, hφ,
    finite_zeroInclusion_of_closed_parameters k p hCM
      (dualLineBundle C (curveHyperplaneLine k ι j)) (curveHyperplaneIdealMap k ι j c)⟩

end AlgebraicGeometry.Scheme.Cohomology
namespace AlgebraicGeometry.ProjectiveSpace

variable (k : Type u) [Field k] (ι : Type u)

set_option backward.isDefEq.respectTransparency false in
/-- The actual point restriction map on chart functions is the original
rational evaluation, followed by the native affine global-sections inverse. -/
theorem rationalPoint_appLE_eq_evaluate [Finite ι]
    (a : ι → k) (i : ι) (hi : a i ≠ 0) :
    (BinaryFormProduct.Field.point (RingHom.id k) a i hi).appLE
      (coordinateOpen k ι i) ⊤
      (BinaryFormProduct.Field.point_preimage_selected (RingHom.id k) a i hi) =
        CommRingCat.ofHom (coordinateSectionEvaluate k ι a i) ≫ (Scheme.ΓSpecIso (.of k)).inv := by
  apply Spec.map_injective
  apply (cancel_mono (isAffineOpen_coordinateOpen k ι i).fromSpec).mp
  rw [IsAffineOpen.SpecMap_appLE_fromSpec _ (isAffineOpen_coordinateOpen k ι i)
    (isAffineOpen_top (Spec (.of k))), Spec.map_comp, Category.assoc,
    coordinateSectionEvaluate_fromSpec, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]

/-- The original projective section map, using its native zero-twist frame. -/
def linearSectionMap (s : (twistingSheaf k ι ((1 : ℕ) : ℤ)).val.obj (op ⊤)) :
    SheafOfModules.unit (ProjectiveSpace k ι).ringCatSheaf ⟶
      twistingSheaf k ι (((1 : ℕ) : ℤ) + 0) :=
  (twistingZeroIso k ι).inv ≫ twistingMultiplyGlobal k ι ((1 : ℕ) : ℤ) 0 s

set_option backward.isDefEq.respectTransparency false in
/-- The original section map sends one to the original section in every frame. -/
theorem linearSectionMap_chart_one (s : (twistingSheaf k ι ((1 : ℕ) : ℤ)).val.obj (op ⊤))
    (i : ι) :
    twistingSectionsEquiv k ι (((1 : ℕ) : ℤ) + 0) i le_rfl
      ((linearSectionMap k ι s).val.app (op (coordinateOpen k ι i))
        (1 : Γ(ProjectiveSpace k ι, coordinateOpen k ι i))) =
        frameCoefficient k ι s i le_rfl := by
  change twistingSectionsEquiv k ι (((1 : ℕ) : ℤ) + 0) i le_rfl
    ((twistingMultiplyGlobal k ι ((1 : ℕ) : ℤ) 0 s).val.app _
      ((unitToTwistingZero k ι).val.app _
        (1 : Γ(ProjectiveSpace k ι, coordinateOpen k ι i)))) = _
  rw [twistingMultiplyGlobal_app, twistingSectionsEquiv_mul, unitToTwistingZero_app, mul_one]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Literal pullback of the same polynomial section at its original rational
point is zero. This is stronger than retaining only the scalar incidence equation. -/
theorem rationalPoint_pullback_linearSectionMap_eq_zero [Finite ι]
    (a : ι → k) (i : ι) (hi : a i ≠ 0) (c : ι →₀ k)
    (hc : Finsupp.linearCombination k a c = 0) :
    (Scheme.Modules.pullback (BinaryFormProduct.Field.point (RingHom.id k) a i hi)).map
      (linearSectionMap k ι (linearFormSection k ι c)) = 0 := by
  let q := BinaryFormProduct.Field.point (RingHom.id k) a i hi
  let D := (coordinateUnitCocycle k ι).zpow (-(((1 : ℕ) : ℤ) + 0))
  let s := linearSectionMap k ι (linearFormSection k ι c)
  let e := FromSections.pullbackCocycleIso q D (iSup_coordinateOpen_eq_top k ι)
  let htop := BinaryFormProduct.Field.point_preimage_selected (RingHom.id k) a i hi
  have hcoeff := FromSections.pullbackCocycleIso_section_coefficient q D
    (iSup_coordinateOpen_eq_top k ι) s i (O := ⊤) htop
  have hz : (q.appLE (coordinateOpen k ι i) ⊤ htop).hom
      (frameCoefficient k ι (linearFormSection k ι c) i le_rfl) = 0 := by
    rw [rationalPoint_appLE_eq_evaluate]
    change (Scheme.ΓSpecIso (.of k)).inv.hom
      (coordinateSectionEvaluate k ι a i
        (frameCoefficient k ι (linearFormSection k ι c) i le_rfl)) = 0
    rw [coordinateSectionEvaluate_frameCoefficient k ι a i hi c hc, map_zero]
  have hmap : e.hom.val.app (op ⊤)
      ((FromSections.pullbackSection q s).val.app (op ⊤) (1 : Γ(Spec (.of k), ⊤))) = 0 := by
    apply ((FromSections.pullbackCocycle q D).localSectionsEquiv i htop).injective
    rw [map_zero]
    exact hcoeff.trans ((congrArg (fun b => (q.appLE (coordinateOpen k ι i) ⊤ htop).hom b)
      (linearSectionMap_chart_one k ι (linearFormSection k ι c) i)).trans hz)
  have hs : FromSections.pullbackSection q s = 0 := by
    apply (unitHomGlobalSectionsEquiv (Spec (.of k)) _).injective
    change (FromSections.pullbackSection q s).val.app (op ⊤) (1 : Γ(Spec (.of k), ⊤)) = 0
    have ht := congrArg (fun z => e.inv.val.app (op ⊤) z) hmap
    rw [map_zero] at ht
    have he : e.inv.val.app (op ⊤) (e.hom.val.app (op ⊤)
        ((FromSections.pullbackSection q s).val.app (op ⊤) (1 : Γ(Spec (.of k), ⊤)))) =
        (FromSections.pullbackSection q s).val.app (op ⊤) (1 : Γ(Spec (.of k), ⊤)) := by
      change ((e.hom ≫ e.inv).val.app (op ⊤)) _ = _
      rw [e.hom_inv_id]
      rfl
    exact he.symm.trans ht
  apply (cancel_epi (pullbackUnitIso q).inv).mp
  simpa only [FromSections.pullbackSection, comp_zero] using hs

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.Cohomology

/-- Literal vanishing of the original pulled polynomial section at the original
rational point, through the native pullback-composition comparison. -/
theorem curveHyperplaneSection_pullback_point_eq_zero
    (k : Type u) [Field k] (ι : Type u) [Finite ι]
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (r : Spec (.of k) ⟶ C) (a : ι → k) (i : ι) (hi : a i ≠ 0) (c : ι →₀ k)
    (he : BinaryFormProduct.Field.point (RingHom.id k) a i hi = r ≫ j)
    (hc : Finsupp.linearCombination k a c = 0) :
    (Scheme.Modules.pullback r).map (curveHyperplaneSection k ι j c) = 0 := by
  let g := twistingMultiplyGlobal k ι ((1 : ℕ) : ℤ) 0 (linearFormSection k ι c)
  have hz := rationalPoint_pullback_linearSectionMap_eq_zero k ι a i hi c hc
  rw [he] at hz
  change (Scheme.Modules.pullback (r ≫ j)).map ((twistingZeroIso k ι).inv ≫ g) = 0 at hz
  rw [Functor.map_comp] at hz
  have hg : (Scheme.Modules.pullback (r ≫ j)).map g = 0 := by
    apply (cancel_epi ((Scheme.Modules.pullback (r ≫ j)).map (twistingZeroIso k ι).inv)).mp
    simpa only [comp_zero] using hz
  have hdouble : (Scheme.Modules.pullback r).map ((Scheme.Modules.pullback j).map g) = 0 := by
    apply (cancel_mono ((Scheme.Modules.pullbackComp r j).hom.app _)).mp
    have hn := (Scheme.Modules.pullbackComp r j).hom.naturality g
    simpa only [Functor.comp_map, hg, comp_zero, zero_comp] using hn
  unfold curveHyperplaneSection
  rw [Functor.map_comp, hdouble, comp_zero]

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- Vanishing of the actual pulled section implies vanishing of its actual
pulled contraction, through the native tensor pullback naturality square. -/
theorem pullback_sectionContraction_eq_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : LineBundle Y)
    (σ : SheafOfModules.unit Y.ringCatSheaf ⟶ L.val)
    (hσ : (Scheme.Modules.pullback f).map σ = 0) :
    (Scheme.Modules.pullback f).map (sectionContraction L σ) = 0 := by
  let D := (dualLineBundle Y L).val
  have ht : (Scheme.Modules.pullback f).map (tensorSheafMap Y (𝟙 D) σ) = 0 := by
    apply (cancel_mono (pullbackTensorMapIso f D L.val).hom).mp
    rw [pullbackTensorMapIso_hom, pullbackTensorMap_naturality, CategoryTheory.Functor.map_id, hσ]
    have hz : tensorSheafMap X (𝟙 ((Scheme.Modules.pullback f).obj D))
        (0 : (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
          (Scheme.Modules.pullback f).obj L.val) = 0 := by
      exact (moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj D)).map_zero _ _
    rw [hz, comp_zero, zero_comp]
  change (Scheme.Modules.pullback f).map
    ((tensorSheafLeftUnit Y D).inv ≫
      (tensorSheafBraiding Y (SheafOfModules.unit Y.ringCatSheaf) D).hom ≫
      tensorSheafMap Y (𝟙 D) σ ≫ (dualEvaluationIso Y L).hom) = 0
  simp only [CategoryTheory.Functor.map_comp, ht, comp_zero, zero_comp]

end AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Modules.Hom

/-- Vanishing after actual geometric pullback means the original module map is
annihilated by the original structure-module arrow. -/
theorem comp_structureModuleMap_eq_zero_of_pullback_map_eq_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (φ : M ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (hφ : (Scheme.Modules.pullback f).map φ = 0) :
    φ ≫ Scheme.Hom.structureModuleMap f = 0 := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left
    φ (pullbackUnitIso f).hom
  rw [pullbackUnitIso_homEquiv] at h
  simpa only [hφ, zero_comp, Adjunction.homEquiv_apply, Functor.map_zero, comp_zero,
    Scheme.Hom.structureModuleMap] using h.symm

/-- The original point morphism factors through the actual zero scheme whenever
the original module map pulls back to zero. No replacement ideal is chosen. -/
theorem exists_lift_zeroInclusion_of_pullback_map_eq_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] {M : Y.Modules}
    [M.IsQuasicoherent] (φ : M ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (hφ : (Scheme.Modules.pullback f).map φ = 0) :
    ∃ f' : X ⟶ zeroScheme φ, f' ≫ zeroInclusion φ = f := by
  have hz := comp_structureModuleMap_eq_zero_of_pullback_map_eq_zero f φ hφ
  have hi : (zeroInclusion φ).ker ≤ f.ker := by
    intro U
    rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply,
      zeroInclusion_kernel φ (imageIdealLocalizes_of_isQuasicoherent φ)]
    rintro _ ⟨m, rfl⟩
    change f.app U (φ.val.app (op U.val) m) = 0
    have hm := congrArg (fun t : M ⟶ (Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf) => t.val.app (op U.val) m) hz
    exact hm
  exact ⟨IsClosedImmersion.lift (zeroInclusion φ) f hi,
    IsClosedImmersion.lift_fac _ _ _⟩

end AlgebraicGeometry.Scheme.Modules.Hom

namespace AlgebraicGeometry.Scheme.Cohomology

/-- A genuine regular finite hyperplane through the original rational point of
the full CM curve. Its ideal is the contraction of the actual pulled polynomial
section, and the original point factors through that same original zero scheme. -/
theorem exists_regular_finite_hyperplane_through_rationalPoint
    (k : Type u) [Field k] [Infinite k] (ι : Type u) [Finite ι]
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
        IsSMulRegular (C.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x))
    (r : Spec (.of k) ⟶ C) (hr : r ≫ (j ≫ toSpec k ι) = 𝟙 _) :
    ∃ c : ι →₀ k, Mono (curveHyperplaneSection k ι j c) ∧
      Mono (curveHyperplaneIdealMap k ι j c) ∧
      IsFinite (Scheme.Modules.Hom.zeroInclusion (curveHyperplaneIdealMap k ι j c) ≫
        (j ≫ toSpec k ι)) ∧
      ∃ rD : Spec (.of k) ⟶ Scheme.Modules.Hom.zeroScheme (curveHyperplaneIdealMap k ι j c),
        rD ≫ Scheme.Modules.Hom.zeroInclusion (curveHyperplaneIdealMap k ι j c) = r := by
  obtain ⟨a, i, hi, c, ha, hc, _, hm, hφ⟩ :=
    exists_curveHyperplane_regular_through_rationalPoint k ι j hCM r hr
  let := hφ
  let p := j ≫ toSpec k ι
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian p
  let : IsClosedImmersion r := isClosedImmersion_of_comp_eq_id p r hr
  let D := dualLineBundle C (curveHyperplaneLine k ι j)
  let : D.val.IsLocallyFree := lineBundle_isLocallyFree C D
  let : D.val.IsQuasicoherent := inferInstance
  have hs := curveHyperplaneSection_pullback_point_eq_zero k ι j r a i hi c ha hc
  have hzero : (Scheme.Modules.pullback r).map (curveHyperplaneIdealMap k ι j c) = 0 :=
    pullback_sectionContraction_eq_zero r (curveHyperplaneLine k ι j)
      (curveHyperplaneSection k ι j c) hs
  exact ⟨c, hm, hφ,
    finite_zeroInclusion_of_closed_parameters k p hCM D (curveHyperplaneIdealMap k ι j c),
    Scheme.Modules.Hom.exists_lift_zeroInclusion_of_pullback_map_eq_zero
      r (curveHyperplaneIdealMap k ι j c) hzero⟩

/-- The original regular hyperplane ideal identifies its dual with the same
pulled-back O(1), through the original ideal factor and bidual map. -/
def curveHyperplaneDualIdealIso
    (k : Type u) [Field k] (ι : Type u) {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j] (c : ι →₀ k)
    [Mono (curveHyperplaneIdealMap k ι j c)] :
    (curveHyperplaneLine k ι j).val ≅
      Invertible.dualSheaf C (Scheme.Hom.idealModule
        (Scheme.Modules.Hom.zeroInclusion (curveHyperplaneIdealMap k ι j c))) :=
  Invertible.bidualIso C (curveHyperplaneLine k ι j) ≪≫
    InternalHom.iso C
      (Invertible.zeroIdealLineBundleIso
        (Invertible.dualLineBundle C (curveHyperplaneLine k ι j))
        (curveHyperplaneIdealMap k ι j c))
      (Iso.refl (SheafOfModules.unit C.ringCatSheaf))

end AlgebraicGeometry.Scheme.Cohomology
