/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.Cartier.Purity
public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.Principal
public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.Affine
public import Aglib.AlgebraicGeometry.Modules.Tensor.AffineSections
public import Aglib.AlgebraicGeometry.Modules.Tensor.ToUnit
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback

/-!
# Global Cartier purity with the original positive counit

Actual affine regular generators of the original ideal produce genuine quotient
charts. Regularity of the original coefficient section implies regularity of
the original ideal action and then of the literal affine coefficient sections.
The passed principal calculation and original open-homology exchange give
global concentration. The purity map is the actual derived adjoint of the
original global coefficient extension class.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open scoped TensorProduct

private theorem sectionTensor_otherTwist_mono
    {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    (I L M : C) (τ : 𝟭 C ⟶ tensorLeft L)
    (htensor : ∀ A B : C, τ.app (A ⊗ B) ≫ (α_ L A B).inv = τ.app A ▷ B)
    [(tensorRight I).PreservesMonomorphisms] [Mono (τ.app M)] :
    Mono (τ.app (I ⊗ M)) := by
  have hmap : Mono (τ.app M ▷ I) := inferInstanceAs (Mono ((tensorRight I).map (τ.app M)))
  let := hmap
  have hright : Mono (τ.app (M ⊗ I)) := by
    constructor
    intro Z f g h
    apply (cancel_mono (τ.app M ▷ I)).mp
    rw [← htensor M I]
    simpa only [Category.assoc] using
      congrArg (fun k : Z ⟶ L ⊗ (M ⊗ I) => k ≫ (α_ L M I).inv) h
  let := hright
  constructor
  intro Z f g h
  apply (cancel_mono (β_ I M).hom).mp
  apply (cancel_mono (τ.app (M ⊗ I))).mp
  have hn := τ.naturality (β_ I M).hom
  change (β_ I M).hom ≫ τ.app (M ⊗ I) =
    τ.app (I ⊗ M) ≫ (tensorLeft L).map (β_ I M).hom at hn
  calc
    _ = (f ≫ τ.app (I ⊗ M)) ≫ (tensorLeft L).map (β_ I M).hom := by
      rw [Category.assoc, hn, ← Category.assoc]
    _ = (g ≫ τ.app (I ⊗ M)) ≫ (tensorLeft L).map (β_ I M).hom := by rw [h]
    _ = _ := by rw [Category.assoc, ← hn, ← Category.assoc]

private theorem sectionTensor_idealAction_mono
    {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    (I L M : C) (τ : 𝟭 C ⟶ tensorLeft L)
    (htensor : ∀ A B : C, τ.app (A ⊗ B) ≫ (α_ L A B).inv = τ.app A ▷ B)
    (e : L ⊗ I ≅ 𝟙_ C) (φ : I ⟶ 𝟙_ C) (hev : τ.app I ≫ e.hom = φ)
    [(tensorRight I).PreservesMonomorphisms] [Mono (τ.app M)] :
    Mono (φ ▷ M ≫ (λ_ M).hom) := by
  let := sectionTensor_otherTwist_mono I L M τ htensor
  let p : L ⊗ (I ⊗ M) ≅ M :=
    (α_ L I M).symm ≪≫ (tensorRight M).mapIso e ≪≫ λ_ M
  have heq : τ.app (I ⊗ M) ≫ p.hom = φ ▷ M ≫ (λ_ M).hom := by
    change τ.app (I ⊗ M) ≫ (α_ L I M).inv ≫ e.hom ▷ M ≫ (λ_ M).hom = _
    rw [← Category.assoc, htensor I M, ← comp_whiskerRight_assoc, hev]
  have h : Mono (τ.app (I ⊗ M) ≫ p.hom) := inferInstance
  exact heq ▸ h

private def regularIdealFrame {R : Type*} [CommRing R] (I : Ideal R)
    (a : R) (ha : IsSMulRegular R a) (hI : I = Ideal.span {a}) : R ≃ₗ[R] I := by
  let aI : I := ⟨a, hI ▸ Ideal.mem_span_singleton_self a⟩
  let f := LinearMap.toSpanSingleton R I aI
  have hi : Function.Injective f := by
    intro x y hxy
    apply ha
    simpa only [f, aI, LinearMap.toSpanSingleton_apply, Submodule.coe_smul_of_tower,
      smul_eq_mul, mul_comm] using congrArg Subtype.val hxy
  have hs : Function.Surjective f := by
    intro x
    have hx : x.val ∈ Ideal.span {a} := hI ▸ x.property
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hx
    exact ⟨r, Subtype.ext hr⟩
  exact LinearEquiv.ofBijective f ⟨hi, hs⟩

private theorem regularIdealFrame_one {R : Type*} [CommRing R] (I : Ideal R)
    (a : R) (ha : IsSMulRegular R a) (hI : I = Ideal.span {a}) :
    (regularIdealFrame I a ha hI 1 : R) = a := by
  change 1 * a = a
  exact one_mul a

private theorem regular_of_injective_tensor_action
    {R N M : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] (a : R) (σ : N) (ell : N →ₗ[R] R)
    (hσ : ell σ = 1) (μ : N ⊗[R] M → M) (hμ : Function.Injective μ)
    (hact : ∀ m : M, μ (σ ⊗ₜ m) = a • m) : IsSMulRegular M a := by
  intro m n h
  have ht : σ ⊗ₜ[R] m = σ ⊗ₜ[R] n :=
    hμ ((hact m).trans (h.trans (hact n).symm))
  let p : N ⊗[R] M →ₗ[R] M :=
    (TensorProduct.lid R M).toLinearMap.comp (TensorProduct.map ell LinearMap.id)
  have hp := congrArg p ht
  simpa only [p, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe, TensorProduct.lid_tmul, hσ, one_smul] using hp

private theorem globalTwoPreimageInv
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Full] [F.Faithful] [G.Full] [G.Faithful]
    {X Y : C} {Z : E} (e : G.obj (F.obj X) ≅ Z) (σ : G.obj (F.obj Y) ≅ Z) :
    σ.inv ≫ G.map (F.map (F.preimageIso (G.preimageIso (e ≪≫ σ.symm))).inv) = e.inv := by
  change σ.inv ≫ G.map (F.map (F.preimage (G.preimage (e ≪≫ σ.symm).inv))) = e.inv
  rw [F.map_preimage, G.map_preimage]
  simp

namespace AlgebraicGeometry.Scheme.Modules

universe u

attribute [local instance] standardHasDerivedCategory principalSheafHasExt

/-- Regularity of the original Cartier section implies regularity of the original ideal action. -/
public theorem cartierIdealAction_mono {D X : Scheme.{u}} (i : D ⟶ X)
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules)
    [Mono ((cartierTensorSection i).app M)] :
    Mono ((tensorToUnit (idealInclusion i)).app M) := by
  let I : X.Modules := idealModule i
  let L : X.Modules := dualSheaf X I
  let τ : 𝟭 X.Modules ⟶ tensorLeft (C := X.Modules) L := cartierTensorSection i
  let : Mono (τ.app M) := inferInstanceAs (Mono ((cartierTensorSection i).app M))
  let : IsFiniteLocallyFree X I := isFiniteLocallyFree_of_isLocallyRankOne hI
  let : (moduleTensorRightFunctor X I).Additive := moduleTensorRightFunctor_additive X I
  let : (moduleTensorRightFunctor X I).PreservesHomology := moduleTensorRight_preservesHomology I
  let : PreservesFiniteLimits (moduleTensorRightFunctor X I) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  let : (tensorRight (C := X.Modules) I).PreservesMonomorphisms :=
    inferInstanceAs (moduleTensorRightFunctor X I).PreservesMonomorphisms
  let e₀ := dualEvaluationIso X ⟨idealModule i, hI⟩
  let e : (L ⊗ I : X.Modules) ≅ 𝟙_ X.Modules :=
    ⟨e₀.hom, e₀.inv, e₀.hom_inv_id, e₀.inv_hom_id⟩
  exact sectionTensor_idealAction_mono I L M τ
    (fun A B => positiveCartierTensorSection_tensor X L A B (cartierDualIdealSection i))
    e (idealInclusion i) (cartierTensorSection_evaluation i hI)

/-- An actual regular ideal generator is regular on the original affine coefficient sections. -/
public theorem cartierEquation_regular_affineSections {D X : Scheme.{u}} (i : D ⟶ X)
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) [M.IsQuasicoherent]
    [Mono ((cartierTensorSection i).app M)] (U : X.Opens) (hU : IsAffineOpen U)
    (a : Γ(X, U)) (ha : IsSMulRegular Γ(X, U) a)
    (hker : RingHom.ker (i.app U).hom = Ideal.span {a}) :
    IsSMulRegular Γ(M, U) a := by
  let I : X.Modules := idealModule i
  let : I.IsQuasicoherent := lineBundle_isQuasicoherent ⟨idealModule i, hI⟩
  let μ : (moduleTensorLeftFunctor X I).obj M ⟶ M := (tensorToUnit (idealInclusion i)).app M
  let : Mono μ := cartierIdealAction_mono i hI M
  let ev : X.Modules ⥤ ModuleCat Γ(X, U) := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let : PreservesLimits ev := inferInstanceAs
    (PreservesLimits (SheafOfModules.evaluation X.ringCatSheaf (op U)))
  have hμ : Function.Injective (ev.map μ).hom := (ModuleCat.mono_iff_injective _).mp inferInstance
  let E : Γ(I, U) ≃ₗ[Γ(X, U)] RingHom.ker (i.app U).hom := idealSectionsEquiv i U
  let F := regularIdealFrame (RingHom.ker (i.app U).hom) a ha hker
  let σ : Γ(I, U) := E.symm (F 1)
  let ell : Γ(I, U) →ₗ[Γ(X, U)] Γ(X, U) := F.symm.toLinearMap.comp E.toLinearMap
  have hσ : ell σ = 1 := by
    change F.symm (E (E.symm (F 1))) = 1
    rw [E.apply_symm_apply, F.symm_apply_apply]
  have hvalue : (show Γ(X, U) from (idealInclusion i).val.app (op U) σ) = a := by
    exact (idealSectionsEquiv_val i U σ).symm.trans
      ((congrArg Subtype.val (E.apply_symm_apply (F 1))).trans
        (regularIdealFrame_one _ a ha hker))
  let f : Γ(I, U) ⊗[Γ(X, U)] Γ(M, U) → Γ(M, U) := fun z =>
    μ.val.app (op U) (moduleTensorSectionLinear X I M U z)
  have hf : Function.Injective f := hμ.comp
    (moduleTensorSectionLinear_bijective_of_isAffine I M U hU).injective
  apply regular_of_injective_tensor_action a σ ell hσ f hf
  intro m
  exact (tensorToUnit_section (idealInclusion i) M U σ m).trans
    (congrArg (fun r : Γ(X, U) => r • m) hvalue)

/-- The original affine chart isomorphism retains coefficient regularity and its ring action. -/
public theorem cartierEquation_regular_affineChart {D X : Scheme.{u}} (i : D ⟶ X)
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) [M.IsQuasicoherent]
    [Mono ((cartierTensorSection i).app M)] (U : X.Opens) (hU : IsAffineOpen U)
    (a : Γ(X, U)) (ha : IsSMulRegular Γ(X, U) a)
    (hker : RingHom.ker (i.app U).hom = Ideal.span {a}) :
    IsSMulRegular ((moduleSpecΓFunctor (R := Γ(X, U))).obj (M.restrict hU.fromSpec)) a := by
  let e := (affineChartΓIso ⟨U, hU⟩ M).toLinearEquiv
  have hreg := cartierEquation_regular_affineSections i hI M U hU a ha hker
  intro m n h
  apply e.injective
  apply hreg
  exact (e.map_smul a m).symm.trans ((congrArg e h).trans (e.map_smul a n))

private def principalQuotientRingIso {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hs : Function.Surjective φ.hom) (a : R) (hker : RingHom.ker φ.hom = Ideal.span {a}) :
    CommRingCat.of (R ⧸ Ideal.span {a}) ≅ S :=
  ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hs)).toCommRingCatIso

private theorem principalQuotientRingIso_mk {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hs : Function.Surjective φ.hom) (a : R) (hker : RingHom.ker φ.hom = Ideal.span {a}) :
    CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})) ≫
      (principalQuotientRingIso φ hs a hker).hom = φ := by
  ext r
  exact (congrArg (RingHom.quotientKerEquivOfSurjective hs)
    (Ideal.quotEquivOfEq_mk hker.symm r)).trans
      (RingHom.quotientKerEquivOfSurjective_apply_mk hs r)

private def principalQuotientSourceIso {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hs : Function.Surjective φ.hom) (a : R) (hker : RingHom.ker φ.hom = Ideal.span {a}) :
    Spec S ≅ Spec (CommRingCat.of (R ⧸ Ideal.span {a})) :=
  Scheme.Spec.mapIso (principalQuotientRingIso φ hs a hker).op

private theorem principalQuotientSourceIso_factor {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hs : Function.Surjective φ.hom) (a : R) (hker : RingHom.ker φ.hom = Ideal.span {a}) :
    Spec.map φ = (principalQuotientSourceIso φ hs a hker).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))) := by
  have h := congrArg (fun f : R ⟶ S => Spec.map f) (principalQuotientRingIso_mk φ hs a hker)
  exact h.symm.trans (Spec.map_comp _ _)

private theorem closedImmersion_fromSpec_square {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (U : X.Opens) (hU : IsAffineOpen U) :
    IsPullback (hU.preimage i).fromSpec (Spec.map (i.app U)) i hU.fromSpec := by
  let hV := hU.preimage i
  refine ((isPullback_morphismRestrict i U).flip).of_iso
    hV.isoSpec (Iso.refl D) hU.isoSpec (Iso.refl X) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans (hV.isoSpec_hom_fromSpec).symm
  · exact (Scheme.Opens.toSpecΓ_naturality i U).symm
  · simp
  · exact (Category.comp_id _).trans (hU.isoSpec_hom_fromSpec).symm

private structure PrincipalCoefficientChart {D X : Scheme.{u}}
    (i : D ⟶ X) (M : X.Modules) (x : D) where
  U : X.Opens
  affine : IsAffineOpen U
  a : Γ(X, U)
  regular : IsSMulRegular Γ(X, U) a
  source : Spec (CommRingCat.of (Γ(X, U) ⧸ Ideal.span {a})) ⟶ D
  sourceOpen : IsOpenImmersion source
  square : IsPullback source
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))) i affine.fromSpec
  point : Spec (CommRingCat.of (Γ(X, U) ⧸ Ideal.span {a}))
  point_eq : source point = x
  coefficientRegular : IsSMulRegular
    ((moduleSpecΓFunctor (R := Γ(X, U))).obj (M.restrict affine.fromSpec)) a

private theorem nonempty_principalCoefficientChart {D X : Scheme.{u}}
    (i : D ⟶ X) [IsClosedImmersion i] (hI : IsLocallyRankOne X (idealModule i))
    (M : X.Modules) [M.IsQuasicoherent] [Mono ((cartierTensorSection i).app M)] (x : D) :
    Nonempty (PrincipalCoefficientChart i M x) := by
  obtain ⟨U, hU, hxU, a, ha, hker⟩ :=
    exists_affine_regular_idealGenerator_of_isLocallyRankOne i hI (i x)
  let φ := i.app U
  let hs : Function.Surjective φ.hom := i.app_surjective U hU
  let e := principalQuotientSourceIso φ hs a hker
  let b := e.inv ≫ (hU.preimage i).fromSpec
  let : IsOpenImmersion b := inferInstance
  have H : IsPullback b
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))) i hU.fromSpec := by
    refine (closedImmersion_fromSpec_square i U hU).of_iso
      e (Iso.refl D) (Iso.refl _) (Iso.refl X) ?_ ?_ ?_ ?_
    · simp [b]
    · exact (Category.comp_id _).trans (principalQuotientSourceIso_factor φ hs a hker)
    · simp
    · simp
  let y := hU.primeIdealOf ⟨i x, hxU⟩
  obtain ⟨z, hz, -⟩ := exists_preimage_of_isPullback H x y
    (hU.fromSpec_primeIdealOf ⟨i x, hxU⟩).symm
  exact ⟨⟨U, hU, a, ha, b, inferInstance, H, z, hz,
    cartierEquation_regular_affineChart i hI M U hU a ha hker⟩⟩

/-- Actual principal charts and the original homology exchange give global Cartier concentration. -/
public theorem derivedClosedImmersionRightAdjointCartierHomology_isZero
    {D X : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) [M.IsQuasicoherent]
    [Mono ((cartierTensorSection i).app M)] (q : ℤ) (hq : q ≠ 1) :
    IsZero (derivedClosedImmersionRightAdjointHomology i M q) := by
  classical
  let C (x : D) : PrincipalCoefficientChart i M x :=
    Classical.choice (nonempty_principalCoefficientChart i hI M x)
  let Y (x : D) := Spec (CommRingCat.of (Γ(X, (C x).U) ⧸ Ideal.span {(C x).a}))
  let b (x : D) : Y x ⟶ D := (C x).source
  let : ∀ x, IsOpenImmersion (b x) := fun x => (C x).sourceOpen
  apply isZero_of_restrict_openCover Y b (fun x => ⟨x, (C x).point, (C x).point_eq⟩)
  intro x
  let R := Γ(X, (C x).U)
  let : IsNoetherianRing R :=
    IsLocallyNoetherian.component_noetherian ⟨(C x).U, (C x).affine⟩
  let N := M.restrict (C x).affine.fromSpec
  let : N.IsQuasicoherent := inferInstance
  have hz := derivedClosedImmersionRightAdjointPrincipalHomology_isZero
    (C x).a (C x).regular N (injectiveResolution N) (C x).coefficientRegular q hq
  exact hz.of_iso
    (derivedClosedImmersionRightAdjointOpenHomologyIso (b x)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {(C x).a}))))
      i (C x).affine.fromSpec (C x).square M q)

/-- The original installed closed right-adjoint value on the original coefficient single. -/
public abbrev globalCartierDerivedObject {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (M : X.Modules) : DerivedCategory.Plus D.Modules :=
  (derivedClosedImmersionRightAdjointPlus i).obj
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)

/-- Lower concentration bound for the original installed global Cartier value. -/
public theorem derivedClosedImmersionRightAdjointCartier_isGE
    {D X : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) [M.IsQuasicoherent]
    [Mono ((cartierTensorSection i).app M)] : (globalCartierDerivedObject i M).IsGE 1 := by
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
  intro q hq
  exact derivedClosedImmersionRightAdjointCartierHomology_isZero i hI M q (ne_of_lt hq)

/-- Upper concentration bound for the original installed global Cartier value. -/
public theorem derivedClosedImmersionRightAdjointCartier_isLE
    {D X : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) [M.IsQuasicoherent]
    [Mono ((cartierTensorSection i).app M)] : (globalCartierDerivedObject i M).IsLE 1 := by
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff, DerivedCategory.isLE_iff]
  intro q hq
  exact derivedClosedImmersionRightAdjointCartierHomology_isZero i hI M q (ne_of_gt hq)

/-- Concentration compares the original installed value with its own actual first homology. -/
public def derivedClosedImmersionRightAdjointCartierHeartIso
    {D X : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) [M.IsQuasicoherent]
    [Mono ((cartierTensorSection i).app M)] :
    (DerivedCategory.Plus.ι.obj (globalCartierDerivedObject i M))⟦(1 : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor D.Modules 0).obj
        (derivedClosedImmersionRightAdjointHomology i M 1) := by
  let K := globalCartierDerivedObject i M
  letI := derivedClosedImmersionRightAdjointCartier_isGE i hI M
  letI := derivedClosedImmersionRightAdjointCartier_isLE i hI M
  exact (shiftFunctor (DerivedCategory D.Modules) (1 : ℤ)).mapIso
    (DerivedCategory.Plus.ι.mapIso (DerivedCategory.Plus.isoSingleHomology K 1)) ≪≫
    ((DerivedCategory.singleFunctors D.Modules).shiftIso 1 0 1 (by omega)).app
      (derivedClosedImmersionRightAdjointHomology i M 1)

/-- The original derived adjoint of the positive original global Cartier extension class. -/
public def cartierCoefficientExtensionMate {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules)
    [Mono ((cartierTensorSection i).app M)] :
    (DerivedCategory.singleFunctor D.Modules 0).obj
      ((pullback i).obj (tensorSheaf X (dualSheaf X (idealModule i)) M)) ⟶
        (DerivedCategory.Plus.ι.obj (globalCartierDerivedObject i M))⟦(1 : ℤ)⟧ :=
  (closedImmersionRightAdjunction i).singleDerivedHomEquivOfInjectiveResolution
    ((pullback i).obj (tensorSheaf X (dualSheaf X (idealModule i)) M))
    (injectiveResolution M) 1 (cartierCoefficientSequence_shortExact i hI M).extClass.hom

/-- The actual global positive mate is invertible; its row and concentration are derived. -/
public theorem cartierCoefficientExtensionMate_isIso
    {D X : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) [M.IsQuasicoherent]
    [Mono ((cartierTensorSection i).app M)] : IsIso (cartierCoefficientExtensionMate i hI M) := by
  let L : LineBundle X := dualLineBundle X ⟨idealModule i, hI⟩
  let K := moduleTensorLeftFunctor X L.val
  let τ : 𝟭 X.Modules ⟶ K := cartierTensorSection i
  let : IsFiniteLocallyFree X L.val := isFiniteLocallyFree_of_isLocallyRankOne L.property
  let : K.Additive := moduleTensorLeftFunctor_additive X L.val
  let : K.PreservesHomology := moduleTensorLeft_preservesHomology L.val
  let : PreservesFiniteLimits K := Functor.preservesFiniteLimits_of_preservesHomology K
  let : PreservesFiniteColimits K := Functor.preservesFiniteColimits_of_preservesHomology K
  let H := fullyFaithfulPushforwardOfClosedImmersion i
  let := H.full
  let := H.faithful
  let : Mono (τ.app (K.obj M)) := cartierTensorSection_twist_mono i hI M
  exact CategoryTheory.Adjunction.sectionExtensionMate_isIso
    (closedImmersionRightAdjunction i) K τ M
    ((pullback i).obj (tensorSheaf X (dualSheaf X (idealModule i)) M))
    ((pullbackPushforwardAdjunction i).unit.app
      (tensorSheaf X (dualSheaf X (idealModule i)) M))
    (cartierCoefficientSequence_zero i hI M) (cartierCoefficientSequence_shortExact i hI M)
    (cartierTensorSection_pushforward_eq_zero i hI)
    (derivedClosedImmersionRightAdjointHomology i M 1)
    (derivedClosedImmersionRightAdjointCartierHeartIso i hI M)

/-- Inverting the original mate gives the positive normalized degree-one purity isomorphism. -/
public def derivedClosedImmersionRightAdjointCartierDegreeOneIso
    {D X : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) [M.IsQuasicoherent]
    [Mono ((cartierTensorSection i).app M)] :
    (DerivedCategory.Plus.ι.obj (globalCartierDerivedObject i M))⟦(1 : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor D.Modules 0).obj
        ((pullback i).obj (tensorSheaf X (dualSheaf X (idealModule i)) M)) := by
  letI := cartierCoefficientExtensionMate_isIso i hI M
  exact (asIso (cartierCoefficientExtensionMate i hI M)).symm

/-- The actual positive purity comparison has exactly the original global row as its counit. -/
public theorem derivedClosedImmersionRightAdjointCartierDegreeOneIso_counit
    {D X : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) [M.IsQuasicoherent]
    [Mono ((cartierTensorSection i).app M)] :
    ((closedImmersionRightAdjunction i).singleDerivedHomEquivOfInjectiveResolution
      ((pullback i).obj (tensorSheaf X (dualSheaf X (idealModule i)) M))
      (injectiveResolution M) 1).symm
        (derivedClosedImmersionRightAdjointCartierDegreeOneIso i hI M).inv =
      (cartierCoefficientSequence_shortExact i hI M).extClass.hom := by
  change ((closedImmersionRightAdjunction i).singleDerivedHomEquivOfInjectiveResolution
    ((pullback i).obj (tensorSheaf X (dualSheaf X (idealModule i)) M))
    (injectiveResolution M) 1).symm (cartierCoefficientExtensionMate i hI M) = _
  exact ((closedImmersionRightAdjunction i).singleDerivedHomEquivOfInjectiveResolution
    ((pullback i).obj (tensorSheaf X (dualSheaf X (idealModule i)) M))
    (injectiveResolution M) 1).symm_apply_apply _

/-- The original single-shift and full faithfulness give global purity in native degree one. -/
public def cartierSingleShiftIso {D : Scheme.{u}} (Q : D.Modules) :
    ((DerivedCategory.singleFunctor D.Modules 1).obj Q)⟦(1 : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor D.Modules 0).obj Q :=
  ((DerivedCategory.singleFunctors D.Modules).shiftIso 1 0 1 (by omega)).app Q

/-- The original single-shift and full faithfulness give global purity in native degree one. -/
public def derivedClosedImmersionRightAdjointCartierIso
    {D X : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) [M.IsQuasicoherent]
    [Mono ((cartierTensorSection i).app M)] :
    globalCartierDerivedObject i M ≅ (DerivedCategory.Plus.singleFunctor D.Modules 1).obj
      ((pullback i).obj (tensorSheaf X (dualSheaf X (idealModule i)) M)) :=
  (DerivedCategory.Plus.ι : DerivedCategory.Plus D.Modules ⥤ DerivedCategory D.Modules).preimageIso
    ((shiftFunctor (DerivedCategory D.Modules) (1 : ℤ)).preimageIso
      (derivedClosedImmersionRightAdjointCartierDegreeOneIso i hI M ≪≫
        (cartierSingleShiftIso
          ((pullback i).obj (tensorSheaf X (dualSheaf X (idealModule i)) M))).symm))

/-- The unshifted global isomorphism retains the exact positive degree-one inverse map. -/
public theorem derivedClosedImmersionRightAdjointCartierIso_shift_inv
    {D X : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) [M.IsQuasicoherent]
    [Mono ((cartierTensorSection i).app M)] :
    (cartierSingleShiftIso
      ((pullback i).obj (tensorSheaf X (dualSheaf X (idealModule i)) M))).inv ≫
        (shiftFunctor (DerivedCategory D.Modules) (1 : ℤ)).map
          (DerivedCategory.Plus.ι.map (derivedClosedImmersionRightAdjointCartierIso i hI M).inv) =
      (derivedClosedImmersionRightAdjointCartierDegreeOneIso i hI M).inv := by
  exact globalTwoPreimageInv
    (DerivedCategory.Plus.ι : DerivedCategory.Plus D.Modules ⥤ DerivedCategory D.Modules)
    (shiftFunctor (DerivedCategory D.Modules) (1 : ℤ))
    (X := globalCartierDerivedObject i M)
    (Y := (DerivedCategory.Plus.singleFunctor D.Modules 1).obj
      ((pullback i).obj (tensorSheaf X (dualSheaf X (idealModule i)) M)))
    (derivedClosedImmersionRightAdjointCartierDegreeOneIso i hI M)
    (cartierSingleShiftIso ((pullback i).obj (tensorSheaf X (dualSheaf X (idealModule i)) M)))

/-- Actual counit normalization of the unshifted installed global purity isomorphism. -/
public theorem derivedClosedImmersionRightAdjointCartierIso_counit
    {D X : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) [M.IsQuasicoherent]
    [Mono ((cartierTensorSection i).app M)] :
    ((closedImmersionRightAdjunction i).singleDerivedHomEquivOfInjectiveResolution
      ((pullback i).obj (tensorSheaf X (dualSheaf X (idealModule i)) M))
      (injectiveResolution M) 1).symm
        ((cartierSingleShiftIso
          ((pullback i).obj (tensorSheaf X (dualSheaf X (idealModule i)) M))).inv ≫
          (shiftFunctor (DerivedCategory D.Modules) (1 : ℤ)).map
            (DerivedCategory.Plus.ι.map
              (derivedClosedImmersionRightAdjointCartierIso i hI M).inv)) =
      (cartierCoefficientSequence_shortExact i hI M).extClass.hom := by
  exact (congrArg
    ((closedImmersionRightAdjunction i).singleDerivedHomEquivOfInjectiveResolution
      ((pullback i).obj (tensorSheaf X (dualSheaf X (idealModule i)) M))
      (injectiveResolution M) 1).symm
    (derivedClosedImmersionRightAdjointCartierIso_shift_inv i hI M)).trans
      (derivedClosedImmersionRightAdjointCartierDegreeOneIso_counit i hI M)

/-- The actual first homology is the genuine pulled-back dual-ideal coefficient. -/
public def derivedClosedImmersionRightAdjointCartierHomologyIso
    {D X : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) [M.IsQuasicoherent]
    [Mono ((cartierTensorSection i).app M)] :
    derivedClosedImmersionRightAdjointHomology i M 1 ≅
      (pullback i).obj (tensorSheaf X (dualSheaf X (idealModule i)) M) :=
  (DerivedCategory.Plus.homologyFunctor D.Modules 1).mapIso
    (derivedClosedImmersionRightAdjointCartierIso i hI M) ≪≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := D.Modules) 1).app
        ((pullback i).obj (tensorSheaf X (dualSheaf X (idealModule i)) M))

end AlgebraicGeometry.Scheme.Modules
