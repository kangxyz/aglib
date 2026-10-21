/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Normalization.InertiaTorsor.AffineAlgebraization
public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.ArbitraryGalois
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.MarkedCoefficients

/-!
# Realization of original field cocycles with actual Hopf coefficients

The supplied finite étale cocommutative Hopf algebra and its actual Ω-point
coordinates determine the same coefficient scheme. The native Galois-category
descent constructs a finite étale cover, its global-section algebra, coaction,
bijective transporter and actual Ω-point. Uniqueness of positive transport
proves equality with the input cocycle and its continuous H¹ class.
Finiteness of Lambda is derived from the supplied mark; it is not an extra input.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.MonObj CategoryTheory.PreGaloisCategory FintypeCatDiscrete
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber fiberToFinite)
open _root_.AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent
open _root_.CategoryTheory
open AlgebraicGeometry.Scheme.FiniteEtale.Adic
open _root_.GroupCohomology.ContinuousH1
open _root_.AlgebraicGeometry.Scheme.EtaleH1 _root_.CategoryTheory.Abelian
open _root_.CategoryTheory.Functor.LargePresheaf
open AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor
open AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.OverRing Algebra.FiniteEtale.TorsorExtension
open Algebra.FiniteEtale.GenericMaps
open AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.Arbitrary
open AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor.AffineAlgebraization

namespace AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor.FieldRealization
universe u
attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory
  _root_.AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent.coverCartesian

variable (K Ω C Lambda : Type u) [Field K] [Field Ω] [Algebra K Ω]
  [hGalois : IsGalois K Ω] [hAlgClosed : IsAlgClosed Ω]
  [CommRing C] [HopfAlgebra K C] [hCocomm : Coalgebra.IsCocomm K C]
  [hFinite : Module.Finite K C] [hEtale : Algebra.Etale K C]
  [hAddGroup : AddCommGroup Lambda] [hTopology : TopologicalSpace Lambda]
  [hDiscrete : DiscreteTopology Lambda]
  [hTopAdd : IsTopologicalAddGroup Lambda]
  [hAction : DistribMulAction (Ω ≃ₐ[K] Ω) Lambda]
  [hContinuous : ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]
  (mark : Lambda ≃ (C →ₐ[K] Ω))
  (hadd : ∀ a b : Lambda, mark (a + b) =
    (Algebra.TensorProduct.lift (mark a) (mark b) (fun _ _ => .all _ _)).comp
      (Bialgebra.comulAlgHom K C))
  (hgal : ∀ (σ : Ω ≃ₐ[K] Ω) a, σ.toAlgHom.comp (mark a) = mark (σ • a))
  [hCategory : GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
  [hFibre : PreGaloisCategory.FiberFunctor (fiberToFinite (basePoint K Ω))]

/-- The group-object structure on the affine carrier of the original coefficient Hopf group. -/
local instance : GrpObj (affine K C) := (coefficientGroup K C).grp

/-- The continuous inverse of the equivalence for the original Ω-valued fibre functor. -/
abbrev inverseGaloisMap : FiberAutGroup (basePoint K Ω) →ₜ* (Ω ≃ₐ[K] Ω) :=
  ContinuousMonoidHom.toContinuousMonoidHom ((fundamentalGroupContinuousEquiv K Ω).symm)

/-- The given Ω-Galois action transported along the reconstructed inverse. -/
abbrev fieldAction : DistribMulAction (FiberAutGroup (basePoint K Ω)) Lambda :=
  restrictedAction Lambda (inverseGaloisMap K Ω)

omit hAlgClosed hDiscrete hTopAdd hCategory hFibre in
theorem fieldAction_continuous
    [_hAlgClosed : IsAlgClosed Ω]
    [_hDiscrete : DiscreteTopology Lambda]
    [_hTopAdd : IsTopologicalAddGroup Lambda]
    [_hCategory : GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
    [_hFibre : PreGaloisCategory.FiberFunctor (fiberToFinite (basePoint K Ω))] :
    letI := fieldAction K Ω Lambda
    ContinuousSMul (FiberAutGroup (basePoint K Ω)) Lambda :=
  restrictedAction_continuous Lambda (inverseGaloisMap K Ω)

/-- The coordinates are actual scheme points of the original field coefficient algebra. -/
def coefficientCoordinates : Lambda ≃ (affine K Ω ⟶ (coefficientGroup K C).X) :=
  mark.trans (affinePointEquiv K C Ω).symm

include hadd in
omit hGalois hAlgClosed hFinite hEtale hTopology hDiscrete hTopAdd hAction hContinuous
  hCategory hFibre in
theorem coefficientCoordinates_add
    [_hGalois : IsGalois K Ω]
    [_hAlgClosed : IsAlgClosed Ω]
    [_hFinite : Module.Finite K C]
    [_hEtale : Algebra.Etale K C]
    [_hTopology : TopologicalSpace Lambda]
    [_hDiscrete : DiscreteTopology Lambda]
    [_hTopAdd : IsTopologicalAddGroup Lambda]
    [_hAction : DistribMulAction (Ω ≃ₐ[K] Ω) Lambda]
    [_hContinuous : ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]
    [_hCategory : GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
    [_hFibre : PreGaloisCategory.FiberFunctor (fiberToFinite (basePoint K Ω))]
    (a b : Lambda) :
    coefficientCoordinates K Ω C Lambda mark (a + b) =
      coefficientCoordinates K Ω C Lambda mark a * coefficientCoordinates K Ω C Lambda mark b := by
  change algebraPoint K C Ω (mark (a + b)) = _
  rw [hadd]
  exact (algebraPoint_coefficient_mul K C Ω (mark a) (mark b)).symm

include hgal in
omit hGalois hAlgClosed hCocomm hFinite hEtale hTopology hDiscrete hTopAdd hContinuous
  hCategory hFibre in
theorem coefficientCoordinates_galois
    [_hGalois : IsGalois K Ω]
    [_hAlgClosed : IsAlgClosed Ω]
    [_hCocomm : Coalgebra.IsCocomm K C]
    [_hFinite : Module.Finite K C]
    [_hEtale : Algebra.Etale K C]
    [_hTopology : TopologicalSpace Lambda]
    [_hDiscrete : DiscreteTopology Lambda]
    [_hTopAdd : IsTopologicalAddGroup Lambda]
    [_hContinuous : ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]
    [_hCategory : GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
    [_hFibre : PreGaloisCategory.FiberFunctor (fiberToFinite (basePoint K Ω))]
    (σ : Ω ≃ₐ[K] Ω) (a : Lambda) :
    coefficientCoordinates K Ω C Lambda mark (σ • a) =
      pointEnd K K Ω σ ≫ coefficientCoordinates K Ω C Lambda mark a := by
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext c
  exact (DFunLike.congr_fun (hgal σ a) c).symm

include hadd in
/-- The multiplicative marking induced by the supplied additive Hopf-point coordinates. -/
def coefficientMark : (affine K Ω ⟶ (coefficientGroup K C).X) ≃* Multiplicative Lambda :=
  MulEquiv.symm {
    toFun := fun a : Multiplicative Lambda => coefficientCoordinates K Ω C Lambda mark a.toAdd
    invFun := fun p => Multiplicative.ofAdd ((coefficientCoordinates K Ω C Lambda mark).symm p)
    left_inv := fun a => (coefficientCoordinates K Ω C Lambda mark).symm_apply_apply a.toAdd
    right_inv := fun p => (coefficientCoordinates K Ω C Lambda mark).apply_symm_apply p
    map_mul' := fun a b => coefficientCoordinates_add K Ω C Lambda mark hadd a.toAdd b.toAdd }

theorem coefficientMark_coordinates (a : Lambda) :
    coefficientMark K Ω C Lambda mark hadd (coefficientCoordinates K Ω C Lambda mark a) =
      Multiplicative.ofAdd a := by
  change Multiplicative.ofAdd ((coefficientCoordinates K Ω C Lambda mark).symm
    (coefficientCoordinates K Ω C Lambda mark a)) = _
  rw [Equiv.symm_apply_apply]

include hgal in
theorem coefficientMark_equivariant :
    letI := fieldAction K Ω Lambda
    ∀ (γ : FiberAutGroup (basePoint K Ω)) p,
      coefficientMark K Ω C Lambda mark hadd (γ.hom.app (coefficientCover (coefficientGroup K C)) p)
        =
      Multiplicative.ofAdd (γ • (coefficientMark K Ω C Lambda mark hadd p).toAdd) := by
  let := fieldAction K Ω Lambda
  intro γ p
  obtain ⟨σ, rfl⟩ := galoisToFibre_surjective K Ω γ
  obtain ⟨a, rfl⟩ := (coefficientCoordinates K Ω C Lambda mark).surjective p
  rw [galoisToFibre_apply, ← coefficientCoordinates_galois K Ω C Lambda mark hgal,
    coefficientMark_coordinates, coefficientMark_coordinates]
  change Multiplicative.ofAdd (σ • a) =
    Multiplicative.ofAdd ((fundamentalGroupContinuousEquiv K Ω).symm (galoisToFibre K K Ω σ) • a)
  exact congrArg (fun σ : Ω ≃ₐ[K] Ω => Multiplicative.ofAdd (σ • a))
    ((fundamentalGroupContinuousEquiv K Ω).symm_apply_apply σ).symm

include mark in
omit hGalois hAlgClosed hCocomm hAddGroup hTopology hDiscrete hTopAdd hAction hContinuous
  hCategory hFibre in
theorem coefficientFinite
    [_hGalois : IsGalois K Ω]
    [_hAlgClosed : IsAlgClosed Ω]
    [_hCocomm : Coalgebra.IsCocomm K C]
    [_hAddGroup : AddCommGroup Lambda]
    [_hTopology : TopologicalSpace Lambda]
    [_hDiscrete : DiscreteTopology Lambda]
    [_hTopAdd : IsTopologicalAddGroup Lambda]
    [_hAction : DistribMulAction (Ω ≃ₐ[K] Ω) Lambda]
    [_hContinuous : ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]
    [_hCategory : GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
    [_hFibre : PreGaloisCategory.FiberFunctor
      (fiberToFinite (basePoint K Ω))] : Finite Lambda :=
  Finite.of_equiv ((fiberToFinite (basePoint K Ω)).obj (coefficientCover (coefficientGroup K C)))
    (coefficientCoordinates K Ω C Lambda mark).symm

/-- The module descent is identified with the ACTUAL coefficient Hopf scheme. -/
def coefficientIso :
    letI := coefficientFinite K Ω C Lambda mark
    letI := fieldAction K Ω Lambda
    letI := fieldAction_continuous K Ω Lambda
    moduleScheme (basePoint K Ω) Lambda ≅ coefficientGroup K C := by
  letI := coefficientFinite K Ω C Lambda mark
  letI := fieldAction K Ω Lambda
  letI := fieldAction_continuous K Ω Lambda
  exact MarkedCoefficients.moduleGroupIso (basePoint K Ω) (coefficientGroup K C) Lambda
    (coefficientMark K Ω C Lambda mark hadd) (coefficientMark_equivariant K Ω C Lambda mark hadd
      hgal)

/-- Native cocycles are transported through the inverse of the literal field map. -/
def liftedCocycle (c : Cocycle (Ω ≃ₐ[K] Ω) Lambda) :
    letI := fieldAction K Ω Lambda
    Cocycle (FiberAutGroup (basePoint K Ω)) Lambda :=
  restrictionCocycles Lambda (inverseGaloisMap K Ω) c

omit hAlgClosed hDiscrete hContinuous hCategory hFibre in
@[simp] theorem liftedCocycle_galois
    [_hAlgClosed : IsAlgClosed Ω]
    [_hDiscrete : DiscreteTopology Lambda]
    [_hContinuous : ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]
    [_hCategory : GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
    [_hFibre : PreGaloisCategory.FiberFunctor (fiberToFinite (basePoint K Ω))]
    (c : Cocycle (Ω ≃ₐ[K] Ω) Lambda) (σ : Ω ≃ₐ[K] Ω) :
    letI := fieldAction K Ω Lambda
    (liftedCocycle K Ω Lambda c).val (galoisToFibre K K Ω σ) = c.val σ := by
  let := fieldAction K Ω Lambda
  change c.val ((fundamentalGroupContinuousEquiv K Ω).symm (galoisToFibre K K Ω σ)) = c.val σ
  exact congrArg c.val ((fundamentalGroupContinuousEquiv K Ω).symm_apply_apply σ)

/-- An actual finite-etale cover, constructed from the original native cocycle. -/
def realizedCover (c : Cocycle (Ω ≃ₐ[K] Ω) Lambda) : Scheme.FiniteEtale (Spec (.of K)) := by
  letI := coefficientFinite K Ω C Lambda mark
  letI := fieldAction K Ω Lambda
  letI := fieldAction_continuous K Ω Lambda
  exact ContinuousTorsors.cocycleCover (basePoint K Ω) (liftedCocycle K Ω Lambda c)

/-- The native scheme torsor action on the finite cover descended from the input cocycle. -/
def realizedModuleAction (c : Cocycle (Ω ≃ₐ[K] Ω) Lambda) :
    letI := coefficientFinite K Ω C Lambda mark
    letI := fieldAction K Ω Lambda
    letI := fieldAction_continuous K Ω Lambda
    TorsorAction (moduleScheme (basePoint K Ω) Lambda)
      (toUnit (realizedCover K Ω C Lambda mark c).obj) := by
  letI := coefficientFinite K Ω C Lambda mark
  letI := fieldAction K Ω Lambda
  letI := fieldAction_continuous K Ω Lambda
  exact ContinuousTorsors.cocycleSchemeAction (basePoint K Ω) (liftedCocycle K Ω Lambda c)

/-- The actual Ω-valued base point of the descended cocycle cover. -/
def realizedSchemePoint (c : Cocycle (Ω ≃ₐ[K] Ω) Lambda) :
    Fiber (basePoint K Ω) (realizedCover K Ω C Lambda mark c) := by
  letI := coefficientFinite K Ω C Lambda mark
  letI := fieldAction K Ω Lambda
  letI := fieldAction_continuous K Ω Lambda
  exact ContinuousTorsors.cocycleBasepoint (basePoint K Ω) (liftedCocycle K Ω Lambda c)

/-- The ACTUAL global-section algebra of the descended finite-etale cover. -/
def realizedAlgebra (c : Cocycle (Ω ≃ₐ[K] Ω) Lambda) : CommAlgCat.{u} K := by
  let Y := realizedCover K Ω C Lambda mark c
  letI := sectionsAlgebra K Y
  exact CommAlgCat.of K (sections K Y)

theorem realizedAlgebra_finite (c : Cocycle (Ω ≃ₐ[K] Ω) Lambda) :
    Module.Finite K (realizedAlgebra K Ω C Lambda mark c) :=
  sections_finite K (realizedCover K Ω C Lambda mark c)

theorem realizedAlgebra_etale (c : Cocycle (Ω ≃ₐ[K] Ω) Lambda) :
    Algebra.Etale K (realizedAlgebra K Ω C Lambda mark c) :=
  sections_etale K (realizedCover K Ω C Lambda mark c)

/-- The descended scheme is identified with this actual coordinate algebra over K. -/
def realizedAlgebraIso (c : Cocycle (Ω ≃ₐ[K] Ω) Lambda) :
    (realizedCover K Ω C Lambda mark c).obj ≅ affine K (realizedAlgebra K Ω C Lambda mark c) :=
  affineCoverPresentation K (realizedCover K Ω C Lambda mark c)

/-- The Ω-point gives the required actual algebra map A -> Ω. -/
def realizedPoint (c : Cocycle (Ω ≃ₐ[K] Ω) Lambda) :
    realizedAlgebra K Ω C Lambda mark c →ₐ[K] Ω :=
  affineCoverPoint K Ω (realizedCover K Ω C Lambda mark c) (realizedSchemePoint K Ω C Lambda mark c)

@[simp] theorem realizedPoint_scheme (c : Cocycle (Ω ≃ₐ[K] Ω) Lambda) :
    algebraPoint K (realizedAlgebra K Ω C Lambda mark c) Ω (realizedPoint K Ω C Lambda mark c) =
      realizedSchemePoint K Ω C Lambda mark c ≫ (realizedAlgebraIso K Ω C Lambda mark c).hom :=
  algebraPoint_affineCoverPoint K Ω (realizedCover K Ω C Lambda mark c)
    (realizedSchemePoint K Ω C Lambda mark c)

theorem realizedAlgebra_nontrivial (c : Cocycle (Ω ≃ₐ[K] Ω) Lambda) :
    Nontrivial (realizedAlgebra K Ω C Lambda mark c) :=
  (realizedPoint K Ω C Lambda mark c).toRingHom.domain_nontrivial

/-- The scheme action is transported through the DERIVED coefficient-group
and affine-carrier isomorphisms to the actual original Hopf group and Spec(A). -/
def realizedAffineAction (c : Cocycle (Ω ≃ₐ[K] Ω) Lambda) :
    TorsorAction (coefficientGroup K C)
      (toUnit (affine K (realizedAlgebra K Ω C Lambda mark c))) := by
  letI := coefficientFinite K Ω C Lambda mark
  letI := fieldAction K Ω Lambda
  letI := fieldAction_continuous K Ω Lambda
  exact relabelTorsor (realizedModuleAction K Ω C Lambda mark c)
    (coefficientIso K Ω C Lambda mark hadd hgal) (realizedAlgebraIso K Ω C Lambda mark c)

/-- The actual algebraic coaction, including both derived algebra diagrams. -/
def realizedCoaction (c : Cocycle (Ω ≃ₐ[K] Ω) Lambda) :
    AlgebraCoaction K (realizedAlgebra K Ω C Lambda mark c) C
      (Bialgebra.counitAlgHom K C) (Bialgebra.comulAlgHom K C) :=
  algebraCoactionOfTorsor K (realizedAlgebra K Ω C Lambda mark c) C
    (realizedAffineAction K Ω C Lambda mark hadd hgal c)

/-- Bijectivity of the actual algebra transporter is an output of the scheme
unique-transport construction and the inverse affine dictionary. -/
theorem realized_transporter_bijective (c : Cocycle (Ω ≃ₐ[K] Ω) Lambda) :
    Function.Bijective
      (transporter K (realizedAlgebra K Ω C Lambda mark c) C
        (realizedCoaction K Ω C Lambda mark hadd hgal c).coact) :=
  actionCoact_transporter_bijective K (realizedAlgebra K Ω C Lambda mark c) C
    (realizedAffineAction K Ω C Lambda mark hadd hgal c)

/-- The coefficient identification sends ORIGINAL coordinates to the same
module-descent coordinates, including the inverse needed by action transport. -/
theorem coefficientIso_inv_coordinates (a : Lambda) :
    letI := coefficientFinite K Ω C Lambda mark
    letI := fieldAction K Ω Lambda
    letI := fieldAction_continuous K Ω Lambda
    coefficientCoordinates K Ω C Lambda mark a ≫
        (coefficientIso K Ω C Lambda mark hadd hgal).inv.hom.hom =
      (moduleFiberMulEquiv (basePoint K Ω) Lambda).symm (Multiplicative.ofAdd a) := by
  let := coefficientFinite K Ω C Lambda mark
  let := fieldAction K Ω Lambda
  let := fieldAction_continuous K Ω Lambda
  let e := coefficientIso K Ω C Lambda mark hadd hgal
  have he : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 (coefficientGroup K C).X :=
    congrArg (fun f : coefficientGroup K C ⟶ coefficientGroup K C => f.hom.hom) e.inv_hom_id
  apply (moduleFiberMulEquiv (basePoint K Ω) Lambda).injective
  rw [MulEquiv.apply_symm_apply]
  have h := MarkedCoefficients.moduleGroupIso_marking (basePoint K Ω) (coefficientGroup K C) Lambda
    (coefficientMark K Ω C Lambda mark hadd) (coefficientMark_equivariant K Ω C Lambda mark hadd
      hgal)
    (coefficientCoordinates K Ω C Lambda mark a ≫ e.inv.hom.hom)
  change coefficientMark K Ω C Lambda mark hadd
    ((coefficientCoordinates K Ω C Lambda mark a ≫ e.inv.hom.hom) ≫ e.hom.hom.hom) = _ at h
  simpa only [Category.assoc, he, Category.comp_id, coefficientMark_coordinates] using h.symm

/-- The descended zero point has exactly the original positive cocycle displacement. -/
theorem realizedModuleAction_galois (c : Cocycle (Ω ≃ₐ[K] Ω) Lambda) (σ : Ω ≃ₐ[K] Ω) :
    letI := coefficientFinite K Ω C Lambda mark
    letI := fieldAction K Ω Lambda
    letI := fieldAction_continuous K Ω Lambda
    (realizedModuleAction K Ω C Lambda mark c).act
      ((moduleFiberMulEquiv (basePoint K Ω) Lambda).symm (Multiplicative.ofAdd (c.val σ)))
      (realizedSchemePoint K Ω C Lambda mark c) =
    pointEnd K K Ω σ ≫ realizedSchemePoint K Ω C Lambda mark c := by
  let := coefficientFinite K Ω C Lambda mark
  let := fieldAction K Ω Lambda
  let := fieldAction_continuous K Ω Lambda
  have h := ContinuousTorsors.basedCocycle_action (basePoint K Ω)
    (moduleScheme (basePoint K Ω) Lambda)
    (ContinuousTorsors.cocycleCover (basePoint K Ω) (liftedCocycle K Ω Lambda c))
    (ContinuousTorsors.cocycleSchemeAction (basePoint K Ω) (liftedCocycle K Ω Lambda c))
    (moduleFiberMulEquiv (basePoint K Ω) Lambda) (moduleFiber_action (basePoint K Ω) Lambda)
    (ContinuousTorsors.cocycleBasepoint (basePoint K Ω) (liftedCocycle K Ω Lambda c))
    (galoisToFibre K K Ω σ)
  rw [ContinuousTorsors.basedCocycle_cocycleSchemeAction, liftedCocycle_galois, galoisToFibre_apply]
    at h
  exact h

/-- Transport to the actual original Hopf coefficient and Spec(A) preserves
that positive original-Galois point equation literally. -/
theorem realizedAffineAction_galois (c : Cocycle (Ω ≃ₐ[K] Ω) Lambda) (σ : Ω ≃ₐ[K] Ω) :
    (realizedAffineAction K Ω C Lambda mark hadd hgal c).act
      (algebraPoint K C Ω (mark (c.val σ)))
      (algebraPoint K (realizedAlgebra K Ω C Lambda mark c) Ω (realizedPoint K Ω C Lambda mark c)) =
    pointEnd K K Ω σ ≫
      algebraPoint K (realizedAlgebra K Ω C Lambda mark c) Ω
        (realizedPoint K Ω C Lambda mark c) := by
  let := coefficientFinite K Ω C Lambda mark
  let := fieldAction K Ω Lambda
  let := fieldAction_continuous K Ω Lambda
  rw [realizedPoint_scheme]
  change (relabelTorsor (realizedModuleAction K Ω C Lambda mark c)
      (coefficientIso K Ω C Lambda mark hadd hgal) (realizedAlgebraIso K Ω C Lambda mark c)).act
    (coefficientCoordinates K Ω C Lambda mark (c.val σ))
    (realizedSchemePoint K Ω C Lambda mark c ≫ (realizedAlgebraIso K Ω C Lambda mark c).hom) = _
  rw [relabelTorsor_act, coefficientIso_inv_coordinates]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [realizedModuleAction_galois]
  exact Category.assoc _ _ _

/-- The extracted algebraic coaction realizes the same ORIGINAL positive
transporter equation on its actual algebra point. -/
theorem realized_translate_galois (c : Cocycle (Ω ≃ₐ[K] Ω) Lambda) (σ : Ω ≃ₐ[K] Ω) :
    Algebra.FiniteEtale.TorsorCocycle.translate K Ω (realizedAlgebra K Ω C Lambda mark c) C
      (realizedCoaction K Ω C Lambda mark hadd hgal c) (mark (c.val σ))
      (realizedPoint K Ω C Lambda mark c) =
    σ.toAlgHom.comp (realizedPoint K Ω C Lambda mark c) := by
  apply (affinePointEquiv K (realizedAlgebra K Ω C Lambda mark c) Ω).symm.injective
  change algebraPoint K (realizedAlgebra K Ω C Lambda mark c) Ω
    (evaluateCoaction K (realizedAlgebra K Ω C Lambda mark c) C
      (actionCoact K (realizedAlgebra K Ω C Lambda mark c) C
        (realizedAffineAction K Ω C Lambda mark hadd hgal c))
      (mark (c.val σ)) (realizedPoint K Ω C Lambda mark c)) = _
  rw [actionCoact_eval, realizedAffineAction_galois]
  exact algebraPoint_comp K (realizedAlgebra K Ω C Lambda mark c) Ω Ω
    (realizedPoint K Ω C Lambda mark c) σ.toAlgHom

/-- Source K2-018#prop:k2018-arithmetic-characters, revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982: the actual finite-etale coordinate
algebra, derived coaction, bijective transporter and actual Ω-point realize the
input ORIGINAL continuous cocycle, by uniqueness of positive transport. -/
theorem realized_basedCocycle_eq (c : Cocycle (Ω ≃ₐ[K] Ω) Lambda) :
    letI := realizedAlgebra_finite K Ω C Lambda mark c
    Algebra.FiniteEtale.TorsorCocycle.basedCocycle K Ω (realizedAlgebra K Ω C Lambda mark c) C
      (realizedCoaction K Ω C Lambda mark hadd hgal c) Lambda mark hadd hgal
      (realized_transporter_bijective K Ω C Lambda mark hadd hgal c)
      (realizedPoint K Ω C Lambda mark c) = c := by
  let := realizedAlgebra_finite K Ω C Lambda mark c
  apply _root_.GroupCohomology.ContinuousH1.Cocycle.ext
  intro σ
  apply mark.injective
  apply Algebra.FiniteEtale.TorsorCocycle.translate_injective K Ω (realizedAlgebra K Ω C Lambda mark
    c) C
    (realizedCoaction K Ω C Lambda mark hadd hgal c)
    (realized_transporter_bijective K Ω C Lambda mark hadd hgal c)
    (realizedPoint K Ω C Lambda mark c)
  exact (Algebra.FiniteEtale.TorsorCocycle.basedCocycle_action K Ω (realizedAlgebra K Ω C Lambda
    mark c) C
    (realizedCoaction K Ω C Lambda mark hadd hgal c) Lambda mark hadd hgal
    (realized_transporter_bijective K Ω C Lambda mark hadd hgal c)
    (realizedPoint K Ω C Lambda mark c) σ).trans
      (realized_translate_galois K Ω C Lambda mark hadd hgal c σ).symm

/-- Source K2-018#prop:k2018-arithmetic-characters, revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982: every native continuous class is
realized by an ACTUAL nontrivial finite-etale K-algebra, a derived algebraic
coaction with bijective transporter, and an actual Ω-point. The equality is
proved in the ORIGINAL positive-transporter H1 quotient. -/
theorem exists_algebraic_field_torsor (ξ : H1 (Ω ≃ₐ[K] Ω) Lambda) :
    ∃ (A : CommAlgCat.{u} K) (hfinite : Module.Finite K A) (_ : Algebra.Etale K A),
      letI := hfinite
      ∃ (α : AlgebraCoaction K A C (Bialgebra.counitAlgHom K C) (Bialgebra.comulAlgHom K C))
        (hT : Function.Bijective (transporter K A C α.coact)) (f : A →ₐ[K] Ω),
        Nontrivial A ∧
        classOf (Ω ≃ₐ[K] Ω) Lambda
          (Algebra.FiniteEtale.TorsorCocycle.basedCocycle K Ω A C α Lambda mark hadd hgal
            hT f) = ξ := by
  obtain ⟨c, rfl⟩ := classOf_surjective (Ω ≃ₐ[K] Ω) Lambda ξ
  refine ⟨realizedAlgebra K Ω C Lambda mark c,
    realizedAlgebra_finite K Ω C Lambda mark c, realizedAlgebra_etale K Ω C Lambda mark c,
    realizedCoaction K Ω C Lambda mark hadd hgal c,
    realized_transporter_bijective K Ω C Lambda mark hadd hgal c,
    realizedPoint K Ω C Lambda mark c, realizedAlgebra_nontrivial K Ω C Lambda mark c, ?_⟩
  rw [realized_basedCocycle_eq]

end AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor.FieldRealization
