/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Normalization.InertiaTorsor.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ContinuousTorsors
public import Mathlib.FieldTheory.KrullTopology

/-!
# Galois action at the original ambient field over a ring

The forward map is literal precomposition by Spec of each K-automorphism of Ω.
The coefficient action is derived from evaluation on the actual Hopf group.
For the existing normalization cover and action, restriction recovers the
same original positive torsor cocycle and class. All DVR, field, Hopf,
coordinate and inertia conditions remain explicit.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.MonObj CategoryTheory.PreGaloisCategory FintypeCatDiscrete
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber fiberToFinite)
open _root_.AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open _root_.CategoryTheory
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
open _root_.GroupCohomology.ContinuousH1
namespace AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor

open Algebra.FiniteEtale.GenericMaps Algebra.FiniteEtale.TorsorExtension

universe u
attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

section AffinePoints
variable (R B D : Type u) [CommRing R] [CommRing B] [Algebra R B]
  [CommRing D] [Algebra R D]

/-- The contravariant spectrum morphism of this algebra map, over the same base. -/
def algebraPoint (f : B →ₐ[R] D) : affine R D ⟶ affine R B :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact f.commutes r)

/-- Actual affine scheme points and ordinary algebra maps, by full faithfulness of Spec. -/
def affinePointEquiv : (affine R D ⟶ affine R B) ≃ (B →ₐ[R] D) where
  toFun p := Spec.homEquivAlgHom ⟨p.left, Over.w p⟩
  invFun := algebraPoint R B D
  left_inv p := by
    apply Over.OverMorphism.ext
    exact Spec.map_preimage p.left
  right_inv f := by
    apply AlgHom.ext
    intro b
    change (Spec.preimage (Spec.map (CommRingCat.ofHom f.toRingHom))).hom b = f b
    rw [Spec.preimage_map]
    rfl

variable (H : Type u) [CommRing H] [Algebra R H]

/-- Scheme action on affine points is evaluation of the original algebraic coaction. -/
theorem action_algebraPoint (alpha : B →ₐ[R] B ⊗[R] H)
    (a : H →ₐ[R] D) (x : B →ₐ[R] D) :
    action R B H alpha (algebraPoint R H D a) (algebraPoint R B D x) =
      algebraPoint R B D (evaluateCoaction R B H alpha a x) := by
  let z := Algebra.TensorProduct.lift x a (fun _ _ => .all _ _)
  have hz :
      pullback.lift (f := Spec.algebraMap R B) (g := Spec.algebraMap R H)
        (Spec.map (CommRingCat.ofHom x.toRingHom)) (Spec.map (CommRingCat.ofHom a.toRingHom))
        ((Over.w (algebraPoint R B D x)).trans (Over.w (algebraPoint R H D a)).symm) ≫
          (pullbackSpecIso R B H).hom = Spec.map (CommRingCat.ofHom z.toRingHom) := by
    apply (cancel_mono (pullbackSpecIso R B H).inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackSpecIso_inv_fst, pullback.lift_fst, ← Spec.map_comp]
      congr 1
      ext b
      simp [z]
    · rw [Category.assoc, pullbackSpecIso_inv_snd, pullback.lift_snd, ← Spec.map_comp]
      congr 1
      ext h
      simp [z]
  apply Over.OverMorphism.ext
  change _ ≫ ((pullbackSpecIso R B H).hom ≫ Spec.map (CommRingCat.ofHom alpha.toRingHom)) = _
  dsimp only [algebraPoint, Over.homMk_left]
  rw [← Category.assoc, hz, ← Spec.map_comp]
  rfl

end AffinePoints

section TensorPoints
variable (R K Ω B : Type u) [CommRing R] [CommRing K] [Algebra R K]
  [CommRing Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [CommRing B] [Algebra R B]

/-- Restriction along the actual second tensor inclusion. -/
def tensorPointEquiv : ((K ⊗[R] B) →ₐ[K] Ω) ≃ (B →ₐ[R] Ω) where
  toFun f := (f.restrictScalars R).comp Algebra.TensorProduct.includeRight
  invFun f := Algebra.TensorProduct.lift (Algebra.ofId K Ω) f (fun _ _ => .all _ _)
  left_inv f := by
    apply Algebra.TensorProduct.ext'
    intro k b
    change algebraMap K Ω k * f (1 ⊗ₜ[R] b) = f (k ⊗ₜ[R] b)
    have hh := (f.toLinearMap.map_smul k ((1 : K) ⊗ₜ[R] b)).symm
    rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one] at hh
    simpa only [AlgHom.toLinearMap_apply, Algebra.smul_def] using hh
  right_inv f := by ext b; simp

end TensorPoints

section NormalizationComparison
open integralClosure
variable (R K Ω A H : Type u)
  [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Algebra.IsIntegral K A] [CommRing H] [Algebra R H]

/-- The point of the literal normalization obtained from an ORIGINAL A-point. -/
def modelPointMap (f : A →ₐ[K] Ω) : integralClosure R A →ₐ[R] Ω :=
  (f.restrictScalars R).comp (integralClosure R A).val

/-- The same point as an actual scheme map over Spec(R). -/
def modelPoint (f : A →ₐ[K] Ω) : affine R Ω ⟶ affine R (integralClosure R A) :=
  algebraPoint R (integralClosure R A) Ω (modelPointMap R K Ω A f)

omit [IsDomain R] [IsIntegrallyClosed R] [IsFractionRing R K] [Algebra.IsIntegral K A] in
/-- The ORIGINAL Spec(A)-point maps to the normalization along the canonical inclusion. -/
theorem modelPoint_original (f : A →ₐ[K] Ω) :
    (modelPoint R K Ω A f).left =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (integralClosure R A).val.toRingHom) := by
  rw [← Spec.map_comp]
  rfl

/-- Every generic Ω-valued normalization point comes from the original A,
using its fixed canonical generic-fibre equivalence. -/
def modelPointEquiv : (A →ₐ[K] Ω) ≃ (affine R Ω ⟶ affine R (integralClosure R A)) :=
  ((AlgEquiv.arrowCongr (genericFiberEquiv R K A).symm (AlgEquiv.refl : Ω ≃ₐ[K] Ω)).trans
    (tensorPointEquiv R K Ω (integralClosure R A))).trans (affinePointEquiv R (integralClosure R A)
      Ω).symm

omit [IsIntegrallyClosed R] in
@[simp] theorem modelPointEquiv_apply (f : A →ₐ[K] Ω) :
    modelPointEquiv R K Ω A f = modelPoint R K Ω A f := by
  apply (affinePointEquiv R (integralClosure R A) Ω).injective
  simp only [modelPointEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  change tensorPointEquiv R K Ω (integralClosure R A)
      ((AlgEquiv.arrowCongr (genericFiberEquiv R K A).symm (AlgEquiv.refl : Ω ≃ₐ[K] Ω)) f) =
    (affinePointEquiv R (integralClosure R A) Ω) (algebraPoint R (integralClosure R A) Ω
      (modelPointMap R K Ω A f))
  rw [show algebraPoint R (integralClosure R A) Ω = (affinePointEquiv R (integralClosure R A)
    Ω).symm from rfl,
    Equiv.apply_symm_apply]
  ext b
  simp [tensorPointEquiv, AlgEquiv.arrowCongr, modelPointMap, genericFiberEquiv_tmul]

omit [IsDomain R] [IsIntegrallyClosed R] [IsFractionRing R K] [Algebra.IsIntegral K A] in
/-- Galois acts on this Ω-valued scheme point by its actual Spec automorphism. -/
theorem modelPoint_galois (sigma : Ω ≃ₐ[K] Ω) (f : A →ₐ[K] Ω) :
    modelPoint R K Ω A (sigma.toAlgHom.comp f) =
      algebraPoint R Ω Ω (sigma.toAlgHom.restrictScalars R) ≫ modelPoint R K Ω A f := by
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

variable {epsilon : H →ₐ[R] R} {delta : H →ₐ[R] H ⊗[R] H}
variable (tau : OriginalTorsorData R K A H epsilon delta)
  (T : AlgebraicTorsorData R (integralClosure R A) H epsilon delta)
  (hsquare : (actualTensorEquiv R K A H).toAlgHom.comp (Algebra.TensorProduct.BaseChange.map R K
    T.coaction.coact) =
    tau.coaction.coact.comp (genericFiberEquiv R K A).toAlgHom)

include hsquare in
omit [IsIntegrallyClosed R] in
/-- The canonical generic square identifies the actual model action on geometric
points with the action of the ORIGINAL A, in the same coefficient coordinates. -/
theorem modelPoint_action (h : (K ⊗[R] H) →ₐ[K] Ω) (f : A →ₐ[K] Ω) :
    action R (integralClosure R A) H T.coaction.coact
        (algebraPoint R H Ω (tensorPointEquiv R K Ω H h)) (modelPoint R K Ω A f) =
      modelPoint R K Ω A (Algebra.FiniteEtale.TorsorCocycle.translate K Ω A (K ⊗[R] H) tau.coaction
        h f) := by
  rw [modelPoint, action_algebraPoint]
  apply congrArg (algebraPoint R (integralClosure R A) Ω)
  let ev := Algebra.TensorProduct.lift f h (fun _ _ => .all _ _)
  have heval (z : integralClosure R A ⊗[R] H) :
      ev (actualTensorEquiv R K A H ((1 : K) ⊗ₜ[R] z)) =
        Algebra.TensorProduct.lift (modelPointMap R K Ω A f)
          (tensorPointEquiv R K Ω H h) (fun _ _ => .all _ _) z := by
    induction z using TensorProduct.inductionOn with
    | tmul b c =>
      simp [actualTensorEquiv, Algebra.TensorProduct.BaseChange.tensorEquiv_symm_tmul,
        genericFiberEquiv_tmul,
        ev, modelPointMap, tensorPointEquiv]
    | add z w hz hw => simp only [TensorProduct.tmul_add, map_add, hz, hw]
  ext b
  have hh := congrArg ev (DFunLike.congr_fun hsquare ((1 : K) ⊗ₜ[R] b))
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.BaseChange.map,
    Algebra.TensorProduct.map_tmul,
    AlgEquiv.coe_toAlgHom, genericFiberEquiv_tmul, map_one,
    _root_.one_mul] at hh
  rw [heval] at hh
  exact hh

end NormalizationComparison

section ActualH1

open integralClosure Algebra.FiniteEtale.TorsorCoordinates
open _root_.GroupCohomology.ContinuousH1
universe v
variable (R K Ω A H : Type u) (Lambda : Type v)
  [CommRing R] [hDomain : IsDomain R] [hDvr : IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [hFraction : IsFractionRing R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [hGalois : IsGalois K Ω] [hAlgClosed : IsAlgClosed Ω]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A] [Algebra.Etale K A]
  [CommRing H] [HopfAlgebra R H] [hCocomm : Coalgebra.IsCocomm R H]
  [hHopfFinite : Module.Finite R H] [hHopfEtale : Algebra.Etale R H]
  [AddCommGroup Lambda] [hLambdaTopology : TopologicalSpace Lambda] [hLambdaDiscrete :
    DiscreteTopology Lambda]
  [hLambdaTopologicalAdd : IsTopologicalAddGroup Lambda] [DistribMulAction (Ω ≃ₐ[K] Ω) Lambda]
  [hLambdaContinuous : ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]
local instance : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A
variable (tau : OriginalTorsorData R K A H (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H))
  (coords : CoefficientPointCoordinates R K Ω H Lambda (Bialgebra.counitAlgHom R H)
    (Bialgebra.comulAlgHom R H))
  (f : A →ₐ[K] Ω)
  (Q : Ideal (integralClosure R Ω)) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal R)]
  (hvan : inertiaClass R K Ω A H Lambda tau coords f Q = 0)

/-- These are the SAME coefficient coordinates, restricted through K tensor H
and turned into actual Spec(Ω)-points of the SAME Spec(H). -/
def coefficientSchemeCoordinates : Lambda ≃ (affine R Ω ⟶ (coefficientGroup R H).X) :=
  (coords.mark.trans (tensorPointEquiv R K Ω H)).trans (affinePointEquiv R H Ω).symm

omit hDomain hDvr hFraction hGalois hAlgClosed hCocomm hHopfFinite hHopfEtale
  hLambdaTopology hLambdaDiscrete hLambdaTopologicalAdd hLambdaContinuous in
/-- The coordinate map respects the actual Hopf multiplication on Spec(H). -/
theorem coefficientSchemeCoordinates_add
    [_hDomain : IsDomain R] [_hDvr : IsDiscreteValuationRing R]
    [_hFraction : IsFractionRing R K] [_hGalois : IsGalois K Ω] [_hAlgClosed : IsAlgClosed Ω]
    [_hCocomm : Coalgebra.IsCocomm R H] [_hHopfFinite : Module.Finite R H]
    [_hHopfEtale : Algebra.Etale R H]
    [_hLambdaTopology : TopologicalSpace Lambda] [_hLambdaDiscrete : DiscreteTopology Lambda]
    [_hLambdaTopologicalAdd : IsTopologicalAddGroup Lambda]
    [_hLambdaContinuous : ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]
    (a b : Lambda) :
    coefficientSchemeCoordinates R K Ω H Lambda coords (a + b) =
      coefficientSchemeCoordinates R K Ω H Lambda coords a *
        coefficientSchemeCoordinates R K Ω H Lambda coords b := by
  change algebraPoint R H Ω (tensorPointEquiv R K Ω H (coords.mark (a + b))) =
    action R H H (Bialgebra.comulAlgHom R H)
      (algebraPoint R H Ω (tensorPointEquiv R K Ω H (coords.mark b)))
      (algebraPoint R H Ω (tensorPointEquiv R K Ω H (coords.mark a)))
  rw [action_algebraPoint]
  apply congrArg (algebraPoint R H Ω)
  let ev := Algebra.TensorProduct.lift (coords.mark a) (coords.mark b) (fun _ _ => .all _ _)
  have ht (z : H ⊗[R] H) :
      ev ((Algebra.TensorProduct.BaseChange.tensorEquiv R K (B := H) (H := H)).symm ((1 : K) ⊗ₜ[R]
        z)) =
        Algebra.TensorProduct.lift
          (tensorPointEquiv R K Ω H (coords.mark a))
          (tensorPointEquiv R K Ω H (coords.mark b)) (fun _ _ => .all _ _) z := by
    induction z using TensorProduct.inductionOn with
    | tmul h k =>
      simp [Algebra.TensorProduct.BaseChange.tensorEquiv_symm_tmul, tensorPointEquiv, ev]
    | add z w hz hw => simp only [TensorProduct.tmul_add, map_add, hz, hw]
  ext h
  change coords.mark (a + b) ((1 : K) ⊗ₜ[R] h) = _
  rw [coords.mark_add]
  change ev ((Algebra.TensorProduct.BaseChange.tensorEquiv R K).symm
    (Algebra.TensorProduct.BaseChange.map R K (Bialgebra.comulAlgHom R H) ((1 : K) ⊗ₜ[R] h))) = _
  simp only [Algebra.TensorProduct.BaseChange.map, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  exact ht ((Bialgebra.comulAlgHom R H) h)

omit hDomain hDvr hFraction hGalois hAlgClosed hCocomm hHopfFinite hHopfEtale
  hLambdaTopology hLambdaDiscrete hLambdaTopologicalAdd hLambdaContinuous in
/-- The coefficient coordinates retain the given Galois action as the literal
Spec(Ω)-automorphism action on the same coefficient scheme. -/
theorem coefficientSchemeCoordinates_galois
    [_hDomain : IsDomain R] [_hDvr : IsDiscreteValuationRing R]
    [_hFraction : IsFractionRing R K] [_hGalois : IsGalois K Ω] [_hAlgClosed : IsAlgClosed Ω]
    [_hCocomm : Coalgebra.IsCocomm R H] [_hHopfFinite : Module.Finite R H]
    [_hHopfEtale : Algebra.Etale R H]
    [_hLambdaTopology : TopologicalSpace Lambda] [_hLambdaDiscrete : DiscreteTopology Lambda]
    [_hLambdaTopologicalAdd : IsTopologicalAddGroup Lambda]
    [_hLambdaContinuous : ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]
    (sigma : Ω ≃ₐ[K] Ω) (a : Lambda) :
    coefficientSchemeCoordinates R K Ω H Lambda coords (sigma • a) =
      algebraPoint R Ω Ω (sigma.toAlgHom.restrictScalars R) ≫
        coefficientSchemeCoordinates R K Ω H Lambda coords a := by
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext h
  exact (DFunLike.congr_fun (coords.mark_galois sigma a) ((1 : K) ⊗ₜ[R] h)).symm

/-- The existing additive coefficient coordinates give an actual multiplicative
mark of the scheme coefficient fibre, with its Hopf group law. -/
def coefficientSchemeMark :
    (affine R Ω ⟶ (coefficientGroup R H).X) ≃* Multiplicative Lambda :=
  MulEquiv.symm {
    toFun := fun a : Multiplicative Lambda => coefficientSchemeCoordinates R K Ω H Lambda coords
      a.toAdd
    invFun := fun a => Multiplicative.ofAdd ((coefficientSchemeCoordinates R K Ω H Lambda
      coords).symm a)
    left_inv := fun a => (coefficientSchemeCoordinates R K Ω H Lambda coords).symm_apply_apply
      a.toAdd
    right_inv := fun a => (coefficientSchemeCoordinates R K Ω H Lambda coords).apply_symm_apply a
    map_mul' := fun a b => coefficientSchemeCoordinates_add R K Ω H Lambda coords a.toAdd b.toAdd }

/-- Actual scheme transport from the selected original point to its Galois image. -/
def normalizationTransport (sigma : Ω ≃ₐ[K] Ω) : affine R Ω ⟶ (coefficientGroup R H).X :=
  Classical.choose ((normalizationSchemeAction R K Ω A H Lambda tau coords f Q hvan).transport
    (modelPoint R K Ω A f)
    (algebraPoint R Ω Ω (sigma.toAlgHom.restrictScalars R) ≫ modelPoint R K Ω A f)
    (toUnit_unique _ _))

/-- The literal positive scheme-transporter coordinate; no cocycle is an input. -/
def schemeCocycleValue (sigma : Ω ≃ₐ[K] Ω) : Lambda :=
  (coefficientSchemeCoordinates R K Ω H Lambda coords).symm
    (normalizationTransport R K Ω A H Lambda tau coords f Q hvan sigma)

omit hLambdaDiscrete in
/-- The original canonical square forces equality of the two actual
transport coordinates, before passing to any cohomology quotient. -/
theorem schemeCocycleValue_eq [_hLambdaDiscrete : DiscreteTopology Lambda]
    (sigma : Ω ≃ₐ[K] Ω) :
    schemeCocycleValue R K Ω A H Lambda tau coords f Q hvan sigma =
      (cocycle R K Ω A H Lambda tau coords f).val sigma := by
  let c := cocycle R K Ω A H Lambda tau coords f
  have hc : Algebra.FiniteEtale.TorsorCocycle.translate K Ω A (K ⊗[R] H) tau.coaction (coords.mark
    (c.val sigma)) f =
      sigma.toAlgHom.comp f :=
    Algebra.FiniteEtale.TorsorCocycle.basedCocycle_action K Ω A (K ⊗[R] H) tau.coaction Lambda
      coords.mark
      coords.mark_add coords.mark_galois tau.transporter_bijective f sigma
  have ha : (normalizationSchemeAction R K Ω A H Lambda tau coords f Q hvan).act
      (coefficientSchemeCoordinates R K Ω H Lambda coords (c.val sigma)) (modelPoint R K Ω A f) =
        algebraPoint R Ω Ω (sigma.toAlgHom.restrictScalars R) ≫ modelPoint R K Ω A f := by
    change action R (integralClosure R A) H
      (Algebra.FiniteEtale.InertiaTorsor.ofH1 R K Ω A H Lambda tau coords f Q hvan).coaction.coact
      (algebraPoint R H Ω (tensorPointEquiv R K Ω H (coords.mark (c.val sigma))))
      (modelPoint R K Ω A f) = _
    rw [modelPoint_action R K Ω A H tau _
      (Algebra.FiniteEtale.InertiaTorsor.ofH1_square R K Ω A H Lambda tau coords f Q hvan), hc,
      modelPoint_galois]
  have hu := (Classical.choose_spec
    ((normalizationSchemeAction R K Ω A H Lambda tau coords f Q hvan).transport
      (modelPoint R K Ω A f)
      (algebraPoint R Ω Ω (sigma.toAlgHom.restrictScalars R) ≫ modelPoint R K Ω A f)
      (toUnit_unique _ _))).2
  apply (coefficientSchemeCoordinates R K Ω H Lambda coords).injective
  change (coefficientSchemeCoordinates R K Ω H Lambda coords)
    ((coefficientSchemeCoordinates R K Ω H Lambda coords).symm
      (normalizationTransport R K Ω A H Lambda tau coords f Q hvan sigma)) = _
  rw [Equiv.apply_symm_apply]
  exact (hu _ ha).symm

/-- Continuity and the cocycle law for the actual scheme transport follow from
the proved coordinate equality with the original continuous cocycle. -/
def normalizationSchemeCocycle : Cocycle (Ω ≃ₐ[K] Ω) Lambda := by
  refine ⟨⟨schemeCocycleValue R K Ω A H Lambda tau coords f Q hvan, ?_⟩, ?_⟩
  · exact (cocycle R K Ω A H Lambda tau coords f).continuous.congr
      (fun sigma => (schemeCocycleValue_eq R K Ω A H Lambda tau coords f Q hvan sigma).symm)
  · intro sigma rho
    change schemeCocycleValue R K Ω A H Lambda tau coords f Q hvan (sigma * rho) =
      schemeCocycleValue R K Ω A H Lambda tau coords f Q hvan sigma +
        sigma • schemeCocycleValue R K Ω A H Lambda tau coords f Q hvan rho
    simpa only [schemeCocycleValue_eq] using
      (cocycle R K Ω A H Lambda tau coords f).map_mul sigma rho

/-- The constructed continuous representative is positive transport on the
actual pointed scheme torsor in its proved multiplicative coefficient mark. -/
theorem normalizationSchemeCocycle_action (sigma : Ω ≃ₐ[K] Ω) :
    (normalizationSchemeAction R K Ω A H Lambda tau coords f Q hvan).act
      ((coefficientSchemeMark R K Ω H Lambda coords).symm
        (Multiplicative.ofAdd ((normalizationSchemeCocycle R K Ω A H Lambda tau coords f Q hvan).val
          sigma)))
      (modelPoint R K Ω A f) =
        algebraPoint R Ω Ω (sigma.toAlgHom.restrictScalars R) ≫ modelPoint R K Ω A f := by
  change (normalizationSchemeAction R K Ω A H Lambda tau coords f Q hvan).act
    ((coefficientSchemeCoordinates R K Ω H Lambda coords)
      ((coefficientSchemeCoordinates R K Ω H Lambda coords).symm
        (normalizationTransport R K Ω A H Lambda tau coords f Q hvan sigma))) _ = _
  rw [Equiv.apply_symm_apply]
  exact (Classical.choose_spec
    ((normalizationSchemeAction R K Ω A H Lambda tau coords f Q hvan).transport
      (modelPoint R K Ω A f)
      (algebraPoint R Ω Ω (sigma.toAlgHom.restrictScalars R) ≫ modelPoint R K Ω A f)
      (toUnit_unique _ _))).1

/-- Equality holds for the actual continuous representatives, not only their classes. -/
theorem normalizationSchemeCocycle_eq :
    normalizationSchemeCocycle R K Ω A H Lambda tau coords f Q hvan =
      cocycle R K Ω A H Lambda tau coords f :=
  _root_.GroupCohomology.ContinuousH1.Cocycle.ext (schemeCocycleValue_eq R K Ω A H Lambda tau coords
    f Q hvan)

/-- The class is formed in the existing common continuous H1 quotient. -/
def normalizationSchemeClass : H1 (Ω ≃ₐ[K] Ω) Lambda :=
  classOf (Ω ≃ₐ[K] Ω) Lambda (normalizationSchemeCocycle R K Ω A H Lambda tau coords f Q hvan)

/-- The actual scheme transport class of the literal normalization recovers the
class of the ORIGINAL A-torsor. This is a generic-point comparison; it does not
assert full etale-sheaf/monodromy classification on Spec(R), or global gluing. -/
theorem normalizationSchemeClass_eq :
    normalizationSchemeClass R K Ω A H Lambda tau coords f Q hvan =
      genericClass R K Ω A H Lambda tau coords f := by
  unfold normalizationSchemeClass genericClass
  rw [normalizationSchemeCocycle_eq]

/-- Even if a different original point is used to construct the model, the
resulting scheme-transport class is the same common continuous H1 class. -/
theorem normalizationSchemeClass_independent (g : A →ₐ[K] Ω)
    (hvan_g : inertiaClass R K Ω A H Lambda tau coords g Q = 0) :
    normalizationSchemeClass R K Ω A H Lambda tau coords f Q hvan =
      normalizationSchemeClass R K Ω A H Lambda tau coords g Q hvan_g := by
  rw [normalizationSchemeClass_eq, normalizationSchemeClass_eq]
  exact genericClass_independent R K Ω A H Lambda tau coords f g


end ActualH1

section NativeFibreCoordinates
open integralClosure Algebra.FiniteEtale.TorsorCoordinates
variable (R K Ω A H Lambda : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A] [Algebra.Etale K A]
  [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
  [Module.Finite R H] [Algebra.Etale R H]
  [AddCommGroup Lambda] [TopologicalSpace Lambda] [DiscreteTopology Lambda]
  [IsTopologicalAddGroup Lambda] [DistribMulAction (Ω ≃ₐ[K] Ω) Lambda]
  [ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]
local instance : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A
variable (tau : OriginalTorsorData R K A H (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H))
  (coords : CoefficientPointCoordinates R K Ω H Lambda (Bialgebra.counitAlgHom R H)
    (Bialgebra.comulAlgHom R H))
  (f : A →ₐ[K] Ω)
  (Q : Ideal (integralClosure R Ω)) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal R)]
  (hvan : inertiaClass R K Ω A H Lambda tau coords f Q = 0)

/-- This is exactly the existing scheme-torsor fibre coordinate construction,
evaluated on the actual Galois-image point of the normalization cover. -/
theorem schemeCocycleValue_fibreBasis (sigma : Ω ≃ₐ[K] Ω) :
    schemeCocycleValue R K Ω A H Lambda tau coords f Q hvan sigma =
      _root_.AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions.fibreBasis
        (Spec.algebraMap R Ω) (coefficientGroup R H)
        (normalizationCover R K Ω A H Lambda tau coords f Q hvan)
        (normalizationSchemeAction R K Ω A H Lambda tau coords f Q hvan)
        (coefficientSchemeMark R K Ω H Lambda coords)
        (normalizationGenericPoint R K Ω A H Lambda tau coords f Q hvan)
        (algebraPoint R Ω Ω (sigma.toAlgHom.restrictScalars R) ≫
          normalizationGenericPoint R K Ω A H Lambda tau coords f Q hvan) := rfl

end NativeFibreCoordinates


end AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor

namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.OverRing
open AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor Algebra.FiniteEtale.TorsorExtension
universe u v
attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory
  _root_.AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent.coverCartesian

section GaloisMap
variable (R K Ω : Type u) [CommRing R] [Field K] [Algebra R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]

/-- The literal given Ω-valued point over the original affine base. -/
abbrev basePoint := Spec.algebraMap R Ω

/-- Its endomorphism is Spec of the original K-automorphism, restricted to R. -/
def pointEnd (sigma : Ω ≃ₐ[K] Ω) : Over.mk (basePoint R Ω) ⟶ Over.mk (basePoint R Ω) :=
  algebraPoint R Ω Ω (sigma.toAlgHom.restrictScalars R)

@[simp] theorem pointEnd_one : pointEnd R K Ω 1 = 𝟙 (Over.mk (basePoint R Ω)) := by
  apply Over.OverMorphism.ext
  change Spec.map (𝟙 _) = 𝟙 _
  exact Spec.map_id _

/-- The raw positive automorphism convention agrees with the native Aut product:
Spec reverses maps and point evaluation then precomposes. No inverse is inserted. -/
theorem pointEnd_mul (sigma rho : Ω ≃ₐ[K] Ω) :
    pointEnd R K Ω (sigma * rho) = pointEnd R K Ω sigma ≫ pointEnd R K Ω rho := by
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- Literal precomposition on every finite etale cover. -/
def act (sigma : Ω ≃ₐ[K] Ω) (Y : Scheme.FiniteEtale (Spec (.of R)))
    (p : Fiber (basePoint R Ω) Y) : Fiber (basePoint R Ω) Y := pointEnd R K Ω sigma ≫ p

@[simp] theorem act_one (Y : Scheme.FiniteEtale (Spec (.of R))) (p : Fiber (basePoint R Ω) Y) :
    act R K Ω 1 Y p = p := by simp [act]

@[simp] theorem act_mul (sigma rho : Ω ≃ₐ[K] Ω) (Y : Scheme.FiniteEtale (Spec (.of R)))
    (p : Fiber (basePoint R Ω) Y) :
    act R K Ω (sigma * rho) Y p = act R K Ω sigma Y (act R K Ω rho Y p) := by
  simp only [act, pointEnd_mul, Category.assoc]

/-- The permutation of the actual finite fibre induced by the given field automorphism. -/
def fibreEquiv (sigma : Ω ≃ₐ[K] Ω) (Y : Scheme.FiniteEtale (Spec (.of R))) :
    Fiber (basePoint R Ω) Y ≃ Fiber (basePoint R Ω) Y where
  toFun := act R K Ω sigma Y
  invFun := act R K Ω sigma⁻¹ Y
  left_inv p := by rw [← act_mul, inv_mul_cancel, act_one]
  right_inv p := by rw [← act_mul, mul_inv_cancel, act_one]

/-- Natural automorphism of the finite fibre functor obtained by Spec precomposition. -/
def fibreAut (sigma : Ω ≃ₐ[K] Ω) : FiberAutGroup (basePoint R Ω) :=
  NatIso.ofComponents (fun Y => FintypeCat.equivEquivIso (fibreEquiv R K Ω sigma Y)) (by
    intro Y Z q
    apply FintypeCat.hom_ext
    intro p
    change pointEnd R K Ω sigma ≫ (p ≫ q.hom) = (pointEnd R K Ω sigma ≫ p) ≫ q.hom
    exact (Category.assoc _ _ _).symm)

/-- The canonical map is constructed on every cover and every cover morphism. -/
def toFibreAut : (Ω ≃ₐ[K] Ω) →* FiberAutGroup (basePoint R Ω) where
  toFun := fibreAut R K Ω
  map_one' := by
    apply Aut.ext
    apply NatTrans.ext
    funext Y
    apply FintypeCat.hom_ext
    intro p
    exact act_one R K Ω Y p
  map_mul' sigma rho := by
    apply Aut.ext
    apply NatTrans.ext
    funext Y
    apply FintypeCat.hom_ext
    intro p
    exact act_mul R K Ω sigma rho Y p

@[simp] theorem toFibreAut_apply (sigma : Ω ≃ₐ[K] Ω) (Y : Scheme.FiniteEtale (Spec (.of R)))
    (p : Fiber (basePoint R Ω) Y) :
    (toFibreAut R K Ω sigma).hom.app Y p = pointEnd R K Ω sigma ≫ p := rfl

/-- Coordinates in the original Omega, with no replacement field. -/
def pointCoordinates (Y : Scheme.FiniteEtale (Spec (.of R))) (p : Fiber (basePoint R Ω) Y) :
    Γ(Y.obj.left, ⊤) →+* Ω :=
  (p.left.appTop ≫ (Scheme.ΓSpecIso (.of Ω)).hom).hom

theorem pointCoordinates_injective (Y : Scheme.FiniteEtale (Spec (.of R))) :
    Function.Injective (pointCoordinates R Ω Y) := by
  let : IsAffine Y.obj.left := isAffine_of_isAffineHom Y.obj.hom
  intro p q h
  apply Over.OverMorphism.ext
  apply ext_of_isAffine
  apply (cancel_mono (Scheme.ΓSpecIso (.of Ω)).hom).mp
  exact CommRingCat.hom_ext h

theorem pointCoordinates_act (sigma : Ω ≃ₐ[K] Ω) (Y : Scheme.FiniteEtale (Spec (.of R)))
    (p : Fiber (basePoint R Ω) Y) :
    pointCoordinates R Ω Y (act R K Ω sigma Y p) =
      sigma.toRingHom.comp (pointCoordinates R Ω Y p) := by
  change ((Spec.map _ ≫ p.left).appTop ≫ _).hom = _
  rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
  rfl

variable [Algebra.IsIntegral K Ω]

/-- Krull-open element stabilizers give continuity of every finite fibre orbit. -/
theorem continuous_act (Y : Scheme.FiniteEtale (Spec (.of R))) (p : Fiber (basePoint R Ω) Y) :
    Continuous (fun sigma : Ω ≃ₐ[K] Ω => (toFibreAut R K Ω sigma).hom.app Y p) := by
  let : TopologicalSpace Ω := ⊥
  let : DiscreteTopology Ω := ⟨rfl⟩
  let : ContinuousSMul (Ω ≃ₐ[K] Ω) Ω :=
    continuousSMul_iff_stabilizer_isOpen.mpr (fun x => stabilizer_isOpen_of_isIntegral x)
  let c : (fiberToFinite (basePoint R Ω)).obj Y → (Γ(Y.obj.left, ⊤) → Ω) :=
    fun p => pointCoordinates R Ω Y p
  have hc : Function.Injective c := by
    intro p q h
    exact pointCoordinates_injective R Ω Y (RingHom.ext (congrFun h))
  have he := (continuous_of_discreteTopology (f := c)).isClosedEmbedding hc
  rw [he.isEmbedding.isInducing.continuous_iff]
  apply continuous_pi
  intro a
  change Continuous (fun sigma : Ω ≃ₐ[K] Ω => pointCoordinates R Ω Y (act R K Ω sigma Y p) a)
  simp_rw [pointCoordinates_act]
  exact continuous_id.smul continuous_const

/-- Continuity for the native topology induced by all finite fibre evaluations. -/
theorem continuous_toFibreAut : Continuous (toFibreAut R K Ω) := by
  rw [Topology.IsInducing.continuous_iff
    (PreGaloisCategory.autEmbedding_isClosedEmbedding (fiberToFinite (basePoint R Ω))).isInducing,
    continuous_pi_iff]
  intro Y
  let c : Aut ((fiberToFinite (basePoint R Ω)).obj Y) →
      ((fiberToFinite (basePoint R Ω)).obj Y → (fiberToFinite (basePoint R Ω)).obj Y) := fun a =>
        a.hom
  have hc : Function.Injective c := by
    intro a b h
    apply Aut.ext
    apply FintypeCat.hom_ext
    exact congrFun h
  have he := (continuous_of_discreteTopology (f := c)).isClosedEmbedding hc
  rw [he.isEmbedding.isInducing.continuous_iff]
  exact continuous_pi (fun p => continuous_act R K Ω Y p)

/-- Canonical continuous Galois-to-fibre-automorphism homomorphism. -/
def galoisToFibre : (Ω ≃ₐ[K] Ω) →ₜ* FiberAutGroup (basePoint R Ω) :=
  { toFibreAut R K Ω with continuous_toFun := continuous_toFibreAut R K Ω }

@[simp] theorem galoisToFibre_apply (sigma : Ω ≃ₐ[K] Ω) (Y : Scheme.FiniteEtale (Spec (.of R)))
    (p : Fiber (basePoint R Ω) Y) :
    (galoisToFibre R K Ω sigma).hom.app Y p = pointEnd R K Ω sigma ≫ p := rfl

end GaloisMap
section CoefficientAction
variable {X : Scheme.{u}} {L : Type u} [Field L]
  (s : Spec (.of L) ⟶ X)
  (H : Grp (Over X)) [IsFinite H.X.hom] [Etale H.X.hom]
  (Lambda : Type v) [AddCommGroup Lambda]
  (mark : (Over.mk s ⟶ H.X) ≃* Multiplicative Lambda)

/-- Natural evaluation with its actual scheme-point type exposed. -/
def coefficientEval (gamma : FiberAutGroup s) (a : Over.mk s ⟶ H.X) : Over.mk s ⟶ H.X :=
  gamma.hom.app (coefficientCover H) a

/-- Naturality on the coefficient product makes every fibre automorphism
multiplicative on the actual coefficient points. -/
theorem coefficient_eval_mul (gamma : FiberAutGroup s) (a b : Over.mk s ⟶ H.X) :
    coefficientEval s H gamma (a * b) =
      coefficientEval s H gamma a * coefficientEval s H gamma b := by
  change gamma.hom.app (coefficientCover H) (lift a b ≫ μ[H.X]) =
    lift (gamma.hom.app (coefficientCover H) a) (gamma.hom.app (coefficientCover H) b) ≫ μ[H.X]
  rw [_root_.AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions.evaluation_naturality
    s gamma (Z := coefficientCover H ⊗ coefficientCover H)
    (W := coefficientCover H) μ[H.X],
    _root_.AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions.evaluation_product
      s H (coefficientCover H)]

/-- The actual coefficient-fibre group automorphism, not an input representation. -/
def coefficientFibreMulEquiv (gamma : FiberAutGroup s) :
    (Over.mk s ⟶ H.X) ≃* (Over.mk s ⟶ H.X) where
  toEquiv := FintypeCat.equivEquivIso.symm (gamma.app (coefficientCover H))
  map_mul' := coefficient_eval_mul s H gamma

/-- The full fibre-automorphism group acts additively through the given genuine
coefficient marking. The action is constructed from natural fibre evaluation. -/
@[instance_reducible] def coefficientFullAction : DistribMulAction (FiberAutGroup s) Lambda where
  smul gamma a := (mark (gamma.hom.app (coefficientCover H) (mark.symm (Multiplicative.ofAdd
    a)))).toAdd
  one_smul a := by
    change (mark (mark.symm (Multiplicative.ofAdd a))).toAdd = a
    rw [mark.apply_symm_apply]
    rfl
  mul_smul gamma delta a := by
    change (mark ((gamma * delta).hom.app (coefficientCover H) (mark.symm (Multiplicative.ofAdd
      a)))).toAdd =
      (mark (gamma.hom.app (coefficientCover H)
        (mark.symm (mark (delta.hom.app (coefficientCover H) (mark.symm (Multiplicative.ofAdd
          a))))))).toAdd
    rw [mark.symm_apply_apply]
    rfl
  smul_zero gamma := by
    change (mark (coefficientFibreMulEquiv s H gamma (mark.symm 1))).toAdd = 0
    rw [map_one, map_one, map_one]
    rfl
  smul_add gamma a b := by
    change (mark (coefficientFibreMulEquiv s H gamma
      (mark.symm (Multiplicative.ofAdd a * Multiplicative.ofAdd b)))).toAdd = _
    rw [map_mul, map_mul, map_mul]
    rfl

/-- Full coefficient equivariance is derived with this constructed action. -/
theorem coefficientFullAction_mark (gamma : FiberAutGroup s) (a : Over.mk s ⟶ H.X) :
    letI := coefficientFullAction s H Lambda mark
    mark (gamma.hom.app (coefficientCover H) a) =
      Multiplicative.ofAdd (gamma • (mark a).toAdd) := by
  let := coefficientFullAction s H Lambda mark
  change mark (gamma.hom.app (coefficientCover H) a) =
    mark (gamma.hom.app (coefficientCover H) (mark.symm (mark a)))
  rw [mark.symm_apply_apply]

variable [TopologicalSpace Lambda] [DiscreteTopology Lambda]

/-- Joint continuity follows from the one finite coefficient-fibre coordinate
in the native topology on the full automorphism group. -/
theorem coefficientFullAction_continuous :
    letI := coefficientFullAction s H Lambda mark
    ContinuousSMul (FiberAutGroup s) Lambda := by
  let := coefficientFullAction s H Lambda mark
  constructor
  have hcoord : Continuous (fun gamma : FiberAutGroup s =>
      PreGaloisCategory.autEmbedding (fiberToFinite s) gamma (coefficientCover H)) :=
    (continuous_apply (coefficientCover H)).comp continuous_induced_dom
  let ev : Aut ((fiberToFinite s).obj (coefficientCover H)) × Lambda → Lambda := fun z =>
    (mark (z.1.hom (mark.symm (Multiplicative.ofAdd z.2)))).toAdd
  change Continuous (fun z : FiberAutGroup s × Lambda =>
    ev (PreGaloisCategory.autEmbedding (fiberToFinite s) z.1 (coefficientCover H), z.2))
  exact (continuous_of_discreteTopology (f := ev)).comp
    ((hcoord.comp continuous_fst).prodMk continuous_snd)

end CoefficientAction

section NormalizationClass
open integralClosure Algebra.FiniteEtale.TorsorCoordinates
open _root_.AlgebraicGeometry.Scheme.EtaleCohomology
variable (R K Ω A H Lambda : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A] [Algebra.Etale K A]
  [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
  [Module.Finite R H] [Algebra.Etale R H]
  [AddCommGroup Lambda] [TopologicalSpace Lambda] [DiscreteTopology Lambda]
  [IsTopologicalAddGroup Lambda] [DistribMulAction (Ω ≃ₐ[K] Ω) Lambda]
  [ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]
local instance : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A
variable (tau : OriginalTorsorData R K A H (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H))
  (coords : CoefficientPointCoordinates R K Ω H Lambda
    (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H))
  (f : A →ₐ[K] Ω)
  (Q : Ideal (integralClosure R Ω)) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal R)]
  (hvan : inertiaClass R K Ω A H Lambda tau coords f Q = 0)

/-- The full model fibre-group action is derived on the same Lambda through
the accepted actual coefficient-scheme marking. -/
abbrev modelCoefficientAction : DistribMulAction (FiberAutGroup (basePoint R Ω)) Lambda :=
  coefficientFullAction (basePoint R Ω) (coefficientGroup R H) Lambda
    (coefficientSchemeMark R K Ω H Lambda coords)

theorem modelCoefficientAction_continuous :
    letI := modelCoefficientAction R K Ω H Lambda coords
    ContinuousSMul (FiberAutGroup (basePoint R Ω)) Lambda :=
  coefficientFullAction_continuous (basePoint R Ω) (coefficientGroup R H) Lambda
    (coefficientSchemeMark R K Ω H Lambda coords)

/-- Restriction of the derived full fibre-group action is the ORIGINAL supplied
Galois action, proved from actual Spec precomposition and the old marking law. -/
theorem modelCoefficientAction_restrict (sigma : Ω ≃ₐ[K] Ω) (a : Lambda) :
    letI := modelCoefficientAction R K Ω H Lambda coords
    (galoisToFibre R K Ω sigma) • a = sigma • a := by
  let := modelCoefficientAction R K Ω H Lambda coords
  change (coefficientSchemeMark R K Ω H Lambda coords
    ((galoisToFibre R K Ω sigma).hom.app (coefficientCover (coefficientGroup R H))
      (coefficientSchemeCoordinates R K Ω H Lambda coords a))).toAdd = sigma • a
  rw [galoisToFibre_apply]
  change (coefficientSchemeMark R K Ω H Lambda coords
    (algebraPoint R Ω Ω (sigma.toAlgHom.restrictScalars R) ≫
      coefficientSchemeCoordinates R K Ω H Lambda coords a)).toAdd = sigma • a
  rw [← coefficientSchemeCoordinates_galois]
  exact (coefficientSchemeCoordinates R K Ω H Lambda coords).symm_apply_apply (sigma • a)

/-- Equality of the restricted action structures, not merely an external
identification or a new equivariance hypothesis. -/
theorem modelCoefficientRestrictedAction_eq :
    letI := modelCoefficientAction R K Ω H Lambda coords
    restrictedAction Lambda (galoisToFibre R K Ω) =
      (inferInstance : DistribMulAction (Ω ≃ₐ[K] Ω) Lambda) := by
  let := modelCoefficientAction R K Ω H Lambda coords
  ext sigma a
  exact modelCoefficientAction_restrict R K Ω H Lambda coords sigma a

/-- Native continuous-H1 group restriction with the identity coefficient map.
Its equivariance is proved, so its target uses the original Galois action. -/
def coefficientRestriction :
    letI := modelCoefficientAction R K Ω H Lambda coords
    PullbackMap (A := Lambda) (B := Lambda) (galoisToFibre R K Ω) := by
  letI := modelCoefficientAction R K Ω H Lambda coords
  exact {
    toFun := id
    map_zero' := rfl
    map_add' _ _ := rfl
    continuous_toFun := continuous_id
    map_smul' := modelCoefficientAction_restrict R K Ω H Lambda coords }

@[simp] theorem coefficientRestriction_apply (a : Lambda) :
    letI := modelCoefficientAction R K Ω H Lambda coords
    (coefficientRestriction R K Ω H Lambda coords).toContinuousAddMonoidHom a = a := rfl

/-- The induced operation on representatives is literal group restriction. -/
theorem coefficientRestriction_cocycle_value :
    letI := modelCoefficientAction R K Ω H Lambda coords
    ∀ (c : Cocycle (FiberAutGroup (basePoint R Ω)) Lambda) (sigma : Ω ≃ₐ[K] Ω),
      ((coefficientRestriction R K Ω H Lambda coords).onCocycles c).val sigma =
        c.val (galoisToFibre R K Ω sigma) := by
  let := modelCoefficientAction R K Ω H Lambda coords
  intro c sigma
  rfl

/-- The existing native cocycle of the actual model scheme torsor, now over the
FULL fibre group with its DERIVED coefficient action and equivariance. -/
def fullSchemeCocycle :
    letI := modelCoefficientAction R K Ω H Lambda coords
    Cocycle (FiberAutGroup (basePoint R Ω)) Lambda := by
  letI := modelCoefficientAction R K Ω H Lambda coords
  letI := modelCoefficientAction_continuous R K Ω H Lambda coords
  exact _root_.AlgebraicGeometry.Scheme.EtaleCohomology.ContinuousTorsors.basedCocycle (basePoint
    R Ω)
    (coefficientGroup R H)
    (normalizationCover R K Ω A H Lambda tau coords f Q hvan)
    (normalizationSchemeAction R K Ω A H Lambda tau coords f Q hvan)
    (coefficientSchemeMark R K Ω H Lambda coords)
    (coefficientFullAction_mark (basePoint R Ω) (coefficientGroup R H) Lambda
      (coefficientSchemeMark R K Ω H Lambda coords))
    (normalizationGenericPoint R K Ω A H Lambda tau coords f Q hvan)

/-- Native cocycle restriction is exactly the accepted actual positive scheme
cocycle. Both the group map and the coefficient equivariance were constructed. -/
theorem fullSchemeCocycle_restriction :
    letI := modelCoefficientAction R K Ω H Lambda coords
    (coefficientRestriction R K Ω H Lambda coords).onCocycles
        (fullSchemeCocycle R K Ω A H Lambda tau coords f Q hvan) =
      normalizationSchemeCocycle R K Ω A H Lambda tau coords f Q hvan := by
  let := modelCoefficientAction R K Ω H Lambda coords
  let := modelCoefficientAction_continuous R K Ω H Lambda coords
  apply _root_.GroupCohomology.ContinuousH1.Cocycle.ext
  intro sigma
  rw [_root_.GroupCohomology.ContinuousH1.PullbackMap.onCocycles_apply]
  change (fullSchemeCocycle R K Ω A H Lambda tau coords f Q hvan).val
      (galoisToFibre R K Ω sigma) =
    (normalizationSchemeCocycle R K Ω A H Lambda tau coords f Q hvan).val sigma
  rw [fullSchemeCocycle,
    _root_.AlgebraicGeometry.Scheme.EtaleCohomology.ContinuousTorsors.basedCocycle_apply,
    galoisToFibre_apply]
  exact (schemeCocycleValue_fibreBasis R K Ω A H Lambda tau coords f Q hvan sigma).symm

/-- The existing native scheme torsor class of the actual finite etale model,
with no full-fibre-group action or marking-equivariance premise. -/
def fullSchemeClass :
    letI := modelCoefficientAction R K Ω H Lambda coords
    letI := modelCoefficientAction_continuous R K Ω H Lambda coords
    H1 (FiberAutGroup (basePoint R Ω)) Lambda := by
  letI := modelCoefficientAction R K Ω H Lambda coords
  letI := modelCoefficientAction_continuous R K Ω H Lambda coords
  letI : Nonempty (Fiber (basePoint R Ω)
      (normalizationCover R K Ω A H Lambda tau coords f Q hvan)) :=
    ⟨normalizationGenericPoint R K Ω A H Lambda tau coords f Q hvan⟩
  exact _root_.AlgebraicGeometry.Scheme.EtaleCohomology.ContinuousTorsors.schemeTorsorClass
    (basePoint R Ω)
    (coefficientGroup R H)
    (normalizationCover R K Ω A H Lambda tau coords f Q hvan)
    (normalizationSchemeAction R K Ω A H Lambda tau coords f Q hvan)
    (coefficientSchemeMark R K Ω H Lambda coords)
    (coefficientFullAction_mark (basePoint R Ω) (coefficientGroup R H) Lambda
      (coefficientSchemeMark R K Ω H Lambda coords))

theorem fullSchemeClass_eq_classOf :
    letI := modelCoefficientAction R K Ω H Lambda coords
    letI := modelCoefficientAction_continuous R K Ω H Lambda coords
    fullSchemeClass R K Ω A H Lambda tau coords f Q hvan =
      classOf (FiberAutGroup (basePoint R Ω)) Lambda
        (fullSchemeCocycle R K Ω A H Lambda tau coords f Q hvan) := by
  let := modelCoefficientAction R K Ω H Lambda coords
  let := modelCoefficientAction_continuous R K Ω H Lambda coords
  let : Nonempty (Fiber (basePoint R Ω)
      (normalizationCover R K Ω A H Lambda tau coords f Q hvan)) :=
    ⟨normalizationGenericPoint R K Ω A H Lambda tau coords f Q hvan⟩
  exact _root_.AlgebraicGeometry.Scheme.EtaleCohomology.ContinuousTorsors.schemeTorsorClass_eq
    (basePoint R
    Ω) (coefficientGroup R H)
    (normalizationCover R K Ω A H Lambda tau coords f Q hvan)
    (normalizationSchemeAction R K Ω A H Lambda tau coords f Q hvan)
    (coefficientSchemeMark R K Ω H Lambda coords)
    (coefficientFullAction_mark (basePoint R Ω) (coefficientGroup R H) Lambda
      (coefficientSchemeMark R K Ω H Lambda coords))
    (normalizationGenericPoint R K Ω A H Lambda tau coords f Q hvan)

/-- Restricting the ACTUAL native schemeTorsorClass gives the accepted
normalizationSchemeClass in the SAME original continuous Galois-H1 quotient. -/
theorem fullSchemeClass_restriction :
    letI := modelCoefficientAction R K Ω H Lambda coords
    letI := modelCoefficientAction_continuous R K Ω H Lambda coords
    (coefficientRestriction R K Ω H Lambda coords).onH1
        (fullSchemeClass R K Ω A H Lambda tau coords f Q hvan) =
      normalizationSchemeClass R K Ω A H Lambda tau coords f Q hvan := by
  let := modelCoefficientAction R K Ω H Lambda coords
  let := modelCoefficientAction_continuous R K Ω H Lambda coords
  rw [fullSchemeClass_eq_classOf, _root_.GroupCohomology.ContinuousH1.PullbackMap.onH1_classOf,
    fullSchemeCocycle_restriction]
  rfl

/-- Thus this actual full-fibre-group model class restricts to the class of the
ORIGINAL A-torsor, with the original coefficient algebra and positive convention. -/
theorem fullSchemeClass_restriction_generic :
    letI := modelCoefficientAction R K Ω H Lambda coords
    letI := modelCoefficientAction_continuous R K Ω H Lambda coords
    (coefficientRestriction R K Ω H Lambda coords).onH1
        (fullSchemeClass R K Ω A H Lambda tau coords f Q hvan) =
      genericClass R K Ω A H Lambda tau coords f := by
  let := modelCoefficientAction R K Ω H Lambda coords
  let := modelCoefficientAction_continuous R K Ω H Lambda coords
  rw [fullSchemeClass_restriction, normalizationSchemeClass_eq]

end NormalizationClass

end AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.OverRing
