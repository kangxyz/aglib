/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Integral closures of finite etale fraction-field algebras

For a normal Noetherian domain with specified fraction field, the literal integral closure in
an etale fraction-field algebra is finite. For a DVR it is free and flat. Localization and
the tensor generic-fibre equivalence require only integrality over the fraction field; the
equivalence sends `k ⊗ b` to `k * b`. A finite product decomposition induces the coordinatewise
integral-closure equivalence under the stated component-finiteness hypotheses.

## Extraction basis

Transferred existing declarations from
`R5Lab/AlgebraicGeometry/FiniteEtale/Normalization/FiniteModel.lean` at revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`, source SHA-256
`60dd994f14b6f00acbaf105021a663a100e5addd20e031efc0d8ccbffff991c1`, lines 24–91.
The Model abbreviation at line 20 is replaced by integralClosure.
Transferred existing declarations from
`R5Lab/AlgebraicGeometry/FiniteEtale/Normalization/EtaleAlgebra.lean` at revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`, source SHA-256
`e99fffbbabe662d55b43913ceb638bede808a016c2424b0e7c3beb06169ac7b4`, lines 12–41 only.
The stated hypotheses and chosen maps are retained; declarations use native mathematical
namespaces and canonical carriers. Source correspondence is separate from native Lean validation.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped nonZeroDivisors TensorProduct

namespace integralClosure

/-- The actual normalization commutes with a finite product decomposition,
provided its component normalizations are finite. -/
def equivPi
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type*} [Finite ι] (L : ι → Type*)
    [∀ i, CommRing (L i)] [∀ i, Algebra R (L i)]
    [∀ i, Module.Finite R (integralClosure R (L i))]
    (e : A ≃ₐ[R] ∀ i, L i) :
    integralClosure R A ≃ₐ[R] ∀ i, integralClosure R (L i) := by
  classical
  letI := Fintype.ofFinite ι
  let f : integralClosure R A →ₐ[R] (∀ i, integralClosure R (L i)) :=
    AlgHom.pi fun i => ((Pi.evalAlgHom R L i).comp e.toAlgHom).mapIntegralClosure
  apply AlgEquiv.ofBijective f
  constructor
  · intro x y h
    apply Subtype.ext
    apply e.injective
    funext i
    exact congrArg Subtype.val (congrFun h i)
  · intro b
    let g : (∀ i, integralClosure R (L i)) →ₐ[R] ∀ i, L i :=
      AlgHom.pi fun i => ((integralClosure R (L i)).val).comp
        (Pi.evalAlgHom R (fun i => integralClosure R (L i)) i)
    have hb : IsIntegral R (e.symm (g b)) :=
      ((Algebra.IsIntegral.isIntegral (R := R) b).map g).map e.symm.toAlgHom
    refine ⟨⟨e.symm (g b), hb⟩, ?_⟩
    funext i
    apply Subtype.ext
    change (e (e.symm (g b))) i = (b i : L i)
    rw [e.apply_symm_apply]
    rfl

variable (R K A : Type*) [CommRing R] [hR : IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]

/-- Normalization of a finite etale algebra is finite over every normal
Noetherian domain. Separability is used in the field factors. -/
theorem finite_of_etale [IsIntegrallyClosed R] [IsNoetherianRing R] [Algebra.Etale K A] :
    Module.Finite R (integralClosure R A) := by
  obtain ⟨ι, hι, L, hL, hKL, e, hfin⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  letI := hι
  letI := hL
  letI := hKL
  letI (i : ι) : Algebra R (L i) := (algebraMap K (L i)).comp (algebraMap R K) |>.toAlgebra
  haveI (i : ι) : IsScalarTower R K (L i) := IsScalarTower.of_algebraMap_eq' rfl
  haveI (i : ι) : Module.Finite K (L i) := (hfin i).1
  haveI (i : ι) : Algebra.IsSeparable K (L i) := (hfin i).2
  haveI (i : ι) : Module.Finite R (integralClosure R (L i)) :=
    IsIntegralClosure.finite R K (L i) _
  let f : integralClosure R A →ₐ[R] (∀ i, integralClosure R (L i)) :=
    AlgHom.pi fun i =>
      (((Pi.evalAlgHom K L i).comp e.toAlgHom).restrictScalars R).mapIntegralClosure
  apply Module.Finite.of_injective f.toLinearMap
  intro x y h
  apply Subtype.ext
  apply e.injective
  funext i
  exact congrArg Subtype.val (congrFun h i)

/-- Localizing the actual normalization at the nonzero base elements recovers
the same generic algebra. This needs only integrality over the fraction field. -/
theorem isLocalization [Algebra.IsIntegral K A] :
    let _ : IsDomain R := hR
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R A) R⁰) A := by
  refine ⟨?_, fun z => ?_, fun {x y} h => ⟨1, ?_⟩⟩
  · rintro ⟨_, x, hx, rfl⟩
    change IsUnit (algebraMap (integralClosure R A) A (algebraMap R (integralClosure R A) x))
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R K A]
    exact (IsLocalization.map_units K ⟨x, hx⟩).map (algebraMap K A)
  · obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization R⁰ z
      (Algebra.IsIntegral.isIntegral (R := K) z)
    refine ⟨⟨⟨m • z, hm⟩, algebraMap R (integralClosure R A) m, m, m.property, rfl⟩, ?_⟩
    change z * algebraMap R A m = m • z
    simp only [Submonoid.smul_def, Algebra.smul_def, mul_comm]
  · simpa only [Submonoid.coe_one, one_mul] using (Subtype.ext h : x = y)

/-- The literal generic-fibre isomorphism, sending `k ⊗ b` to `k * b`. -/
def genericFiberEquiv [Algebra.IsIntegral K A] : K ⊗[R] integralClosure R A ≃ₐ[K] A := by
  letI := isLocalization R K A
  haveI : Algebra.IsPushout R (integralClosure R A) K A :=
    Algebra.isPushout_of_isLocalization R⁰ K (integralClosure R A) A
  haveI : Algebra.IsPushout R K (integralClosure R A) A := Algebra.IsPushout.symm inferInstance
  exact Algebra.IsPushout.equiv R K (integralClosure R A) A

/-- The generic-fibre equivalence sends a pure tensor to the product of its images. -/
@[simp] theorem genericFiberEquiv_tmul [Algebra.IsIntegral K A]
    (k : K) (b : integralClosure R A) :
    genericFiberEquiv R K A (k ⊗ₜ[R] b) = algebraMap K A k * (b : A) := by
  letI := isLocalization R K A
  haveI : Algebra.IsPushout R (integralClosure R A) K A :=
    Algebra.isPushout_of_isLocalization R⁰ K (integralClosure R A) A
  haveI : Algebra.IsPushout R K (integralClosure R A) A := Algebra.IsPushout.symm inferInstance
  exact Algebra.IsPushout.equiv_tmul R K (integralClosure R A) A k b

/-- Over a DVR the same finite normalization is free, hence flat. -/
theorem free_of_etale [IsDiscreteValuationRing R] [Algebra.Etale K A] :
    Module.Free R (integralClosure R A) := by
  haveI := finite_of_etale R K A
  haveI : Module.IsTorsionFree R A := .trans_faithfulSMul R K A
  haveI : Module.IsTorsionFree R (integralClosure R A) :=
    Subtype.coe_injective.moduleIsTorsionFree ((integralClosure R A).val) (by simp)
  infer_instance

/-- The integral closure of an etale fraction-field algebra over a DVR is flat. -/
theorem flat_of_etale [IsDiscreteValuationRing R] [Algebra.Etale K A] :
    Module.Flat R (integralClosure R A) := by
  haveI := free_of_etale R K A
  infer_instance

end integralClosure
