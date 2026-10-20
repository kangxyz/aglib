/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.IntegralClosure.Actions
public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Aglib.RingTheory.TensorProduct.CoalgebraBaseChange

/-!
# Generic maps on actual finite etale models and nonsplit coactions

Source correspondence: the P8/P14 same-normalization action slice of
`K2-018#prop:k2018-arithmetic-characters`, mathematical snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`. No actual model is constructed here.
The supplied actual finite etale algebras retain their carriers and base maps.

Pinned mathlib supplies `TensorProduct.toIntegralClosure_bijective_of_smooth`.
The normalization comparison is its actual canonical map; Etale implies Smooth.
The generic-model normalization theorem is DERIVED below, not an assumed
normalization record, action, torsor, or specialized cover-existence theorem.
The library theorem covers arbitrary commutative rings and product algebras.
-/

/-!
Extraction source: `R5Lab.Aglib.RingTheory.IntegralClosure.FiniteEtale.Coactions`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`387e99c38d26e9c4be33345dae6480fe7699c213ca59c87750feaf70b04dd46b`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped TensorProduct
open Algebra.TensorProduct

namespace Algebra.FiniteEtale.GenericMaps

universe u

section NormalizationConsequence

variable (R K : Type u) [CommRing R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
variable {B : Type u} [CommRing B] [Algebra R B] [Algebra.Etale R B]

/-- Consequence of the proved pinned smooth-closure theorem, identifying the
actual model in its tensor orientation; no finite-etale model is constructed.
Supporting P8/P14 slice of `K2-018#prop:k2018-arithmetic-characters`
at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`; see the encoded subset and module scope. -/
def normalTensorModelEquiv : B ≃ₐ[B] integralClosure B (B ⊗[R] K) := by
  let eI : integralClosure R K ≃ₐ[R] R :=
    IsIntegralClosure.equiv R (integralClosure R K) K R
  let eB : B ⊗[R] integralClosure R K ≃ₐ[B] B :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B) eI).trans
      (Algebra.TensorProduct.rid R B B)
  exact eB.symm.trans (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R B K)
    TensorProduct.toIntegralClosure_bijective_of_smooth)

@[simp] theorem normalTensorModelEquiv_coe (b : B) :
    (normalTensorModelEquiv R K b : B ⊗[R] K) = b ⊗ₜ[R] (1 : K) := by
  simp [normalTensorModelEquiv, TensorProduct.toIntegralClosure]

/-- Derive generic normalization from the proved canonical comparison.
Finite integrality permits replacing B-integrality by R-integrality.
This proof uses canonical inclusion maps and makes no domain assumption on B.
Supporting P8/P14 slice of `K2-018#prop:k2018-arithmetic-characters`
at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`; see the encoded subset and module scope. -/
theorem finiteEtaleGenericNormalization (B : Type u) [CommRing B] [Algebra R B]
    [Module.Finite R B] [Algebra.Etale R B] :
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := K) (B := B)
    IsIntegralClosure B R (K ⊗[R] B) := by
  letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := K) (B := B)
  let e := normalTensorModelEquiv R K (B := B)
  let swap : (K ⊗[R] B) ≃ₐ[B] (B ⊗[R] K) :=
    { (Algebra.TensorProduct.comm R K B).toRingEquiv with
      commutes' b := by rfl }
  refine ⟨?_, ?_⟩
  · intro b c h
    apply e.injective
    apply Subtype.ext
    rw [normalTensorModelEquiv_coe, normalTensorModelEquiv_coe]
    exact congrArg swap h
  · intro x
    constructor
    · intro hx
      have hxs : IsIntegral B (swap x) := hx.tower_top.map swap.toAlgHom
      let y : integralClosure B (B ⊗[R] K) := ⟨swap x, hxs⟩
      refine ⟨e.symm y, ?_⟩
      apply swap.injective
      calc
        swap (algebraMap B (K ⊗[R] B) (e.symm y)) = (e (e.symm y) : B ⊗[R] K) := by
          rw [normalTensorModelEquiv_coe]
          rfl
        _ = swap x := by simp [y]
    · rintro ⟨b, rfl⟩
      exact (Algebra.IsIntegral.isIntegral (R := R) b).map
        (IsScalarTower.toAlgHom R B (K ⊗[R] B))

end NormalizationConsequence

section Tensor

variable (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]
variable {B C H J : Type u} [CommRing B] [Algebra R B]
  [CommRing C] [Algebra R C] [CommRing H] [Algebra R H]
  [CommRing J] [Algebra R J]

theorem genericMap_id :
    BaseChange.map R K (AlgHom.id R B) = AlgHom.id K (K ⊗[R] B) :=
  Algebra.TensorProduct.map_id

@[simp] theorem genericMap_comp (g : C →ₐ[R] H) (f : B →ₐ[R] C) :
    BaseChange.map R K (g.comp f) = (BaseChange.map R K g).comp (BaseChange.map R K f) :=
  Algebra.TensorProduct.map_id_comp g f

/-- Naturality of the actual tensor comparison.
Supporting P8/P14 slice of `K2-018#prop:k2018-arithmetic-characters`
at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`; see the encoded subset and module scope. -/
theorem genericTensorEquiv_naturality (f : B →ₐ[R] C) (g : H →ₐ[R] J) :
    (BaseChange.tensorEquiv R K (B := C) (H := J)).toAlgHom.comp
        (Algebra.TensorProduct.map (BaseChange.map R K f) (BaseChange.map R K g)) =
      (BaseChange.map R K (Algebra.TensorProduct.map f g)).comp
        (BaseChange.tensorEquiv R K (B := B) (H := H)).toAlgHom := by
  ext b <;> simp [BaseChange.map, BaseChange.tensorEquiv, Algebra.TensorProduct.one_def]

/-- Tensor two generic maps while retaining the actual model tensor carrier.
Supporting P8/P14 slice of `K2-018#prop:k2018-arithmetic-characters`
at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`; see the encoded subset and module scope. -/
def genericTensorMap
    (f : (K ⊗[R] B) →ₐ[K] (K ⊗[R] C))
    (g : (K ⊗[R] H) →ₐ[K] (K ⊗[R] J)) :
    (K ⊗[R] (B ⊗[R] H)) →ₐ[K] (K ⊗[R] (C ⊗[R] J)) :=
  (BaseChange.tensorEquiv R K (B := C) (H := J)).toAlgHom.comp
    ((Algebra.TensorProduct.map f g).comp
      (BaseChange.tensorEquiv R K (B := B) (H := H)).symm.toAlgHom)

@[simp] theorem genericTensorMap_genericMap (f : B →ₐ[R] C) (g : H →ₐ[R] J) :
    genericTensorMap R K (BaseChange.map R K f) (BaseChange.map R K g) =
      BaseChange.map R K (Algebra.TensorProduct.map f g) := by
  apply AlgHom.ext
  intro z
  obtain ⟨t, rfl⟩ := (BaseChange.tensorEquiv R K (B := B) (H := H)).surjective z
  simpa [genericTensorMap] using
    DFunLike.congr_fun (genericTensorEquiv_naturality R K f g) t

end Tensor

section ActualModels

variable (R K : Type u) [CommRing R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
variable {B C D : Type u} [CommRing B] [Algebra R B]
  [CommRing C] [Algebra R C] [CommRing D] [Algebra R D]
  [Module.Finite R B] [Algebra.Etale R B]
  [Module.Finite R C] [Algebra.Etale R C]
  [Module.Finite R D] [Algebra.Etale R D]

/-- Identify the supplied actual model with its literal integral closure.
This uses the derived integral-closure theorem, not a replacement model.
Supporting P8/P14 slice of `K2-018#prop:k2018-arithmetic-characters`
at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`; see the encoded subset and module scope. -/
def modelEquiv : B ≃ₐ[R] integralClosure R (K ⊗[R] B) := by
  letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := K) (B := B)
  letI := finiteEtaleGenericNormalization R K B
  exact IsIntegralClosure.equiv R B (K ⊗[R] B) (integralClosure R (K ⊗[R] B))

@[simp] theorem modelEquiv_coe (b : B) :
    (modelEquiv R K b : K ⊗[R] B) = (1 : K) ⊗ₜ[R] b := by
  letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := K) (B := B)
  letI := finiteEtaleGenericNormalization R K B
  exact IsIntegralClosure.algebraMap_equiv R B (K ⊗[R] B)
    (integralClosure R (K ⊗[R] B)) b

/-- Extend a generic map on the actual finite etale objects by integrality.
This is the derived full-faithfulness construction for the P8/P14 slice.
Supporting P8/P14 slice of `K2-018#prop:k2018-arithmetic-characters`
at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`; see the encoded subset and module scope. -/
def liftGeneric (f : (K ⊗[R] B) →ₐ[K] (K ⊗[R] C)) : B →ₐ[R] C :=
  (modelEquiv R K (B := C)).symm.toAlgHom.comp
    (((f.restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B)).codRestrict
        (integralClosure R (K ⊗[R] C)) (fun b =>
          (Algebra.IsIntegral.isIntegral (R := R) b).map
            ((f.restrictScalars R).comp Algebra.TensorProduct.includeRight)))

omit [Algebra.Etale R B] in
@[simp] theorem liftGeneric_one_tmul
    (f : (K ⊗[R] B) →ₐ[K] (K ⊗[R] C)) (b : B) :
    (1 : K) ⊗ₜ[R] liftGeneric R K f b = f ((1 : K) ⊗ₜ[R] b) := by
  rw [← modelEquiv_coe R K]
  simp [liftGeneric]
  rfl

omit [Algebra.Etale R B] in
@[simp] theorem genericMap_liftGeneric
    (f : (K ⊗[R] B) →ₐ[K] (K ⊗[R] C)) :
    BaseChange.map R K (liftGeneric R K f) = f := by
  apply Algebra.TensorProduct.ext'
  intro k b
  change k ⊗ₜ[R] liftGeneric R K f b = f (k ⊗ₜ[R] b)
  have ht : k ⊗ₜ[R] b = algebraMap K (K ⊗[R] B) k * ((1 : K) ⊗ₜ[R] b) := by
    change k ⊗ₜ[R] b = (k ⊗ₜ[R] (1 : B)) * ((1 : K) ⊗ₜ[R] b)
    simp
  rw [ht, map_mul, f.commutes]
  rw [← liftGeneric_one_tmul R K f b]
  change k ⊗ₜ[R] liftGeneric R K f b =
    (k ⊗ₜ[R] (1 : C)) * ((1 : K) ⊗ₜ[R] liftGeneric R K f b)
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

omit [Module.Finite R B] [Algebra.Etale R B] in
/-- Faithfulness uses the actual injection into the generic fibre.
Supporting P8/P14 slice of `K2-018#prop:k2018-arithmetic-characters`
at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`; see the encoded subset and module scope. -/
theorem genericMap_injective : Function.Injective
    (BaseChange.map R K : (B →ₐ[R] C) → ((K ⊗[R] B) →ₐ[K] (K ⊗[R] C))) := by
  letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := K) (B := C)
  letI := finiteEtaleGenericNormalization R K C
  intro f g h
  apply AlgHom.ext
  intro b
  apply IsIntegralClosure.algebraMap_injective C R (K ⊗[R] C)
  exact DFunLike.congr_fun h ((1 : K) ⊗ₜ[R] b)

omit [Algebra.Etale R B] in
@[simp] theorem liftGeneric_genericMap (f : B →ₐ[R] C) :
    liftGeneric R K (BaseChange.map R K f) = f := by
  apply genericMap_injective R K
  simp

/-- Actual finite etale model maps correspond to all maps of their actual
generic algebras, by the proved normalization theorem above.
Supporting P8/P14 slice of `K2-018#prop:k2018-arithmetic-characters`
at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`; see the encoded subset and module scope. -/
def genericHomEquiv :
    (B →ₐ[R] C) ≃ ((K ⊗[R] B) →ₐ[K] (K ⊗[R] C)) where
  toFun := BaseChange.map R K
  invFun := liftGeneric R K
  left_inv := liftGeneric_genericMap R K
  right_inv := genericMap_liftGeneric R K

/-- A generic algebra isomorphism extends to an isomorphism of the same
actual models. This is derived from full faithfulness, not assumed.
Supporting P8/P14 slice of `K2-018#prop:k2018-arithmetic-characters`
at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`; see the encoded subset and module scope. -/
def liftGenericEquiv (e : (K ⊗[R] B) ≃ₐ[K] (K ⊗[R] C)) : B ≃ₐ[R] C :=
  AlgEquiv.ofAlgHom (liftGeneric R K e.toAlgHom)
    (liftGeneric R K e.symm.toAlgHom)
    (by apply genericMap_injective R K; simp [genericMap_comp])
    (by apply genericMap_injective R K; simp [genericMap_comp])

/-- The actual morphism is an isomorphism precisely when its generic fibre
is; finite evidence about points is not used.
Supporting P8/P14 slice of `K2-018#prop:k2018-arithmetic-characters`
at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`; see the encoded subset and module scope. -/
theorem bijective_iff_generic (f : B →ₐ[R] C) :
    Function.Bijective f ↔ Function.Bijective (BaseChange.map R K f) := by
  constructor
  · intro hf
    let e := AlgEquiv.ofBijective f hf
    exact (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e).bijective
  · intro hf
    let e := AlgEquiv.ofBijective (BaseChange.map R K f) hf
    have he : (liftGenericEquiv R K e).toAlgHom = f :=
      liftGeneric_genericMap R K f
    have he' := (liftGenericEquiv R K e).bijective
    change Function.Bijective (liftGenericEquiv R K e).toAlgHom at he'
    rwa [he] at he'

end ActualModels

section CoactionDiagrams

variable (R K : Type u) [CommRing R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
variable (B H : Type u) [CommRing B] [Algebra R B]
  [CommRing H] [Algebra R H]

/-- Apply the actual coefficient counit to the right tensor factor.
Supporting P8/P14 slice of `K2-018#prop:k2018-arithmetic-characters`
at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`; see the encoded subset and module scope. -/
def coactionCounit (ε : H →ₐ[R] R) : B ⊗[R] H →ₐ[R] B :=
  (Algebra.TensorProduct.rid R R B).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id R B) ε)

/-- Algebra-level right coaction for fixed actual coefficient structure maps.
For a Hopf coefficient algebra take its genuine counit and comultiplication.
Only the bialgebra part is needed to transfer the coaction laws.
Supporting P8/P14 slice of `K2-018#prop:k2018-arithmetic-characters`
at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`; see the encoded subset and module scope. -/
@[ext] structure AlgebraCoaction (ε : H →ₐ[R] R) (Δ : H →ₐ[R] H ⊗[R] H) where
  /-- The supplied actual R-algebra coaction on the model algebra B. -/
  coact : B →ₐ[R] B ⊗[R] H
  counit : (coactionCounit R B H ε).comp coact = AlgHom.id R B
  coassoc : (Algebra.TensorProduct.map (AlgHom.id R B) Δ).comp coact =
    (Algebra.TensorProduct.assoc R R R B H H).toAlgHom.comp
      ((Algebra.TensorProduct.map coact (AlgHom.id R H)).comp coact)

/-- A genuine generic algebra coaction, expressed through the canonical
generic tensor comparison on the same actual objects. H need not be split:
the input is an algebra map and its coalgebra diagrams, not a set of
K-rational automorphisms or an action already defined on the model.
Supporting P8/P14 slice of `K2-018#prop:k2018-arithmetic-characters`
at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`; see the encoded subset and module scope. -/
structure GenericCoaction (ε : H →ₐ[R] R) (Δ : H →ₐ[R] H ⊗[R] H) where
  /-- The supplied coaction on the original generic tensor algebra, valued in the canonical
  generic tensor of B tensor H. -/
  coact : (K ⊗[R] B) →ₐ[K] (K ⊗[R] (B ⊗[R] H))
  counit : (BaseChange.map R K (coactionCounit R B H ε)).comp coact =
    AlgHom.id K (K ⊗[R] B)
  coassoc : (BaseChange.map R K (Algebra.TensorProduct.map (AlgHom.id R B) Δ)).comp coact =
    (BaseChange.map R K (Algebra.TensorProduct.assoc R R R B H H).toAlgHom).comp
      ((genericTensorMap R K coact (AlgHom.id K (K ⊗[R] H))).comp coact)

local instance tensorEtale {C D : Type u} [CommRing C] [CommRing D]
    [Algebra R C] [Algebra R D] [Algebra.Etale R C] [Algebra.Etale R D] :
    Algebra.Etale R (C ⊗[R] D) := Algebra.Etale.comp R C _

variable [Module.Finite R B] [Algebra.Etale R B]
  [Module.Finite R H] [Algebra.Etale R H]
variable {ε : H →ₐ[R] R} {Δ : H →ₐ[R] H ⊗[R] H}

/-- Extend the nonsplit generic coaction to the SAME supplied finite etale
model and coefficient algebra. Both laws are proved by faithful generic
base change after constructing the integral map. P8/P14 foundational slice
of `K2-018#prop:k2018-arithmetic-characters`, snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`; no external normality or
normalization premise and no E-model construction is introduced. -/
def extendCoaction (α : GenericCoaction R K B H ε Δ) : AlgebraCoaction R B H ε Δ where
  coact := liftGeneric R K α.coact
  counit := by
    apply genericMap_injective R K
    simpa only [genericMap_comp, genericMap_liftGeneric, genericMap_id] using α.counit
  coassoc := by
    apply genericMap_injective R K
    simpa only [genericMap_comp, ← genericTensorMap_genericMap,
      genericMap_liftGeneric, genericMap_id] using α.coassoc

@[simp] theorem extendCoaction_generic (α : GenericCoaction R K B H ε Δ) :
    BaseChange.map R K (extendCoaction R K B H α).coact = α.coact :=
  genericMap_liftGeneric R K α.coact

/-- Uniqueness holds on the actual model, including the two diagram laws.
Supporting P8/P14 slice of `K2-018#prop:k2018-arithmetic-characters`
at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`; see the encoded subset and module scope. -/
theorem extendCoaction_unique (α : GenericCoaction R K B H ε Δ)
    (β : AlgebraCoaction R B H ε Δ) (h : BaseChange.map R K β.coact = α.coact) :
    β = extendCoaction R K B H α := by
  apply AlgebraCoaction.ext
  apply genericMap_injective R K
  simpa using h

/-- The actual affine transporter map. For a right group action its
contravariant formula is b tensor c |-> (b tensor 1) * coact(c).
Supporting P8/P14 slice of `K2-018#prop:k2018-arithmetic-characters`
at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`; see the encoded subset and module scope. -/
def transporter (δ : B →ₐ[R] B ⊗[R] H) : B ⊗[R] B →ₐ[R] B ⊗[R] H :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft δ (fun _ _ => .all _ _)

/-- The generic transporter on the canonically identified product fibre.
Supporting P8/P14 slice of `K2-018#prop:k2018-arithmetic-characters`
at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`; see the encoded subset and module scope. -/
def genericTransporter
    (δ : (K ⊗[R] B) →ₐ[K] (K ⊗[R] (B ⊗[R] H))) :
    (K ⊗[R] (B ⊗[R] B)) →ₐ[K] (K ⊗[R] (B ⊗[R] H)) :=
  (Algebra.TensorProduct.lift (BaseChange.map R K Algebra.TensorProduct.includeLeft) δ
      (fun _ _ => .all _ _)).comp (BaseChange.tensorEquiv R K).symm.toAlgHom

omit [IsIntegrallyClosed R] [IsFractionRing R K]
  [Module.Finite R B] [Algebra.Etale R B] [Module.Finite R H] [Algebra.Etale R H] in
/-- The transporter is the actual generic base change of its model map.
Supporting P8/P14 slice of `K2-018#prop:k2018-arithmetic-characters`
at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`; see the encoded subset and module scope. -/
theorem genericTransporter_genericMap (δ : B →ₐ[R] B ⊗[R] H) :
    genericTransporter R K B H (BaseChange.map R K δ) =
      BaseChange.map R K (transporter R B H δ) := by
  have ht : (BaseChange.map R K (transporter R B H δ)).comp
      (BaseChange.tensorEquiv R K (B := B) (H := B)).toAlgHom =
      Algebra.TensorProduct.lift (BaseChange.map R K Algebra.TensorProduct.includeLeft)
        (BaseChange.map R K δ) (fun _ _ => .all _ _) := by
    ext b <;> simp [BaseChange.map, transporter, Algebra.TensorProduct.one_def]
    simp only [← Algebra.TensorProduct.one_def, one_mul]
  apply AlgHom.ext
  intro z
  obtain ⟨t, rfl⟩ := (BaseChange.tensorEquiv R K (B := B) (H := B)).surjective z
  simpa [genericTransporter] using (DFunLike.congr_fun ht t).symm

/-- The generic torsor transporter isomorphism extends to an isomorphism
of the actual product models. Local nonemptiness/faithful flatness is a
separate condition when packaging this as a scheme torsor.
Supporting P8/P14 slice of `K2-018#prop:k2018-arithmetic-characters`
at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`; see the encoded subset and module scope. -/
theorem transporter_bijective_of_generic (α : GenericCoaction R K B H ε Δ)
    (h : Function.Bijective (genericTransporter R K B H α.coact)) :
    Function.Bijective (transporter R B H (extendCoaction R K B H α).coact) := by
  apply (bijective_iff_generic R K _).mpr
  rw [← genericTransporter_genericMap, extendCoaction_generic]
  exact h

end CoactionDiagrams

section LiteralNormalization

open integralClosure
attribute [local instance] tensorEtale

variable (R K A H : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Algebra.IsIntegral K A] [CommRing H] [Algebra R H]

/-- The canonical comparison with the ORIGINAL actual generic algebra A and
the actual coefficient fibre. Its model is literally integralClosure R A.
Supporting P8/P14 slice of `K2-018#prop:k2018-arithmetic-characters`
at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`; see the encoded subset and module scope. -/
def actualTensorEquiv :
    K ⊗[R] (integralClosure R A ⊗[R] H) ≃ₐ[K] A ⊗[K] (K ⊗[R] H) :=
  (BaseChange.tensorEquiv R K (B := integralClosure R A) (H := H)).symm.trans
    (Algebra.TensorProduct.congr (genericFiberEquiv R K A)
      (AlgEquiv.refl : (K ⊗[R] H) ≃ₐ[K] (K ⊗[R] H)))

variable [Module.Finite R (integralClosure R A)] [Algebra.Etale R (integralClosure R A)]
  [Module.Finite R H] [Algebra.Etale R H]

/-- Extend an actual generic coaction MAP on A to its SAME literal model.
Etaleness of that model is an explicit independently supplied condition; this
module does not construct or replace an E-owned model. Coaction laws are
handled by `extendCoaction` on the canonical generic fibre.
Supporting P8/P14 slice of `K2-018#prop:k2018-arithmetic-characters`
at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`; see the encoded subset and module scope. -/
def liftActualCoactionHom (δ : A →ₐ[K] A ⊗[K] (K ⊗[R] H)) :
    integralClosure R A →ₐ[R] integralClosure R A ⊗[R] H :=
  liftGeneric R K ((actualTensorEquiv R K A H).symm.toAlgHom.comp
    (δ.comp (genericFiberEquiv R K A).toAlgHom))

omit [IsNoetherianRing R] in
/-- Exact compatibility with the fixed original generic algebra and the
canonical FiniteModel.genericFiberEquiv. The square is a CONCLUSION, not an
assumed extension/action/square premise.
Supporting P8/P14 slice of `K2-018#prop:k2018-arithmetic-characters`
at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`; see the encoded subset and module scope. -/
theorem liftActualCoactionHom_square (δ : A →ₐ[K] A ⊗[K] (K ⊗[R] H)) :
    (actualTensorEquiv R K A H).toAlgHom.comp
        (BaseChange.map R K (liftActualCoactionHom R K A H δ)) =
      δ.comp (genericFiberEquiv R K A).toAlgHom := by
  ext x
  simp [liftActualCoactionHom]

end LiteralNormalization

end Algebra.FiniteEtale.GenericMaps
