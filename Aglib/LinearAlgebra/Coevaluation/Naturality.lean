/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.LinearAlgebra.Coevaluation
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Naturality of the original coevaluation map

The selected map is Mathlib's native coevaluation. Its two contraction
triangles imply the whole linear-map naturality equation. The current native
coevaluation API is over fields; this file retains that scope and introduces
neither another coevaluation nor a basis parameter.
-/

@[expose] public section

noncomputable section

open Module
open scoped TensorProduct

namespace TensorProduct

variable (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

private theorem coevaluation_tensorHom_identity :
    _root_.dualTensorHom k V V
      (TensorProduct.comm k V (Dual k V) (coevaluation k V 1)) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  have h (x : V ⊗[k] Dual k V) :
      _root_.dualTensorHom k V V (TensorProduct.comm k V (Dual k V) x) v =
        TensorProduct.rid k V
          ((contractLeft k V).lTensor V
            (TensorProduct.assoc k V (Dual k V) V (x ⊗ₜ[k] v))) := by
    induction x using TensorProduct.inductionOn with
    | tmul w f => simp
    | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply, TensorProduct.add_tmul, hx, hy]
  rw [h]
  have ht := LinearMap.congr_fun (contractLeft_assoc_coevaluation' k V) (1 ⊗ₜ[k] v)
  simpa using congrArg (TensorProduct.rid k V) ht

variable {k V} {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- Naturality of the whole original coevaluation map for an actual linear map. -/
theorem coevaluation_naturality (f : V →ₗ[k] W) :
    TensorProduct.map f (LinearMap.id : Dual k V →ₗ[k] Dual k V) ∘ₗ coevaluation k V =
      TensorProduct.map (LinearMap.id : W →ₗ[k] W) f.dualMap ∘ₗ coevaluation k W := by
  apply LinearMap.ext_ring
  change TensorProduct.map f LinearMap.id (coevaluation k V 1) =
    TensorProduct.map LinearMap.id f.dualMap (coevaluation k W 1)
  apply (TensorProduct.comm k W (Dual k V)).injective
  apply (_root_.dualTensorHomEquiv k V W).injective
  change _root_.dualTensorHom k V W
      (TensorProduct.comm k W (Dual k V)
        (TensorProduct.map f LinearMap.id (coevaluation k V 1))) =
    _root_.dualTensorHom k V W
      (TensorProduct.comm k W (Dual k V)
        (TensorProduct.map LinearMap.id f.dualMap (coevaluation k W 1)))
  rw [← TensorProduct.map_comm LinearMap.id f,
    ← TensorProduct.map_comm f.dualMap LinearMap.id]
  have hl := LinearMap.congr_fun (_root_.dualTensorHom_comp_lTensor (M := V) f)
    (TensorProduct.comm k V (Dual k V) (coevaluation k V 1))
  have hr := LinearMap.congr_fun (_root_.dualTensorHom_comp_rTensor_dualMap (P := W) f)
    (TensorProduct.comm k W (Dual k W) (coevaluation k W 1))
  simp only [LinearMap.comp_apply, coevaluation_tensorHom_identity,
    LinearMap.compRight_apply, LinearMap.lcomp_apply', LinearMap.comp_id, LinearMap.id_comp]
    at hl hr
  simpa only [LinearMap.lTensor_def, LinearMap.rTensor_def] using hl.trans hr.symm

/-- The same whole naturality equation at an arbitrary original coefficient. -/
theorem coevaluation_naturality_apply (f : V →ₗ[k] W) (r : k) :
    TensorProduct.map f (LinearMap.id : Dual k V →ₗ[k] Dual k V) (coevaluation k V r) =
      TensorProduct.map (LinearMap.id : W →ₗ[k] W) f.dualMap (coevaluation k W r) :=
  LinearMap.congr_fun (coevaluation_naturality f) r

section CoefficientMap

variable (R M K : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]
  [CommSemiring K] [Algebra R K]

/-- The canonical change of coefficients on the original primal-dual tensor. -/
def coevaluationBaseChangeMap :
    M ⊗[R] Dual R M →ₗ[R] (K ⊗[R] M) ⊗[K] Dual K (K ⊗[R] M) :=
  TensorProduct.mapOfCompatibleSMul K R R (K ⊗[R] M) (Dual K (K ⊗[R] M)) ∘ₗ
    TensorProduct.map (TensorProduct.mk R K M 1) (Module.Dual.baseChange K)

@[simp]
theorem coevaluationBaseChangeMap_tmul (m : M) (f : Dual R M) :
    coevaluationBaseChangeMap R M K (m ⊗ₜ[R] f) =
      (1 ⊗ₜ[R] m) ⊗ₜ[K] f.baseChange K := rfl

end CoefficientMap

section FieldExtension

variable (k V) (K : Type*) [Field K] [Algebra k K]

omit [FiniteDimensional k V] in
private theorem tensorHom_coevaluationBaseChangeMap (x : V ⊗[k] Dual k V) (v : V) :
    _root_.dualTensorHom K (K ⊗[k] V) (K ⊗[k] V)
        (TensorProduct.comm K (K ⊗[k] V) (Dual K (K ⊗[k] V))
          (coevaluationBaseChangeMap k V K x)) (1 ⊗ₜ[k] v) =
      1 ⊗ₜ[k] (_root_.dualTensorHom k V V
        (TensorProduct.comm k V (Dual k V) x) v) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, TensorProduct.tmul_add, hx, hy]
  | tmul w f =>
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul]

/-- Coevaluation at one is preserved by the original module and dual coefficient maps. -/
theorem coevaluation_baseChange_one :
    coevaluationBaseChangeMap k V K (coevaluation k V 1) =
      coevaluation K (K ⊗[k] V) 1 := by
  apply (TensorProduct.comm K (K ⊗[k] V) (Dual K (K ⊗[k] V))).injective
  apply (_root_.dualTensorHomEquiv K (K ⊗[k] V) (K ⊗[k] V)).injective
  change _root_.dualTensorHom K (K ⊗[k] V) (K ⊗[k] V)
      (TensorProduct.comm K (K ⊗[k] V) (Dual K (K ⊗[k] V))
        (coevaluationBaseChangeMap k V K (coevaluation k V 1))) =
    _root_.dualTensorHom K (K ⊗[k] V) (K ⊗[k] V)
      (TensorProduct.comm K (K ⊗[k] V) (Dual K (K ⊗[k] V))
        (coevaluation K (K ⊗[k] V) 1))
  rw [coevaluation_tensorHom_identity]
  apply (TensorProduct.isBaseChange k V K).algHom_ext
  intro v
  change _ = 1 ⊗ₜ[k] v
  simpa only [coevaluation_tensorHom_identity, LinearMap.id_apply, TensorProduct.mk_apply]
    using tensorHom_coevaluationBaseChangeMap k V K (coevaluation k V 1) v

/-- The whole original coevaluation map is natural under an extension of fields. -/
theorem coevaluation_baseChange :
    coevaluationBaseChangeMap k V K ∘ₗ coevaluation k V =
      (coevaluation K (K ⊗[k] V)).restrictScalars k ∘ₗ Algebra.linearMap k K := by
  apply LinearMap.ext_ring
  simpa using coevaluation_baseChange_one k V K

end FieldExtension

end TensorProduct
