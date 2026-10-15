/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Descent.Nilpotent

/-!
# Finite purely inseparable descent after arbitrary affine base change

This extends the nilpotent overlap calculation to `R ⊗[K] L` for an arbitrary
commutative `K`-algebra `R`. The two scalar coordinates are displayed explicitly
in the intermediate calculation; no Noetherian condition is used.

## Extraction basis

Transferred from `R5Lab.RingTheory.Descent.BaseChangedPureAlgebra` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`bd2605f8241a8000a21f8f4894d36214957e49e8fe2b396220a4b23453cb378e`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section

open scoped _root_.TensorProduct

namespace Algebra.Descent.PurelyInseparable

open Algebra.Descent

universe u v w t

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  (R : Type w) [CommRing R] [Algebra K R]
  (B : Type t) [CommRing B] [Algebra K B] [Algebra R B] [IsScalarTower K R B]

/-- The overlap tensor algebra is the field-extension tensor algebra after
commuting and cancelling the scalar-extension factor. -/
def baseChangedOverlapEquiv : (R ⊗[K] L) ⊗[R] B ≃ₐ[R] B ⊗[K] L :=
  (Algebra.TensorProduct.comm R (R ⊗[K] L) B).trans
    (Algebra.TensorProduct.cancelBaseChange K R R B L)

@[simp] theorem baseChangedOverlapEquiv_tmul (r : R) (l : L) (b : B) :
    baseChangedOverlapEquiv K L R B ((r ⊗ₜ[K] l) ⊗ₜ[R] b) = (r • b) ⊗ₜ[K] l := by
  simp only [baseChangedOverlapEquiv, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.cancelBaseChange_tmul]

variable [Algebra L B] [IsScalarTower K L B]
  [Algebra (R ⊗[K] L) B] [IsScalarTower R (R ⊗[K] L) B]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [Algebra K B] [IsScalarTower K R B] [IsScalarTower K L B] in
theorem tensor_scalar_coordinates
    (hL : ∀ l : L, algebraMap (R ⊗[K] L) B (1 ⊗ₜ[K] l) = algebraMap L B l)
    (r : R) (l : L) :
    algebraMap (R ⊗[K] L) B (r ⊗ₜ[K] l) = algebraMap R B r * algebraMap L B l := by
  have he : (r ⊗ₜ[K] l : R ⊗[K] L) = (r ⊗ₜ[K] 1) * (1 ⊗ₜ[K] l) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [he, map_mul, hL]
  congr 1
  exact (IsScalarTower.algebraMap_apply R (R ⊗[K] L) B r).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem counit_baseChanged_comp_equiv
    (hL : ∀ l : L, algebraMap (R ⊗[K] L) B (1 ⊗ₜ[K] l) = algebraMap L B l) :
    (Algebra.TensorProduct.tensorAugmentation K L B).toRingHom.comp
        (baseChangedOverlapEquiv K L R B).toRingHom =
      (counit R (R ⊗[K] L) B).toRingHom := by
  apply RingHom.ext
  intro z
  induction z using _root_.TensorProduct.inductionOn with
  | tmul s b =>
    induction s using _root_.TensorProduct.inductionOn with
    | tmul r l =>
      change Algebra.TensorProduct.tensorAugmentation K L B
        (baseChangedOverlapEquiv K L R B ((r ⊗ₜ[K] l) ⊗ₜ[R] b)) =
          (r ⊗ₜ[K] l : R ⊗[K] L) • b
      rw [baseChangedOverlapEquiv_tmul, Algebra.TensorProduct.tensorAugmentation_tmul,
        Algebra.smul_def, Algebra.smul_def, tensor_scalar_coordinates K L R B hL]
      ac_rfl
    | add x y hx hy => simp only [_root_.TensorProduct.add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem counit_baseChanged_ker_isNilpotent_of_coordinates
    [IsPurelyInseparable K L] [Module.Finite K L]
    (hL : ∀ l : L, algebraMap (R ⊗[K] L) B (1 ⊗ₜ[K] l) = algebraMap L B l) :
    IsNilpotent (RingHom.ker (counit R (R ⊗[K] L) B).toRingHom) := by
  rw [← counit_baseChanged_comp_equiv K L R B hL, ← RingHom.comap_ker]
  exact Ideal.isNilpotent_comap_of_injective _ (baseChangedOverlapEquiv K L R B).toRingHom
    (baseChangedOverlapEquiv K L R B).injective
    (Algebra.TensorProduct.tensorAugmentation_ker_isNilpotent K L B)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [Algebra K B] [IsScalarTower K R B] [Algebra L B] [IsScalarTower K L B] in
/-- Nilpotence for the exact overlap counit, with all field-coordinate
structures constructed internally from the actual scalar-extension algebra. -/
theorem counit_baseChanged_ker_isNilpotent
    [IsPurelyInseparable K L] [Module.Finite K L] :
    IsNilpotent (RingHom.ker (counit R (R ⊗[K] L) B).toRingHom) := by
  let : Algebra K B := ((algebraMap R B).comp (algebraMap K R)).toAlgebra
  let : IsScalarTower K R B := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra L B := ((algebraMap (R ⊗[K] L) B).comp
    (Algebra.TensorProduct.includeRight : L →ₐ[K] R ⊗[K] L).toRingHom).toAlgebra
  let : IsScalarTower K L B := IsScalarTower.of_algebraMap_eq' (by
    ext k
    symm
    change algebraMap (R ⊗[K] L) B (1 ⊗ₜ[K] algebraMap K L k) =
      algebraMap R B (algebraMap K R k)
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    exact (IsScalarTower.algebraMap_apply R (R ⊗[K] L) B (algebraMap K R k)).symm)
  exact counit_baseChanged_ker_isNilpotent_of_coordinates K L R B (fun _ ↦ rfl)

omit [Algebra K B] [IsScalarTower K R B] [Algebra L B] [IsScalarTower K L B] in
/-- A formally étale algebra over an arbitrary scalar extension `R ⊗[K] L`
gets an actual descent coaction when `L/K` is finite and purely inseparable. -/
def baseChangedPureDatum [IsPurelyInseparable K L] [Module.Finite K L]
    [Algebra.FormallyEtale (R ⊗[K] L) B] : Datum R (R ⊗[K] L) B :=
  Algebra.Descent.Nilpotent.datumOfNilpotentCounits R (R ⊗[K] L) B
    (counit_baseChanged_ker_isNilpotent K L R B)
    (counit_baseChanged_ker_isNilpotent K L R ((R ⊗[K] L) ⊗[R] B))

omit [Algebra K B] [IsScalarTower K R B] [Algebra L B] [IsScalarTower K L B] in
/-- Reconstruction for the constructed invariant algebra, with no Noetherian
or finite type assumption on the affine base algebra `R`. -/
def baseChangedPureEquiv [IsPurelyInseparable K L] [Module.Finite K L]
    [Algebra.FormallyEtale (R ⊗[K] L) B] :
    (R ⊗[K] L) ⊗[R] (baseChangedPureDatum K L R B).invariants ≃ₐ[R ⊗[K] L] B :=
  (baseChangedPureDatum K L R B).baseChangeEquiv

omit [Algebra K B] [IsScalarTower K R B] [Algebra L B] [IsScalarTower K L B] in
theorem baseChangedPure_invariants_finite
    [IsPurelyInseparable K L] [Module.Finite K L]
    [Algebra.FormallyEtale (R ⊗[K] L) B] [Module.Finite (R ⊗[K] L) B] :
    Module.Finite R (baseChangedPureDatum K L R B).invariants :=
  (baseChangedPureDatum K L R B).invariants_finite

omit [Algebra K B] [IsScalarTower K R B] [Algebra L B] [IsScalarTower K L B] in
theorem baseChangedPure_invariants_etale
    [IsPurelyInseparable K L] [Module.Finite K L] [Algebra.Etale (R ⊗[K] L) B] :
    Algebra.Etale R (baseChangedPureDatum K L R B).invariants :=
  (baseChangedPureDatum K L R B).invariants_etale

variable {B} {C : Type*} [CommRing C] [Algebra R C] [Algebra (R ⊗[K] L) C]
  [IsScalarTower R (R ⊗[K] L) C]

omit [Algebra K B] [IsScalarTower K R B] [Algebra L B] [IsScalarTower K L B] in
/-- Every map of the scalar-extended formally étale algebras respects their
proved descent coactions. The FE-02 invariants map therefore descends it. -/
def baseChangedPureDatumHom [IsPurelyInseparable K L] [Module.Finite K L]
    [Algebra.FormallyEtale (R ⊗[K] L) B] [Algebra.FormallyEtale (R ⊗[K] L) C]
    (f : B →ₐ[R ⊗[K] L] C) :
    (baseChangedPureDatum K L R B).Hom (baseChangedPureDatum K L R C) :=
  Algebra.Descent.Nilpotent.datumOfNilpotentCounitsHom R (R ⊗[K] L)
    (counit_baseChanged_ker_isNilpotent K L R B)
    (counit_baseChanged_ker_isNilpotent K L R ((R ⊗[K] L) ⊗[R] B))
    (counit_baseChanged_ker_isNilpotent K L R C)
    (counit_baseChanged_ker_isNilpotent K L R ((R ⊗[K] L) ⊗[R] C)) f

omit [Algebra K B] [IsScalarTower K R B] [Algebra L B] [IsScalarTower K L B] in
/-- The map on canonical descent invariants induced by `f` for a finite purely inseparable field
extension `L/K` and formally étale `(R ⊗[K] L)`-algebras. -/
def baseChangedPureInvariantsMap [IsPurelyInseparable K L] [Module.Finite K L]
    [Algebra.FormallyEtale (R ⊗[K] L) B] [Algebra.FormallyEtale (R ⊗[K] L) C]
    (f : B →ₐ[R ⊗[K] L] C) :
    (baseChangedPureDatum K L R B).invariants →ₐ[R] (baseChangedPureDatum K L R C).invariants :=
  (baseChangedPureDatumHom K L R f).invariantsMap

end Algebra.Descent.PurelyInseparable
