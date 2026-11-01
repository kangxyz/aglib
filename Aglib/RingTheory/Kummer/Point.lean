/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.Evaluation
public import Aglib.RingTheory.Kummer.RegularParameter

/-! # The original closed field point of a root algebra

A local field-valued coefficient point kills every element of the maximal
ideal. The original root therefore evaluates to zero. Integrality and the
actual local root algebra make this evaluation local, without Noetherianity,
domain assumptions, or a replacement residue field.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace Algebra.Kummer

variable (R Ω : Type*) [CommRing R] [IsLocalRing R] [Field Ω] [Algebra R Ω]
  [IsLocalHom (algebraMap R Ω)]

/-- A local field point kills every element of the original maximal ideal. -/
theorem rootPoint_coefficient_zero (f : R) (hf : f ∈ maximalIdeal R) :
    algebraMap R Ω f = 0 := by
  by_contra h
  exact hf (isUnit_of_map_unit (algebraMap R Ω) f (isUnit_iff_ne_zero.mpr h))

variable (N : ℕ) (hN : 0 < N) (f : R) (hf : f ∈ maximalIdeal R)

/-- Evaluate the original root at zero in the original field. -/
def rootPoint : RootAlgebra N f →ₐ[R] Ω :=
  rootEvaluation R Ω N f 0 (by
    rw [zero_pow (Nat.ne_of_gt hN), rootPoint_coefficient_zero R Ω f hf])

@[simp] theorem rootPoint_root :
    rootPoint R Ω N hN f hf (AdjoinRoot.root (rootPolynomial N f)) = 0 :=
  rootEvaluation_root ..

/-- The original root evaluation is local, as its actual kernel lies over the
coefficient maximal ideal and is maximal by integrality. -/
theorem rootPoint_isLocalHom : IsLocalHom (rootPoint R Ω N hN f hf).toRingHom := by
  let T := RootAlgebra N f
  let p := rootPoint R Ω N hN f hf
  let : Module.Finite R T := root_finite N hN f
  let : IsLocalRing T := parameterRoot_isLocalRing R f hf N hN
  have hker : (RingHom.ker p.toRingHom).under R = maximalIdeal R := by
    ext r
    change p (algebraMap R T r) = 0 ↔ ¬ IsUnit r
    rw [p.commutes]
    exact ⟨fun hz hr => (hr.map (algebraMap R Ω)).ne_zero hz,
      rootPoint_coefficient_zero R Ω r⟩
  let : (RingHom.ker p.toRingHom).IsPrime := RingHom.ker_isPrime _
  have hm : (RingHom.ker p.toRingHom).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) _ (by rw [hker]; infer_instance)
  have he := IsLocalRing.eq_maximalIdeal hm
  constructor
  intro t ht
  by_contra hn
  have hz : p t = 0 := by
    change t ∈ RingHom.ker p.toRingHom
    rwa [he]
  exact ht.ne_zero hz

variable (B : Type*) [CommRing B] [IsLocalRing B] [Algebra R B]
  [Algebra B Ω] [IsScalarTower R B Ω] [IsLocalHom (algebraMap B Ω)]

include Ω hf in
omit [IsLocalHom (algebraMap B Ω)] in
/-- The same point forces the original parameter image into the new maximal ideal. -/
theorem rootPoint_parameter_mem : algebraMap R B f ∈ maximalIdeal B := by
  intro h
  have hu := h.map (algebraMap B Ω)
  rw [← IsScalarTower.algebraMap_apply, rootPoint_coefficient_zero R Ω f hf] at hu
  exact not_isUnit_zero hu

/-- The whole pointed root-change triangle, with the same original field. -/
theorem rootPoint_baseChange :
    ((rootPoint B Ω N hN (algebraMap R B f)
      (rootPoint_parameter_mem R Ω f hf B)).restrictScalars R).comp
        (rootBaseChangeHom B N f) = rootPoint R Ω N hN f hf :=
  rootEvaluation_baseChange R B Ω N f 0 _ _

end Algebra.Kummer
