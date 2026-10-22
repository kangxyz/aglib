/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.GenericTargetFittingTransport
public import Aglib.RingTheory.DiscreteValuationRing.GenericTensorRelations

/-! # The actual fixed modification point on the generic target

The original modification coordinates supply the divisibility witnesses after
the actual generic source-target square. Regularity follows from the image
uniformizer, so the resulting point factors the same generic tensor target.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Algebra.NeronModification ParameterLocalization

namespace GenericParameterCentre

variable {R S B ι : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [CommRing B] [Algebra R B] [Finite ι]
  (p : R) [Fact (Irreducible p)] [Fact (Irreducible (algebraMap R S p))]
  (χ : B →ₐ[R] S)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "R₁" => ParameterLocalization.Ring R ι p
local notation "S₁" => ParameterLocalization.Ring S ι (algebraMap R S p)
local notation "B₁" => B ⊗[R] R₁

/-- A fixed original modification point supplies an actual point of the same
modification after generic coefficient extension. The distinguished scalar is
the direct image of the new parameter uniformizer, and the centre generators
are precisely the images of the original family. -/
theorem exists_lift_tensorTargetOverParameters
    {ν : Type*} (g : ν → B)
    (χM : Modification (algebraMap R B p) g →+* S)
    (hχM : χM.comp (of (algebraMap R B p) g) = χ.toRingHom) :
    letI : Algebra R₁ S₁ := (parameterMap R S ι p).toRingHom.toAlgebra
    ∃ χN : Modification (algebraMap R₁ B₁ (algebraMap R R₁ p))
        (fun j => algebraMap B B₁ (g j)) →+* S₁,
      χN.comp (of (algebraMap R₁ B₁ (algebraMap R R₁ p))
        (fun j => algebraMap B B₁ (g j))) =
          (tensorTargetOverParameters R S ι p χ).toRingHom := by
  let : Algebra R₁ S₁ := (parameterMap R S ι p).toRingHom.toAlgebra
  let : IsDiscreteValuationRing S₁ :=
    isDiscreteValuationRing S ι (algebraMap R S p)
  let χ₁ : B₁ →ₐ[R₁] S₁ := tensorTargetOverParameters R S ι p χ
  let σ : S →+* S₁ := algebraMap S S₁
  let p₁ : R₁ := algebraMap R R₁ p
  let g₁ : ν → B₁ := fun j => algebraMap B B₁ (g j)
  have hpA : algebraMap R₁ B₁ p₁ = algebraMap B B₁ (algebraMap R B p) :=
    (IsScalarTower.algebraMap_apply R R₁ B₁ p).symm.trans
      (IsScalarTower.algebraMap_apply R B B₁ p)
  have hp₁S : Irreducible (algebraMap R₁ S₁ p₁) := by
    change Irreducible (parameterMap R S ι p (algebraMap R R₁ p))
    rw [parameterMap_uniformizer]
    exact uniformizer_irreducible S ι (algebraMap R S p)
  let z : ν → S₁ := fun j => σ (χM (coordinate (algebraMap R B p) g j))
  have hz (j : ν) : χ₁ (algebraMap R₁ B₁ p₁) * z j = χ₁ (g₁ j) := by
    have h := congrArg (fun x => σ (χM x)) (of_mul_coordinate (algebraMap R B p) g j)
    rw [map_mul, map_mul] at h
    have hpoint (a : B) : χM (of (algebraMap R B p) g a) = χ a :=
      DFunLike.congr_fun hχM a
    rw [hpoint, hpoint] at h
    have hsquare (a : B) : χ₁ (algebraMap B B₁ a) = σ (χ a) :=
      DFunLike.congr_fun (tensorTarget_comp_algebraMap (ι := ι) p χ) a
    rw [hpA, hsquare, hsquare]
    exact h
  have hregular : IsRegular (χ₁ (algebraMap R₁ B₁ p₁)) := by
    rw [χ₁.commutes]
    exact isRegular_iff_ne_zero.mpr hp₁S.ne_zero
  refine ⟨lift (algebraMap R₁ B₁ p₁) g₁ χ₁.toRingHom z hz hregular, ?_⟩
  exact lift_comp_of (algebraMap R₁ B₁ p₁) g₁ χ₁.toRingHom z hz hregular

end GenericParameterCentre
