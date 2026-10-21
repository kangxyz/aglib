/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.TensorTargetCentre

/-! # The actual local map from the selected source centre to the target DVR -/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace SeparableResidueExtension

variable (R E S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field E] [Algebra (ResidueField R) E] [Module.Finite (ResidueField R) E]
  [Algebra.IsSeparable (ResidueField R) E]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)]
  (e : E →ₐ[ResidueField R] ResidueField S)

/-- The base DVR acts on the specified residue extension through its residue map. -/
local instance centreTargetResidueAlgebra : Algebra R E :=
  ((algebraMap (ResidueField R) E).comp (residue R)).toAlgebra

variable {B : Type*} [CommRing B] [Algebra R B]
  (f : B →ₐ[R] E) (g : B →ₐ[R] S)
  (hfg : ∀ b, residue S (g b) = e (f b))

include hfg in
/-- Every actual denominator outside the selected centre maps to a unit. -/
theorem tensorTarget_denominator_unit
    (s : (SeparableTensorDiagonal.sourceIdeal (ResidueField R) E
      (tensorResidue R E f)).primeCompl) :
    IsUnit (tensorTarget R E S e g s) := by
  apply (residue_ne_zero_iff_isUnit _).mp
  intro hs
  apply s.property
  exact (tensorTarget_residue_kernel R E S e f g hfg).le hs

/-- The actual tensor map extends across precisely the selected centre. -/
def centreTargetMap : CentreRing R E f →+* TargetRing R E S e :=
  IsLocalization.lift
    (M := (SeparableTensorDiagonal.sourceIdeal (ResidueField R) E
      (tensorResidue R E f)).primeCompl)
    (g := (tensorTarget R E S e g).toRingHom)
    (tensorTarget_denominator_unit R E S e f g hfg)

/-- The extension retains the original actual tensor map. -/
@[simp] theorem centreTargetMap_algebraMap (x : B ⊗[R] Ring R E) :
    centreTargetMap R E S e f g hfg
      (algebraMap (B ⊗[R] Ring R E) (CentreRing R E f) x) =
    tensorTarget R E S e g x :=
  IsLocalization.lift_eq _ x

/-- The source and target centres agree under the extended map. -/
instance centreTargetMap_isLocalHom :
    IsLocalHom (centreTargetMap R E S e f g hfg) := by
  have hm : maximalIdeal (CentreRing R E f) ≤
      (maximalIdeal (TargetRing R E S e)).comap (centreTargetMap R E S e f g hfg) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
      (SeparableTensorDiagonal.sourceIdeal (ResidueField R) E (tensorResidue R E f))
      (CentreRing R E f)]
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change centreTargetMap R E S e f g hfg
      (algebraMap (B ⊗[R] Ring R E) (CentreRing R E f) a) ∈
      maximalIdeal (TargetRing R E S e)
    rw [centreTargetMap_algebraMap]
    apply (residue_eq_zero_iff _).mp
    rw [← tensorTarget_residue_kernel R E S e f g hfg] at ha
    exact ha
  refine ⟨fun x hx => ?_⟩
  by_contra hn
  exact (hm hn) hx

/-- Original pure tensors retain the literal coefficient square after localization. -/
theorem centreTargetMap_tmul (b : B) (a : Ring R E) :
    centreTargetMap R E S e f g hfg
      (algebraMap (B ⊗[R] Ring R E) (CentreRing R E f) (b ⊗ₜ[R] a)) =
    algebraMap S (TargetRing R E S e) (g b) * targetMap R E S e a := by
  rw [centreTargetMap_algebraMap, tensorTarget_tmul]

end SeparableResidueExtension
