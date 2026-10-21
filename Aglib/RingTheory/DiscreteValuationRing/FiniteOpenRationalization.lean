/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.TensorOpenTargetPoint

/-! # Actual finite-open rationalization of the original centre

This bundles only previously constructed maps. Finite generation, the rational
point, its kernel, and its compatibility with the target are proved outputs.
-/

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

/-- The base DVR acts on the rational residue field through its specified residue extension. -/
local instance finiteOpenRationalizationResidueAlgebra : Algebra R E :=
  ((algebraMap (ResidueField R) E).comp (residue R)).toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {B : Type*} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
  (f : B →ₐ[R] E) (g : B →ₐ[R] S)

/-- The constructed finite principal open has the actual rational residue point,
precisely the extended original centre as kernel, and the actual compatible target point. -/
theorem exists_finite_open_rationalization (hf : Function.Surjective f)
    (hfg : ∀ b, residue S (g b) = e (f b)) :
    ∃ (s : B ⊗[R] Ring R E)
      (hs : s ∉ SeparableTensorDiagonal.sourceIdeal (ResidueField R) E (tensorResidue R E f)),
      Algebra.FiniteType (Ring R E) (Localization.Away s) ∧
      Function.Surjective (openRationalPoint R E f s hs) ∧
      RingHom.ker (openRationalPoint R E f s hs).toRingHom =
        ((RingHom.ker f.toRingHom).map
          (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Ring R E)).map
            (algebraMap (B ⊗[R] Ring R E) (Localization.Away s)) ∧
      ∀ x : Localization.Away s,
        residue (TargetRing R E S e) (openTargetPoint R E S e f g s hs hfg x) =
          ResidueField.map (targetMap R E S e).toRingHom
            (openRationalPoint R E f s hs x) := by
  obtain ⟨s, hs, hIJ⟩ := exists_tensor_centre_open R E f hf
  refine ⟨s, hs, tensor_away_finiteType R E s,
    openRationalPoint_surjective R E f s hs hf, ?_, ?_⟩
  · exact (ker_openRationalPoint R E f s hs).trans hIJ.symm
  · exact openTargetPoint_residue R E S e f g s hs hfg

end SeparableResidueExtension
