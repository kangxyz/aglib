/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Dedekind.AffineUnramifiedNorm
public import Aglib.KTheory.MilnorK.Residue.Product

/-! # Actual local orders of global coordinate-unit symbols -/

@[expose] public noncomputable section
namespace MilnorK

namespace DVR
variable (R E : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field E] [Algebra R E] [IsFractionRing R E]

/-- An arbitrary last parameter contributes its actual normalized integer order;
the original preceding coordinates are reduced as ring units. -/
theorem residue_ring_units_last (n : ℕ) (a : Fin n → Rˣ) (b : Eˣ) :
    residue R E n (symbol (Fin.snoc (MilnorK.K2.DVR.fieldUnits R E ∘ a) b)) =
      MilnorK.K2.DVR.value R E (Additive.ofMul b) •
        symbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a) := by
  have h := residue_symbol_snoc_units (MilnorK.K2.DVR.chosenData R E)
    (MilnorK.K2.DVR.chosenData_unitReductionCompatible R E) n
    (MilnorK.K2.DVR.fieldUnits R E ∘ a)
    (fun i => MilnorK.K2.DVR.value_fieldUnits R E (a i)) b
  change residue R E n _ = _ at h
  refine h.trans ?_
  congr 1
  exact specialize_ring_units R E n a
end DVR

namespace DedekindResidue
open IsDedekindDomain IsLocalRing
variable (S E : Type*) [CommRing S] [IsDedekindDomain S]
  [Field E] [Algebra S E] [IsFractionRing S E]

/-- The local contribution of a global affine coordinate tuple and an arbitrary
function uses the unchanged original fraction field and literal residue map. -/
theorem residue_ring_units_last (q : HeightOneSpectrum S) (n : ℕ)
    (a : Fin n → Sˣ) (b : Eˣ) :
    DVR.residue (Localization.AtPrime q.asIdeal) E n
      (symbol (Fin.snoc (Units.map (algebraMap S E).toMonoidHom ∘ a) b)) =
      MilnorK.K2.DVR.value (Localization.AtPrime q.asIdeal) E (Additive.ofMul b) •
        symbol (Units.map ((IsLocalRing.residue (Localization.AtPrime q.asIdeal)).comp
          (algebraMap S (Localization.AtPrime q.asIdeal))).toMonoidHom ∘ a) := by
  have h := DVR.residue_ring_units_last (Localization.AtPrime q.asIdeal) E n
    (Units.map (algebraMap S (Localization.AtPrime q.asIdeal)).toMonoidHom ∘ a) b
  convert h using 2
  · apply congrArg symbol
    congr 1
    funext i
    apply Units.ext
    exact IsScalarTower.algebraMap_apply S (Localization.AtPrime q.asIdeal) E (a i)
  · rfl

end DedekindResidue
end MilnorK
