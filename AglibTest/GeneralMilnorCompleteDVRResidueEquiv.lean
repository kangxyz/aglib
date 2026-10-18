/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.CompleteDVRResidueEquiv

/-!
# Consumers of actual integral-closure residue transport

The complete consumer assumes residue characteristic zero and derives the
fraction-field characteristic, separability, and both actual DVR structures.
A second consumer tests transport between arbitrary actual integral-closure
models in one field, as needed when iterating along a tower.
-/

@[expose] public noncomputable section

namespace AglibTest.GeneralMilnorCompleteDVRResidueEquiv

open IsLocalRing MilnorK IsDiscreteValuationRing.CompleteExtension
open MilnorK.CompleteDVRResidueEquiv

section Complete

variable (R F E L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
  [FiniteDimensional F E] [FiniteDimensional F L]

/-- No characteristic, separability, DVR, or fraction-ring assumptions on the
extension rings are supplied beyond the original complete base data. -/
theorem actual_complete_residue_square (ε : E ≃ₐ[F] L) (n : ℕ) (x : K E (n + 1)) :
    let _ : CharZero R := RingHom.charZero (IsLocalRing.residue R)
    let _ : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective R F)
    let _ := integralClosure_isDiscreteValuationRing R F E
    let _ := integralClosure_isDiscreteValuationRing R F L
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F E (integralClosure R E)
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F L (integralClosure R L)
    map n (residueEquiv R F ε).toRingHom (DVR.residue (integralClosure R E) E n x) =
      DVR.residue (integralClosure R L) L n (map (n + 1) ε.toRingHom x) := by
  dsimp only
  let _ : CharZero R := RingHom.charZero (IsLocalRing.residue R)
  let _ : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective R F)
  let _ := integralClosure_isDiscreteValuationRing R F E
  let _ := integralClosure_isDiscreteValuationRing R F L
  let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F E (integralClosure R E)
  let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F L (integralClosure R L)
  exact LinearMap.congr_fun (residue_naturality_complete R F ε n) x

end Complete

section Models

variable (R E S T : Type*) [CommRing R] [Field E] [Algebra R E]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Algebra R S] [Algebra S E] [IsScalarTower R S E]
  [Algebra R T] [Algebra T E] [IsScalarTower R T E]
  [IsIntegralClosure S R E] [IsIntegralClosure T R E]
  [IsFractionRing S E] [IsFractionRing T E]

/-- Model transport fixes the actual fraction field, rather than replacing it. -/
theorem actual_model_residue_square (n : ℕ) (x : K E (n + 1)) :
    map n (ResidueField.mapEquiv (IsIntegralClosure.equiv R S E T).toRingEquiv).toRingHom
        (DVR.residue S E n x) = DVR.residue T E n x := by
  have h := DVR.residue_equiv_apply (IsIntegralClosure.equiv R S E T).toRingEquiv
    (RingEquiv.refl E) (fun s => (IsIntegralClosure.algebraMap_equiv R S E T s).symm) n x
  simpa only [show (RingEquiv.refl E).toRingHom = RingHom.id E from rfl,
    map_id, LinearMap.id_apply] using h

end Models

open Lean in
run_cmd do
  for name in #[``MilnorK.DVR.residue_equiv,
      ``MilnorK.DVR.residue_equiv_apply,
      ``MilnorK.CompleteDVRResidueEquiv.closureEquiv,
      ``MilnorK.CompleteDVRResidueEquiv.closureEquiv_apply,
      ``MilnorK.CompleteDVRResidueEquiv.residueEquiv,
      ``MilnorK.CompleteDVRResidueEquiv.residueEquiv_residue,
      ``MilnorK.CompleteDVRResidueEquiv.residueAlgEquiv,
      ``MilnorK.CompleteDVRResidueEquiv.residueAlgEquiv_toRingEquiv,
      ``MilnorK.CompleteDVRResidueEquiv.residue_naturality,
      ``MilnorK.CompleteDVRResidueEquiv.residue_naturality_apply,
      ``MilnorK.CompleteDVRResidueEquiv.residue_naturality_complete,
      ``actual_complete_residue_square, ``actual_model_residue_square] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual complete-DVR residue equivalences use only standard foundations."

end AglibTest.GeneralMilnorCompleteDVRResidueEquiv
