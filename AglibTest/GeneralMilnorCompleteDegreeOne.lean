/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.CompleteDegreeOne

/-!
# Degree-one base-case consumers

The complete consumer starts from the original complete DVR and the actual
finite extension. All structures on its literal integral closure are derived.
-/

@[expose] public noncomputable section

namespace AglibTest.GeneralMilnorCompleteDegreeOne

open IsLocalRing MilnorK IsDiscreteValuationRing.CompleteExtension

variable (R F E : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [FiniteDimensional F E]

/-- The degree-one norm square on the actual closure, with no extension-ring
structure supplied and only residue characteristic zero assumed. -/
theorem actual_complete_degree_one (hd : Module.finrank F E = 1)
    (n : ℕ) (x : K E (n + 1)) :
    let _ : CharZero R := RingHom.charZero (IsLocalRing.residue R)
    let _ : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective R F)
    let _ := integralClosure_isDiscreteValuationRing R F E
    let _ := integralClosure_isLocalHom R F E
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F E (integralClosure R E)
    let _ := IsIntegralClosure.finite R F E (integralClosure R E)
    DVR.residue R F n (finiteExtensionNorm F E (n + 1) x) =
      finiteExtensionNorm (ResidueField R) (ResidueField (integralClosure R E)) n
        (DVR.residue (integralClosure R E) E n x) := by
  dsimp only
  let _ : CharZero R := RingHom.charZero (IsLocalRing.residue R)
  let _ : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective R F)
  let _ := integralClosure_isDiscreteValuationRing R F E
  let _ := integralClosure_isLocalHom R F E
  let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F E (integralClosure R E)
  let _ := IsIntegralClosure.finite R F E (integralClosure R E)
  exact residue_finiteExtensionNorm_complete_degree_one R F E (integralClosure R E) hd n x

open Lean in
run_cmd do
  for name in #[``MilnorK.finiteExtensionNorm_self_apply,
      ``MilnorK.residue_finiteExtensionNorm_complete_degree_one,
      ``actual_complete_degree_one] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "The actual degree-one complete-DVR square uses only standard foundations."

end AglibTest.GeneralMilnorCompleteDegreeOne
