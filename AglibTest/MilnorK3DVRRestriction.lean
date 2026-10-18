/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.DVRRestriction
public import Lean.Util.CollectAxioms

/-! # Consumers of actual unramified DVR restriction -/

@[expose] public noncomputable section

namespace AglibTest.MilnorK3DVRRestriction

open MilnorK.K2 MilnorK.K3

variable {R S K L : Type*}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L]
  (j : R →+* S) [IsLocalHom j] (F : K →+* L)
  (hF : ∀ r : R, F (algebraMap R K r) = algebraMap S L (j r))

include hF

omit [IsLocalHom j] in
/-- Integer-order compatibility is a conclusion from structural ring maps. -/
theorem original_order_is_preserved {π : R} (hπ : Irreducible π)
    (hjπ : Irreducible (j π)) (a : Kˣ) :
    MilnorK.K2.DVR.value S L
        (Additive.ofMul (Units.map F.toMonoidHom a)) =
      MilnorK.K2.DVR.value R K (Additive.ofMul a) :=
  MilnorK.K3.DVR.value_map j F hF hπ hjπ (Additive.ofMul a)

/-- Every original K₃ quotient class satisfies the actual residue square. -/
theorem original_residue_commutes {π : R} (hπ : Irreducible π)
    (hjπ : Irreducible (j π)) (x : MilnorK.K3.Group K) :
    MilnorK.K2.map (IsLocalRing.ResidueField.map j)
        (MilnorK.K3.DVR.residue R K x) =
      MilnorK.K3.DVR.residue S L (MilnorK.K3.map F x) :=
  LinearMap.congr_fun
    (MilnorK.K3.DVR.residue_restrict j F hF hπ hjπ) x

/-- The target angular component is obtained using the actual residue-field map. -/
theorem original_unit_reduction_commutes {π : R} (hπ : Irreducible π)
    (hjπ : Irreducible (j π)) (a : Kˣ) :
    MilnorK.K2.DVR.unitResidue (K := L) hjπ (Units.map F.toMonoidHom a) =
      Units.map (IsLocalRing.ResidueField.map j).toMonoidHom
        (MilnorK.K2.DVR.unitResidue (K := K) hπ a) :=
  MilnorK.K3.DVR.unitResidue_map j F hF hπ hjπ a

open Lean in
run_cmd do
  for name in #[``MilnorK.K3.DVR.residueFieldMap,
      ``MilnorK.K3.DVR.residueFieldMap_residue,
      ``MilnorK.K3.DVR.fieldUnits_map,
      ``MilnorK.K3.DVR.uniformizer_map,
      ``MilnorK.K3.DVR.mapped_normalizedLift_spec,
      ``MilnorK.K3.DVR.value_map,
      ``MilnorK.K3.DVR.normalizedLift_map,
      ``MilnorK.K3.DVR.unitResidue_map,
      ``MilnorK.K3.DVR.unitPart_map,
      ``MilnorK.K3.DVR.residue_restrict,
      ``original_order_is_preserved, ``original_residue_commutes,
      ``original_unit_reduction_commutes] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual unramified DVR restriction uses only standard Lean logical foundations."

end AglibTest.MilnorK3DVRRestriction
