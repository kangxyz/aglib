/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootScalarBranches
public import Aglib.KTheory.MilnorK.K3.ResidueBaseChangeSupport
public import Lean.Util.CollectAxioms

/-!
# Consumers of literal scalar-extended polynomial branches

These consumers use the original finite `placesAbove` set, not an alternative
branch index. They check completeness of this set, local multiplicity one,
scalar-compatible maximal quotient fields, and the exact map from the original
AdjoinRoot field through the whole scalar tensor algebra to each branch.
-/

@[expose] public noncomputable section

open Polynomial AdjoinRoot
open MilnorK.K3.PolynomialResidue
open scoped TensorProduct

namespace AglibTest.AdjoinRootScalarBranches

variable {k L : Type*} [Field k] [Field L]

/-- The already existing finite target-place set is exactly the full maximal
spectrum of the whole scalar-extended quotient algebra. -/
def placesAboveEquivMaximal (φ : k →+* L) (p : MonicIrreducible k) :
    {q // q ∈ placesAbove φ p} ≃ MaximalSpectrum (AdjoinRoot (p.val.map φ)) :=
  (Equiv.subtypeEquivRight (fun q => mem_placesAbove φ p q)).trans
    (branchEquivMaximal _ (Polynomial.map_ne_zero p.property.2.ne_zero))

/-- No maximal quotient is omitted by the original residue support. -/
theorem every_maximal_is_original_place (φ : k →+* L) (p : MonicIrreducible k)
    (m : MaximalSpectrum (AdjoinRoot (p.val.map φ))) :
    ∃ q : {q // q ∈ placesAbove φ p}, placesAboveEquivMaximal φ p q = m :=
  (placesAboveEquivMaximal φ p).surjective m

/-- The coefficients occurring in the actual fundamental-cycle formula are
one after characteristic-zero scalar extension. -/
theorem original_local_multiplicity_one [CharZero k]
    (φ : k →+* L) (p : MonicIrreducible k)
    (m : MaximalSpectrum (AdjoinRoot (p.val.map φ))) :
    (Module.length (Localization.AtPrime m.asIdeal)
      (Localization.AtPrime m.asIdeal)).toNat = 1 := by
  rw [scalar_local_length_eq_one φ p.val p.property.1, ENat.toNat_one]

/-- The literal quotient-field equivalence preserves the residual polynomial
coordinate, before taking norms, cycles, or motivic classes. -/
theorem quotient_root_is_original_root (p : L[X]) (q : IrreducibleBranch p) :
    branchQuotientAlgEquiv p q
      (Ideal.Quotient.mk (branchMaximal p q).asIdeal (root p)) = root q.val.val := by
  change branchQuotientEquiv p q
    (Ideal.Quotient.mk (branchMaximal p q).asIdeal (mk p X)) = mk q.val.val X
  rw [branchQuotientEquiv_mk, divisorMap_mk]

/-- The old field maps through the literal tensor-product scalar extension,
then the branch quotient, by exactly the existing residue-field map. -/
theorem tensor_branch_is_original_residue_map [Algebra k L]
    (p : MonicIrreducible k) (q : MonicIrreducible L)
    (hq : q.val ∣ p.val.map (algebraMap k L)) :
    (divisorMap (p.val.map (algebraMap k L)) q.val hq).comp
      ((scalarExtensionEquiv (L := L) p.val).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom) =
      Polynomial.LocalResidue.adjoinRootMap (algebraMap k L) p.val q.val hq := by
  rw [scalarExtensionEquiv_comp_includeRight, divisorMap_comp_scalarMap]

/-- The other tensor-product map is precisely the original target scalar map. -/
theorem tensor_preserves_target_scalars [Algebra k L] (p : k[X]) (a : L) :
    scalarExtensionEquiv (L := L) p
      (algebraMap L (L ⊗[k] AdjoinRoot p) a) =
      algebraMap L (AdjoinRoot (p.map (algebraMap k L))) a :=
  (scalarExtensionEquiv (L := L) p).commutes a

open Lean in
run_cmd do
  for name in #[``AdjoinRoot.branchMaximal_injective,
      ``AdjoinRoot.branchMaximal_surjective, ``AdjoinRoot.branchEquivMaximal,
      ``AdjoinRoot.branchQuotientAlgEquiv, ``AdjoinRoot.isReduced_of_squarefree,
      ``AdjoinRoot.local_length_eq_one_of_squarefree, ``AdjoinRoot.scalar_local_length_eq_one,
      ``AdjoinRoot.divisorMap_comp_scalarMap, ``AdjoinRoot.scalarExtensionEquiv,
      ``AdjoinRoot.scalarExtensionEquiv_comp_includeRight, ``placesAboveEquivMaximal,
      ``every_maximal_is_original_place, ``original_local_multiplicity_one,
      ``quotient_root_is_original_root, ``tensor_branch_is_original_residue_map,
      ``tensor_preserves_target_scalars] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Literal scalar-extension branches use only standard Lean foundations."

end AglibTest.AdjoinRootScalarBranches
