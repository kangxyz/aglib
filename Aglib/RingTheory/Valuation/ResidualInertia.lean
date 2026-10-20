/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Valuation.ResidualGalois
public import Aglib.RingTheory.IntegralClosure.Inertia

/-!
Identification of the original integral-closure inertia with the kernel of the
already constructed actual residual Galois map. The prime is the maximal ideal
of the actual spectral valuation ring, transported through the literal integral
closure equivalence. At a number-field completion this is also the existing
integralClosure.Inertia.chosenPrime: completeness gives a local integral closure.
-/

/-!
Extraction source: `R5Lab.Aglib.RingTheory.Valuation.ResidualInertia`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`1427eac743e6e7dc45a70babf7ea5b1c074d417e2292ffac2b5f4d766f2ca31e`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section

namespace Valuation.ResidualGalois

open Valuation.ResidualGalois
open Field.absoluteGaloisGroup.RootsOfUnity

universe u
variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] (V : ValuationSubring K)
  [Fact (∀ x : K, x ∈ V ↔ ‖x‖₊ ≤ 1)]

/-- The prime comes from the actual spectral norm extending the completion norm.
Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
def valuationPrime : Ideal (integralClosure.Inertia.IntegralModel V K) :=
  (IsLocalRing.maximalIdeal (ClosureIntegers K)).comap
    (integralClosureEquiv K V).toRingHom

local instance integralClosureLocal : IsLocalRing (integralClosure.Inertia.IntegralModel V K) :=
  (integralClosureEquiv K V).symm.toRingEquiv.isLocalRing

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
theorem valuationPrime_isMaximal : (valuationPrime K V).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective (integralClosureEquiv K V).toRingHom
    (integralClosureEquiv K V).surjective

/-- There is only one maximal ideal on the same integral closure.
Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
theorem maximal_eq_valuationPrime (Q : Ideal (integralClosure.Inertia.IntegralModel V K))
    [Q.IsMaximal] : Q = valuationPrime K V :=
  (IsLocalRing.eq_maximalIdeal (inferInstance : Q.IsMaximal)).trans
    (IsLocalRing.eq_maximalIdeal (valuationPrime_isMaximal K V)).symm

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
theorem integralClosureEquiv_smul (g : Field.absoluteGaloisGroup K)
    (x : integralClosure.Inertia.IntegralModel V K) :
    integralClosureEquiv K V (g • x) = integerAut K V g (integralClosureEquiv K V x) := by
  apply Subtype.ext
  change (integralClosureEquiv K V (g • x) : AlgebraicClosure K) =
    AlgEquiv.toAlgHom g (integralClosureEquiv K V x : AlgebraicClosure K)
  rw [integralClosureEquiv_coe, integralClosureEquiv_coe]
  rfl

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
theorem closureReduction_eq_zero_iff (x : ClosureIntegers K) :
    closureReduction K V x = 0 ↔ x ∈ IsLocalRing.maximalIdeal (ClosureIntegers K) := by
  change residueClosureEquiv K V (IsLocalRing.residue (ClosureIntegers K) x) = 0 ↔ _
  constructor
  · intro h
    apply (IsLocalRing.residue_eq_zero_iff x).mp
    apply (residueClosureEquiv K V).injective
    simpa only [map_zero] using h
  · intro h
    rw [(IsLocalRing.residue_eq_zero_iff x).mpr h, map_zero]

/-- Exact inertia membership uses actual reduction of each same integral element.
Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
theorem residualKernel_iff_inertia (g : Field.absoluteGaloisGroup K) :
    absoluteResidue K V g = 1 ↔ g ∈ integralClosure.Inertia.inertia V K (valuationPrime K V) := by
  rw [integralClosure.Inertia.mem_inertia_iff]
  constructor
  · intro hg x
    change integralClosureEquiv K V (g • x - x) ∈
      IsLocalRing.maximalIdeal (ClosureIntegers K)
    rw [← closureReduction_eq_zero_iff K V, _root_.map_sub, _root_.map_sub, sub_eq_zero,
      integralClosureEquiv_smul]
    have hs : AlgEquiv.toAlgHom (absoluteResidue K V g)
        (closureReduction K V (integralClosureEquiv K V x)) =
        closureReduction K V (integerAut K V g (integralClosureEquiv K V x)) :=
      absoluteResidueHom_residue K V g (integralClosureEquiv K V x)
    rw [hg] at hs
    exact hs.symm
  · intro hg
    apply AlgEquiv.ext
    intro z
    obtain ⟨a, rfl⟩ := closureReduction_surjective K V z
    obtain ⟨x, rfl⟩ := (integralClosureEquiv K V).surjective a
    have hx := hg x
    change integralClosureEquiv K V (g • x - x) ∈
      IsLocalRing.maximalIdeal (ClosureIntegers K) at hx
    rw [← closureReduction_eq_zero_iff K V, _root_.map_sub, _root_.map_sub, sub_eq_zero,
      integralClosureEquiv_smul] at hx
    change AlgEquiv.toAlgHom (absoluteResidue K V g)
      (closureReduction K V (integralClosureEquiv K V x)) =
      closureReduction K V (integralClosureEquiv K V x)
    exact (absoluteResidueHom_residue K V g (integralClosureEquiv K V x)).trans hx

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
theorem inertia_eq_residualKernel :
    integralClosure.Inertia.inertia V K (valuationPrime K V) =
      (absoluteResidue K V).toMonoidHom.ker := by
  ext g
  exact (residualKernel_iff_inertia K V g).symm

end Valuation.ResidualGalois
