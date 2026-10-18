/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Dedekind.AffineEndpointNormEquality
public import Aglib.RingTheory.FiniteTypeLocalResidue

/-! # Endpoint branch norms are the actual base-field residue norms -/

@[expose] public noncomputable section
namespace MilnorK.DedekindResidue

open Polynomial PolynomialResidue PolynomialDedekindResidue IsLocalRing IsDedekindDomain
attribute [local instance] Classical.decEq polynomialPointResidueCharZero

universe u
variable (k S : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S] [Algebra k S] [IsScalarTower k k[X] S]

local instance (a : k) : Fact (Irreducible (X - C a)) := ⟨irreducible_X_sub_C a⟩

local instance finiteType : Algebra.FiniteType k S := Algebra.FiniteType.trans (S := k[X])
  (inferInstanceAs (Algebra.FiniteType k k[X]))
  (inferInstanceAs (Algebra.FiniteType k[X] S))

local instance localResidueFinite (q : HeightOneSpectrum S) :
    FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal)) :=
  Localization.finiteType_localResidue_finite k S q.asIdeal

/-- This is the literal composite of the two actual linear-place residue identifications. -/
def endpointResidueEquiv (a : k) :
    ResidueField (Localization.AtPrime (point (endpointPolynomial k a)).asIdeal) ≃ₐ[k] k :=
  (Polynomial.LocalResidue.residueEquiv (endpointPolynomial k a).val).trans (linearRootEquiv a)

/-- Each original branch norm, after the actual endpoint identification, is
precisely the residue-field norm to the original ground field. -/
theorem endpoint_branchNorm_eq (a : k) (n : ℕ)
    (q : AdicCompletion.IdealBranch
      ((point (endpointPolynomial k a)).asIdeal.map (algebraMap k[X] S)))
    (x : K (ResidueField (Localization.AtPrime
      (branchPoint k[X] S (point (endpointPolynomial k a)) q).asIdeal)) n) :
    MilnorK.map n (endpointResidueEquiv k a).toRingHom
      (branchCoordinateNorm k[X] S (point (endpointPolynomial k a)) n q x) =
        finiteExtensionNorm k (ResidueField (Localization.AtPrime
          (branchPoint k[X] S (point (endpointPolynomial k a)) q).asIdeal)) n x := by
  let p := point (endpointPolynomial k a)
  let := Localization.basePrimeLocalAlgebra p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let := Localization.basePrimeLocalTower p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let := Localization.basePrimeLocal_isLocalHom p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let := Localization.basePrimeLocal_residueFinite p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let : IsScalarTower k (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.val) := by
    apply IsScalarTower.of_algebraMap_eq
    intro c
    rw [IsScalarTower.algebraMap_apply k k[X] (Localization.AtPrime p.asIdeal),
      ← IsScalarTower.algebraMap_apply k[X] (Localization.AtPrime p.asIdeal),
      ← IsScalarTower.algebraMap_apply k k[X]]
  let : FiniteDimensional k (ResidueField (Localization.AtPrime q.val)) :=
    localResidueFinite k S (branchPoint k[X] S p q)
  have hs (c : ResidueField (Localization.AtPrime p.asIdeal)) :
      (RingEquiv.refl (ResidueField (Localization.AtPrime q.val)))
          (algebraMap (ResidueField (Localization.AtPrime p.asIdeal))
            (ResidueField (Localization.AtPrime q.val)) c) =
        algebraMap k (ResidueField (Localization.AtPrime q.val))
          (endpointResidueEquiv k a c) := by
    have hc : algebraMap k (ResidueField (Localization.AtPrime p.asIdeal))
        (endpointResidueEquiv k a c) = c := by
      exact ((endpointResidueEquiv k a).symm.commutes _).symm.trans
        ((endpointResidueEquiv k a).symm_apply_apply c)
    rw [IsScalarTower.algebraMap_apply k (ResidueField (Localization.AtPrime p.asIdeal)), hc]
    rfl
  let : CharZero (ResidueField (Localization.AtPrime p.asIdeal)) :=
    polynomialPointResidueCharZero k p
  have h := finiteExtensionNorm_equiv (endpointResidueEquiv k a).toRingEquiv
    (RingEquiv.refl (ResidueField (Localization.AtPrime q.val))) hs n x
  have hid : (RingEquiv.refl (ResidueField (Localization.AtPrime q.val))).toRingHom =
      RingHom.id _ := rfl
  simp only [hid, MilnorK.map_id] at h
  dsimp only [branchCoordinateNorm]
  exact h

variable (E : Type u) [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

omit [Algebra k[X] E] [IsScalarTower k[X] S E]
  [IsScalarTower k[X] (RatFunc k) E] [FiniteDimensional (RatFunc k) E] in
/-- The full original endpoint sum has actual ground-field norms term by term;
no abstractly isomorphic residue fields or branch multiplicities are substituted. -/
theorem endpointWeightedResidueSum_eq_baseNormSum (a : k) (n : ℕ) (u : Fin n → Sˣ) :
    endpointWeightedResidueSum k S E a n u =
      ∑ q : AdicCompletion.IdealBranch
          ((point (endpointPolynomial k a)).asIdeal.map (algebraMap k[X] S)),
        let Q := branchPoint k[X] S (point (endpointPolynomial k a)) q
        MilnorK.K2.DVR.value (Localization.AtPrime Q.asIdeal) E
          (Additive.ofMul (endpointParameter k E a)) •
          finiteExtensionNorm k (ResidueField (Localization.AtPrime Q.asIdeal)) n
            (symbol (Units.map ((IsLocalRing.residue (Localization.AtPrime Q.asIdeal)).comp
              (algebraMap S (Localization.AtPrime Q.asIdeal))).toMonoidHom ∘ u)) := by
  unfold endpointWeightedResidueSum
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [← LinearMap.comp_apply, ← MilnorK.map_comp]
  change MilnorK.map n (endpointResidueEquiv k a).toRingHom _ = _
  rw [endpoint_branchNorm_eq, map_smul]

end MilnorK.DedekindResidue
