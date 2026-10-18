/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.One
public import Aglib.KTheory.MilnorK.Residue.RamifiedRestriction
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# The actual Galois trace of a polynomial norm and its tame residue

Split polynomial base change gives the trace over the actual field automorphisms.
Each automorphism restricts to the integral closure and hence to its residue field.
Ramified restriction then identifies the residue of this trace on every Milnor
class. No norm on the residue extension and no norm-residue or tower law is assumed.
The missing next step is the inertia-fiber count comparing this trace with the
residue-field norm trace; the present result alone is not norm-residue compatibility.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue

variable {F : Type*} [Field F] [CharZero F]

local instance (p : MonicIrreducible F) : Module.Finite F (AdjoinRoot p.val) :=
  p.property.1.finite_adjoinRoot

open Classical in
/-- Splitting base change is the sum of the actual Galois automorphisms, without
using presentation independence or a tower law. -/
theorem polynomialNorm_restrict_eq_sum_galois (n : ℕ) (p : MonicIrreducible F)
    [Normal F (AdjoinRoot p.val)] (x : K (AdjoinRoot p.val) n) :
    map n (algebraMap F (AdjoinRoot p.val)) (polynomialNorm n p x) =
      ∑ σ : Gal(AdjoinRoot p.val/F), map n σ.toRingHom x := by
  classical
  have hp : (p.val.map (algebraMap F (AdjoinRoot p.val))).Splits := by
    have hmin : p.val = minpoly F (AdjoinRoot.root p.val) :=
      minpoly.eq_of_irreducible_of_monic p.property.2
        (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]) p.property.1
    exact (congrArg (fun f : F[X] =>
      (f.map (algebraMap F (AdjoinRoot p.val))).Splits) hmin).mpr
        (Normal.splits (inferInstance : Normal F (AdjoinRoot p.val)) _)
  let B := (Equiv.ofBijective (splitBranchAlgHom p hp)
    ⟨splitBranchAlgHom_injective p hp, splitBranchAlgHom_surjective p hp⟩).trans
    (Normal.algHomEquivAut F (AdjoinRoot p.val) (AdjoinRoot p.val))
  rw [polynomialNorm_restrict_of_splits (algebraMap F (AdjoinRoot p.val)) n p hp]
  simp only [Finset.attach_eq_univ]
  apply Fintype.sum_equiv B
  intro q
  have h : (B q).toAlgHom = splitBranchAlgHom p hp q := by
    change ((splitBranchAlgHom p hp q).restrictNormal' (AdjoinRoot p.val)).toAlgHom = _
    apply AlgHom.ext
    intro a
    have hh := congrArg (fun f : AdjoinRoot p.val →ₐ[F] AdjoinRoot p.val => f a)
      ((Normal.algHomEquivAut F (AdjoinRoot p.val) (AdjoinRoot p.val)).symm_apply_apply
        (splitBranchAlgHom p hp q))
    simpa [Normal.algHomEquivAut] using hh
  exact congrArg (fun f : AdjoinRoot p.val →+* AdjoinRoot p.val => map n f x)
    (congrArg AlgHom.toRingHom h).symm

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R F] [IsFractionRing R F]
  (p : MonicIrreducible F)
  (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Algebra S (AdjoinRoot p.val)]
  [IsScalarTower R S (AdjoinRoot p.val)]
  [IsFractionRing S (AdjoinRoot p.val)] [IsIntegralClosure S R (AdjoinRoot p.val)]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- Actual integral-closure automorphisms commute with tame residues in every
Milnor degree; their residue maps are the native local-ring quotient maps. -/
theorem residue_map_galRestrict (n : ℕ) (σ : Gal(AdjoinRoot p.val/F))
    (x : K (AdjoinRoot p.val) (n + 1)) :
    DVR.residue S (AdjoinRoot p.val) n (map (n + 1) σ.toRingHom x) =
      map n (IsLocalRing.ResidueField.mapEquiv
        (galRestrict R F (AdjoinRoot p.val) S σ).toRingEquiv).toRingHom
        (DVR.residue S (AdjoinRoot p.val) n x) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  let τ := galRestrict R F (AdjoinRoot p.val) S σ
  let : IsLocalHom τ.toRingHom := ⟨fun a ha => (MulEquiv.isUnit_map τ).mp ha⟩
  exact (DVR.residue_restrict_apply τ.toRingHom σ.toRingHom
    (fun s => (algebraMap_galRestrict_apply R σ s).symm)
    hϖ (hϖ.map τ.toMulEquiv) n x).symm

open Classical in
/-- The all-class ramified trace identity. The exponent is the literal exponent
in the uniformizer equation, and all summands use actual induced residue maps.
No residue-extension norm or compatibility premise occurs in the statement. -/
theorem residue_polynomialNorm_galois_trace
    [Normal F (AdjoinRoot p.val)] [IsLocalHom (algebraMap R S)]
    (n : ℕ) (x : K (AdjoinRoot p.val) (n + 1))
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) :
    (e : ℤ) • map n (IsLocalRing.ResidueField.map (algebraMap R S))
        (DVR.residue R F n (polynomialNorm (n + 1) p x)) =
      ∑ σ : Gal(AdjoinRoot p.val/F),
        map n (IsLocalRing.ResidueField.mapEquiv
          (galRestrict R F (AdjoinRoot p.val) S σ).toRingEquiv).toRingHom
          (DVR.residue S (AdjoinRoot p.val) n x) := by
  rw [← DVR.residue_ramified_restrict_apply (algebraMap R S)
    (algebraMap F (AdjoinRoot p.val))
    (fun r => by simp only [← IsScalarTower.algebraMap_apply]) hπ hϖ u e he]
  rw [polynomialNorm_restrict_eq_sum_galois, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact residue_map_galRestrict R p S n σ x

end MilnorK.PolynomialNorm
