/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.CompletePGroup
public import Aglib.RingTheory.AdjoinRootNestedBaseChange
public import Aglib.RingTheory.CompleteDVRIntegralClosureTower

/-!
# Actual complete-DVR diagrams for every scalar branch

The coefficient polynomial may split into any number of branches. Each old-root
map is the original `adjoinRootMap`; both upper ring maps are its literal
restrictions to integral closures. The upper DVR remains the closure of the
original base, also when it is viewed over the coefficient DVR.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm.CompleteScalarBranch

open Polynomial Polynomial.LocalResidue PolynomialResidue IsLocalRing AdjoinRoot
open IsDiscreteValuationRing.CompleteExtension IsDiscreteValuationRing.IntegralClosureTower

universe u

attribute [local instance] AdjoinRoot.scalarBranchAlgebra closureAlgebra

section Maps

variable (R : Type*) {F L : Type*} [CommRing R] [Field F] [Field L]
  [Algebra F L] [Algebra R F] [Algebra R L] [IsScalarTower R F L]
  (p : MonicIrreducible F) (r : IrreducibleBranch (p.val.map (algebraMap F L)))

/-- The old-root action is exactly the quotient map for this coefficient branch. -/
theorem branch_algebraMap_eq :
    algebraMap (AdjoinRoot p.val) (AdjoinRoot r.val.val) =
      adjoinRootMap (algebraMap F L) p.val r.val.val r.property := rfl

/-- The original base ring commutes with the literal old-root branch map. -/
instance baseBranchTower : IsScalarTower R (AdjoinRoot p.val) (AdjoinRoot r.val.val) := by
  let : IsScalarTower F (AdjoinRoot p.val) (AdjoinRoot r.val.val) :=
    AdjoinRoot.scalarBranchBaseTower p.val r
  apply IsScalarTower.of_algebraMap_eq
  intro a
  rw [IsScalarTower.algebraMap_apply R F (AdjoinRoot p.val),
    ← IsScalarTower.algebraMap_apply F (AdjoinRoot p.val) (AdjoinRoot r.val.val),
    ← IsScalarTower.algebraMap_apply R F (AdjoinRoot r.val.val)]

/-- The actual integral-closure map has precisely the old-root quotient values. -/
theorem oldRoot_closureMap_apply (s : integralClosure R (AdjoinRoot p.val)) :
    algebraMap (integralClosure R (AdjoinRoot r.val.val)) (AdjoinRoot r.val.val)
      (algebraMap (integralClosure R (AdjoinRoot p.val))
        (integralClosure R (AdjoinRoot r.val.val)) s) =
      adjoinRootMap (algebraMap F L) p.val r.val.val r.property
        (algebraMap (integralClosure R (AdjoinRoot p.val)) (AdjoinRoot p.val) s) := rfl

omit [Algebra R F] [IsScalarTower R F L] in
/-- The coefficient map also remains the original field inclusion on integral elements. -/
theorem coefficient_closureMap_apply (t : integralClosure R L) :
    algebraMap (integralClosure R (AdjoinRoot r.val.val)) (AdjoinRoot r.val.val)
      (algebraMap (integralClosure R L) (integralClosure R (AdjoinRoot r.val.val)) t) =
      algebraMap L (AdjoinRoot r.val.val) (algebraMap (integralClosure R L) L t) := rfl

/-- No new upper ring is introduced over the old-root integral closure. -/
theorem oldRoot_isIntegralClosure :
    IsIntegralClosure (integralClosure R (AdjoinRoot r.val.val))
      (integralClosure R (AdjoinRoot p.val)) (AdjoinRoot r.val.val) :=
  upper_isIntegralClosure R (AdjoinRoot p.val) (AdjoinRoot r.val.val)

omit [Algebra R F] [IsScalarTower R F L] in
/-- No new upper ring is introduced over the coefficient integral closure. -/
theorem coefficient_isIntegralClosure :
    IsIntegralClosure (integralClosure R (AdjoinRoot r.val.val))
      (integralClosure R L) (AdjoinRoot r.val.val) :=
  upper_isIntegralClosure R L (AdjoinRoot r.val.val)

/-- The old-root ring map is local, without imposing unramifiedness. -/
theorem oldRoot_isLocalHom :
    IsLocalHom (algebraMap (integralClosure R (AdjoinRoot p.val))
      (integralClosure R (AdjoinRoot r.val.val))) :=
  upper_isLocalHom R (AdjoinRoot p.val) (AdjoinRoot r.val.val)

omit [Algebra R F] [IsScalarTower R F L] in
/-- The coefficient ring map is local, without imposing unramifiedness. -/
theorem coefficient_isLocalHom :
    IsLocalHom (algebraMap (integralClosure R L) (integralClosure R (AdjoinRoot r.val.val))) :=
  upper_isLocalHom R L (AdjoinRoot r.val.val)

end Maps

section Finiteness

variable (R F L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L] [FiniteDimensional F L]
  (p : MonicIrreducible F) (r : IrreducibleBranch (p.val.map (algebraMap F L)))

/-- Every scalar-branch integral closure is finite over the actual old-root closure. -/
theorem oldRoot_finite :
    Module.Finite (integralClosure R (AdjoinRoot p.val))
      (integralClosure R (AdjoinRoot r.val.val)) := by
  let : FiniteDimensional L (AdjoinRoot r.val.val) := r.val.property.1.finite_adjoinRoot
  let : FiniteDimensional F (AdjoinRoot r.val.val) := Module.Finite.trans L _
  exact upper_finite R F (AdjoinRoot p.val) (AdjoinRoot r.val.val)

/-- Every scalar-branch integral closure is finite over the actual coefficient closure. -/
theorem coefficient_finite :
    Module.Finite (integralClosure R L) (integralClosure R (AdjoinRoot r.val.val)) := by
  let : FiniteDimensional L (AdjoinRoot r.val.val) := r.val.property.1.finite_adjoinRoot
  let : FiniteDimensional F (AdjoinRoot r.val.val) := Module.Finite.trans L _
  exact upper_finite R F L (AdjoinRoot r.val.val)

end Finiteness

section Complete

variable (R F L : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
  [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L] [FiniteDimensional F L]
  (p : MonicIrreducible F) (r : IrreducibleBranch (p.val.map (algebraMap F L)))

/-- Every branch embedded in a Galois p-group ambient satisfies the actual
coefficient norm-residue square. All structures on both closure DVRs are derived. -/
theorem residue_finiteExtensionNorm_complete_scalarBranch_of_pGroup
    (Ω : Type u) [Field Ω] [Algebra L Ω] [FiniteDimensional L Ω] [IsGalois L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[L] Ω))
    (g : AdjoinRoot r.val.val →ₐ[L] Ω) (n : ℕ) (x : K (AdjoinRoot r.val.val) (n + 1)) :
    let _ : CharZero L := charZero_of_injective_algebraMap (algebraMap F L).injective
    let _ : FiniteDimensional L (AdjoinRoot r.val.val) := r.val.property.1.finite_adjoinRoot
    let _ : FiniteDimensional F (AdjoinRoot r.val.val) := Module.Finite.trans L _
    let _ := integralClosure_isDiscreteValuationRing R F L
    let _ := integralClosure_isDiscreteValuationRing R F (AdjoinRoot r.val.val)
    let _ := integralClosure_isLocalHom R F L
    let _ := coefficient_isLocalHom R p r
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F L (integralClosure R L)
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F (AdjoinRoot r.val.val)
      (integralClosure R (AdjoinRoot r.val.val))
    let _ := coefficient_finite R F L p r
    let _ : CharZero (ResidueField (integralClosure R L)) :=
      charZero_of_injective_algebraMap
        (algebraMap (ResidueField R) (ResidueField (integralClosure R L))).injective
    DVR.residue (integralClosure R L) L n
        (finiteExtensionNorm L (AdjoinRoot r.val.val) (n + 1) x) =
      finiteExtensionNorm (ResidueField (integralClosure R L))
        (ResidueField (integralClosure R (AdjoinRoot r.val.val))) n
        (DVR.residue (integralClosure R (AdjoinRoot r.val.val)) (AdjoinRoot r.val.val) n x) := by
  dsimp only
  let D := AdjoinRoot r.val.val
  let T := integralClosure R L
  let U := integralClosure R D
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap F L).injective
  let : CharZero D := charZero_of_injective_algebraMap (algebraMap L D).injective
  let : FiniteDimensional L D := r.val.property.1.finite_adjoinRoot
  let : FiniteDimensional F D := Module.Finite.trans L D
  let : IsDiscreteValuationRing T := integralClosure_isDiscreteValuationRing R F L
  let : IsDiscreteValuationRing U := integralClosure_isDiscreteValuationRing R F D
  let : IsLocalHom (algebraMap R T) := integralClosure_isLocalHom R F L
  let : IsLocalHom (algebraMap T U) := coefficient_isLocalHom R p r
  let : IsFractionRing T L := IsIntegralClosure.isFractionRing_of_finite_extension R F L T
  let : IsFractionRing U D := IsIntegralClosure.isFractionRing_of_finite_extension R F D U
  let : Module.Finite T U := coefficient_finite R F L p r
  let : IsAdicComplete (maximalIdeal T) T := integralClosure_isAdicComplete R F L
  let : CharZero (ResidueField T) := charZero_of_injective_algebraMap
    (algebraMap (ResidueField R) (ResidueField T)).injective
  let : IsScalarTower R T U := baseTower R L D
  let : @IsScalarTower T U D _ _ (AdjoinRoot.instSMulAdjoinRoot (S := T) r.val.val) := by
    let : Algebra T D := AdjoinRoot.instAlgebra (S := T) r.val.val
    exact IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsIntegralClosure U T D := coefficient_isIntegralClosure R p r
  exact residue_finiteExtensionNorm_complete_of_pGroup T U L D Ω ℓ hG g n x

end Complete

end MilnorK.PolynomialNorm.CompleteScalarBranch
