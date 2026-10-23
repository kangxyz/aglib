/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.PrimeToCharacteristicVanishing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.PrimeToCharacteristicDegreeTwo
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.FiniteConstantReduction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ResidueFiberDimension
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.LowDegree

/-! # Original finite-constant comparison for finite schemes over a strictly local line

The restriction is the original all-degree cohomology pullback followed by the
native constant-sheaf transport. The base is an arbitrary henselian local ring
with separably closed residue field; neither Noetherianity nor an invertible
coefficient-order condition is imposed on the final theorem.

The invertible-order degree-two case uses the actual Picard lift. Higher target
groups vanish by curve Kummer theory. Characteristic-primary coefficients and
the genuine split finite-abelian reduction provide the remaining coefficients.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u w w'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  {Y : Scheme.{u}} (f : Y ⟶ ProjectiveLine.projectiveP1 R) [IsFinite f]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} Y)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} (residueFiber f))]

/-- Every positive invertible cyclic coefficient has surjective original restriction
in every degree, without a Noetherian hypothesis on the henselian local base. -/
theorem finite_projectiveLine_invertibleCyclicRestriction_surjective
    (n : ℕ) (hn : 0 < n) (hR : IsUnit (n : Γ(Spec (.of R), ⊤))) (q : ℕ) :
    Function.Surjective (constantRestriction (ULift.{u} (ZMod n))
      (pullback.fst (f ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)) q) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let k := IsLocalRing.ResidueField R
  let : CompactSpace (residueFiber f) :=
    QuasiCompact.compactSpace_of_compactSpace (residueFiberStructureMap f)
  have hk : IsUnit (n : Γ(Spec (.of k), ⊤)) :=
    levelInvertible (LocalRing.residueSpecMap R) n hR
  have hbase : IsUnit (n : k) := by
    simpa using hk.map (Scheme.ΓSpecIso (.of k)).hom.hom
  have htarget : IsUnit (n : Γ(residueFiber f, ⊤)) :=
    levelInvertible
      (pullback.fst (f ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)) n
      (levelInvertible (f ≫ ProjectiveLine.structureMap R) n hR)
  by_cases hq : q ≤ 1
  · exact (finite_projectiveLine_constantRestriction_bijective_of_le_one
      (ULift.{u} (ZMod n)) f q hq).surjective
  · by_cases htwo : q = 2
    · subst q
      apply finite_projectiveLine_constantRestriction_two_surjective_of_picardBoundary_surjective
        f n hn hR
      exact picardBoundary_surjective_of_curve k (residueFiber f) (residueFiberStructureMap f)
        (residueFiber_topologicalKrullDim_le_one f) n hn hbase htarget
    · have hgt : 2 < q := by omega
      let : Subsingleton (Sheaf.H.{w'} (mu (residueFiber f) n) q) :=
        roots_subsingleton_H_of_curve k (residueFiber f) (residueFiberStructureMap f)
          (residueFiber_topologicalKrullDim_le_one f) n hn hbase htarget q hgt
      let : IsSepClosed (IsLocalRing.ResidueField k) :=
        Algebra.IsAlgebraic.isSepClosed (F := k) (E := IsLocalRing.ResidueField k)
      let e := Kummer.HenselianConstant.constantRootIsoOver k n hn hk (residueFiberStructureMap f)
      let : Subsingleton (Sheaf.H.{w'}
          (ConstantFinite.coefficient (ULift.{u} (ZMod n)) (residueFiber f)) q) :=
        (cohomologyMapIso_bijective e q).injective.subsingleton
      intro a
      exact ⟨0, Subsingleton.elim _ _⟩

/-- The original all-degree finite-constant restriction is surjective for a finite
scheme over the projective line over any strictly henselian local ring. -/
theorem finite_projectiveLine_constantRestriction_surjective
    (A : Type u) [AddCommGroup A] [Finite A] (q : ℕ) :
    Function.Surjective (constantRestriction A
      (pullback.fst (f ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)) q) :=
  finite_projectiveLine_constantRestriction_surjective_of_invertible_cyclic f q
    (fun n hn hR => finite_projectiveLine_invertibleCyclicRestriction_surjective f n hn hR q) A

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
