/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.CharacteristicPrimaryGeometry
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ResidueFiberDimension
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.LowDegree

/-! # Characteristic-primary restriction on the literal closed fibre

Above degree one the original target vanishes; in degrees zero and one the
existing proper-henselian theorem applies to the same original pullback map.
The local base is not required to be Noetherian, complete or equicharacteristic.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.OverField

universe u w w'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  {Y : Scheme.{u}} (f : Y ⟶ ProjectiveLine.projectiveP1 R) [IsFinite f]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} Y)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} (residueFiber f))]

/-- Every characteristic-primary cyclic coefficient has surjective original
restriction to the literal residue fibre, in every degree. -/
theorem finite_projectiveLine_characteristicPrimaryRestriction_surjective
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    (r q : ℕ) : Function.Surjective
      (constantRestriction (ULift.{u} (ZMod (p ^ r)))
        (pullback.fst (f ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)) q) := by
  by_cases hq : q ≤ 1
  · exact (finite_projectiveLine_constantRestriction_bijective_of_le_one
      (ULift.{u} (ZMod (p ^ r))) f q hq).surjective
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show 2 ≤ q by omega)
    have hq' : q = m + 2 := by omega
    rw [hq']
    let C : FScheme (IsLocalRing.ResidueField R) := Over.mk (residueFiberStructureMap f)
    let : HasExt.{w'} (AbelianSheaf.{u, u + 1} C.left) :=
      inferInstanceAs (HasExt.{w'} (AbelianSheaf.{u, u + 1} (residueFiber f)))
    let : IsProper C.hom := inferInstanceAs (IsProper (residueFiberStructureMap f))
    let : Subsingleton (Sheaf.H.{w'}
        (ConstantFinite.coefficient (ULift.{u} (ZMod (p ^ r))) (residueFiber f)) (m + 2)) :=
      characteristicPrimary_vanishing.{u, w'} C (residueFiber_topologicalKrullDim_le_one f) p m r
    intro a
    exact ⟨0, Subsingleton.elim _ _⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
