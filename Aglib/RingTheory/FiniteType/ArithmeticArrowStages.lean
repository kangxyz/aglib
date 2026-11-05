/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteType.ArrowSubalgebraColimit
public import Aglib.RingTheory.Nagata.ClosedSupportNormalization

/-! # Arithmetic properties of the original simultaneous arrow stages

Only the auxiliary ground ring is of finite type over the integers. The
original rings A and B and their original arrow are arbitrary. The same
sourceStage and targetStage used by the established inclusion cocones are
arithmetic finite type and hence Nagata; no alternate model is introduced.
-/

@[expose] public noncomputable section

namespace Algebra.FiniteTypeArrowLimit

universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra.FiniteType ℤ R] [Algebra R A] [Algebra R B]
  (α : A →ₐ[R] B) (s : Index A B)

/-- The same source stage has its actual arithmetic structure. -/
theorem sourceStage_finiteType_int : Algebra.FiniteType ℤ (sourceStage α s) := by
  let : IsScalarTower ℤ R (sourceStage α s) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  exact Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType ℤ R)
    (inferInstance : Algebra.FiniteType R (sourceStage α s))

/-- The same target stage has its actual arithmetic structure. -/
theorem targetStage_finiteType_int : Algebra.FiniteType ℤ (targetStage α s) := by
  let : IsScalarTower ℤ R (targetStage α s) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  exact Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType ℤ R)
    (inferInstance : Algebra.FiniteType R (targetStage α s))

/-- The literal source stage, not the arbitrary source ring, is Nagata. -/
theorem sourceStage_nagata : IsNagataRing.{u, 0} (sourceStage α s) := by
  let : Algebra.FiniteType ℤ (sourceStage α s) := sourceStage_finiteType_int α s
  exact IsNagataRing.of_finiteType_int _

/-- The literal target stage, not the arbitrary target ring, is Nagata. -/
theorem targetStage_nagata : IsNagataRing.{u, 0} (targetStage α s) := by
  let : Algebra.FiniteType ℤ (targetStage α s) := targetStage_finiteType_int α s
  exact IsNagataRing.of_finiteType_int _

end Algebra.FiniteTypeArrowLimit
