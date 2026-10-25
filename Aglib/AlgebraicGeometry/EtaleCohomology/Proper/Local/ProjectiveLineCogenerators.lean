/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.FiniteCogenerators
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.FiniteProducts

/-! # Original projective-line tests on geometric annihilator cogenerators

The geometric predicate supplies an actual coefficient isomorphism to the
annihilator of a finite constant product. Original coefficient naturality
transports the finite-product tests to the underlying coefficient of the
given genuine module sheaf. No cohomological property is assumed in the
geometric predicate.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u eX eS

attribute [local instance] hasSheafifyLarge

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} (ProjectiveLine.projectiveP1 R))]
  [HasExt.{eS} (AbelianSheaf.{u, u + 1}
    (pullback (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)))]
  {n : ℕ} (M : Reduction.ZModSheaf (ProjectiveLine.projectiveP1 R) n)

/-- Every genuine module sheaf in the actual geometric annihilator class
has surjective original closed-fibre pullback in every degree. -/
theorem finiteConstantAnnihilator_residuePullback_surjective
    [IsSepClosed (IsLocalRing.ResidueField R)]
    (hM : IsFiniteConstantAnnihilator (ProjectiveLine.projectiveP1 R) n M) (q : ℕ) :
    Function.Surjective (cohomologyPullback.{u, eX, eS}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      ((Reduction.zmodUnderlying (ProjectiveLine.projectiveP1 R) n).obj M) q) := by
  obtain ⟨I, hI, Y, f, A, hf, hA, ⟨e⟩⟩ := hM
  let := hI
  let := hf
  let := hA
  exact cohomologyPullback_surjective_of_iso _ e.symm q
    (finiteConstantProductAnnihilator_residuePullback_surjective Y f A n q)

/-- Degree-zero injectivity holds on the same actual geometric test class
over a henselian local base without a separably closed residue-field premise. -/
theorem finiteConstantAnnihilator_residuePullback_injective_zero
    (hM : IsFiniteConstantAnnihilator (ProjectiveLine.projectiveP1 R) n M) :
    Function.Injective (cohomologyPullback.{u, eX, eS}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      ((Reduction.zmodUnderlying (ProjectiveLine.projectiveP1 R) n).obj M) 0) := by
  obtain ⟨I, hI, Y, f, A, hf, hA, ⟨e⟩⟩ := hM
  let := hI
  let := hf
  let := hA
  exact cohomologyPullback_injective_of_iso _ e.symm 0
    (finiteConstantProductAnnihilator_residuePullback_injective_zero Y f A n)

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
