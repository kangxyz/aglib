/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Bounded
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.LocalTorsionColimit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.TorsionPostnikov

/-! # Proper base change on locally torsion coefficients

The original proper higher exchange is invertible on every internally torsion
sheaf. The same defined derived exchange is invertible on every bounded-below
complex whose homology sheaves are internally torsion. The base schemes and
base change are arbitrary, and the four supplied derived models are independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u dX dS dX' dS'

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) [IsProper f] (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (H : IsPullback g' f' f g)

/-- Proper base change for the original higher exchange on locally torsion
coefficients, with no uniform annihilator or restriction on the base. -/
theorem properHigherBaseChange_isIso
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) (q : ℕ) :
    IsIso ((higherBaseChangeMap f f' g g' H.w.symm q).app F) := by
  have : IsProper f' := MorphismProperty.of_isPullback H (inferInstance : IsProper f)
  exact Reduction.higherBaseChangeMap_isIso_of_torsion_of_killed f f' g g' H.w.symm q
    (fun n hn M hM => properHigherBaseChange_isIso_of_killed f f' g g' H n hn M hM q)
    F hF

/-- The same proper derived exchange on the original single of a locally
torsion sheaf. -/
theorem properDerivedBaseChange_single_isIso
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) :
    IsIso ((derivedBaseChangeMap f f' g g' H.w.symm).app
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)) :=
  (Reduction.derivedBaseChangeMap_single_isIso_iff_higher f f' g g' H.w.symm F).mpr
    (properHigherBaseChange_isIso f f' g g' H F hF)

/-- Proper base change for the original derived exchange on every D+ object
with locally torsion homology. No upper cohomology or dimension bound is needed. -/
theorem properDerivedBaseChange_isIso_of_torsion_homology
    (K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X))
    (hK : ∀ i : ℤ, IsTorsion X
      ((DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} X) i).obj K)) :
    IsIso ((derivedBaseChangeMap f f' g g' H.w.symm).app K) :=
  Reduction.derivedBaseChangeMap_isIso_of_torsion_homology f f' g g' H.w.symm
    (fun F hF q => properHigherBaseChange_isIso f f' g g' H F hF q) K hK

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
