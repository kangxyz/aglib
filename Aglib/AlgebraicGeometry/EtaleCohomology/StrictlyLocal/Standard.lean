/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.StrictlyLocal.Cohomology

/-!
# Strictly-local vanishing in the native larger coefficient universe

The value universe `u + 1` matches the object universe of the actual small etale
site. These convenient specializations of the general value-universe theorems
retain the original small-etale sheaves and original Ext-based cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.StrictlyLocal

universe u w

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  [HasSheafify (Scheme.smallEtaleTopology (Spec (.of R))) AddCommGrpCat.{u + 1}]

/-- Global sections of all abelian sheaves in the native larger value universe
are right exact, with no concrete-sheafification comparison premise. -/
theorem globalSections_preservesFiniteColimits_standard :
    PreservesFiniteColimits (globalSections.{u, u + 1} R) :=
  globalSections_preservesFiniteColimits R

/-- The actual constant integer sheaf is projective in the native larger
coefficient universe, with no additional local-surjectivity premise. -/
theorem constant_integer_projective_standard :
    Projective ((constantSheaf (Scheme.smallEtaleTopology (Spec (.of R)))
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) :=
  constant_integer_projective R

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of R)))]

/-- Original positive-degree Sheaf.H is zero at the native larger value
universe and the explicitly supplied Ext universe. -/
theorem H_eq_zero_standard
    (F : AbelianSheaf.{u, u + 1} (Spec (.of R))) (q : ℕ) (hq : 0 < q)
    (x : Sheaf.H.{w} F q) : x = 0 :=
  H_eq_zero R F q hq x

/-- Actual positive-degree small-etale cohomology groups are trivial in the
native larger value universe, retaining only sheafification and Ext existence. -/
theorem subsingleton_H_standard
    (F : AbelianSheaf.{u, u + 1} (Spec (.of R))) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w} F q) :=
  subsingleton_H R F q hq

end AlgebraicGeometry.Scheme.EtaleCohomology.StrictlyLocal
