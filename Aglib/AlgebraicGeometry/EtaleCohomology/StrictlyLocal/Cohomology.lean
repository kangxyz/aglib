/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.StrictlyLocal.Site
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Basic
public import Aglib.CategoryTheory.Sites.SheafCohomology.SplitTerminal

/-! # Original small-etale cohomology over a strictly local ring -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.StrictlyLocal

universe u v w

variable (R : Type u) [CommRing R]

/-- Actual evaluation at the identity object in the original small etale site. -/
abbrev globalSections : AbelianSheaf.{u, v} (Spec (.of R)) ⥤ AddCommGrpCat.{v} :=
  (sheafSections (Scheme.smallEtaleTopology (Spec (.of R))) AddCommGrpCat.{v}).obj
    (op (terminalObject R))

variable [HasSheafify (Scheme.smallEtaleTopology (Spec (.of R))) AddCommGrpCat.{v}]

/-- Actual small-etale global sections preserve finite limits. -/
theorem globalSections_preservesFiniteLimits : PreservesFiniteLimits (globalSections.{u, v} R) :=
  CategoryTheory.SheafCohomology.SplitTerminal.sections_preservesFiniteLimits
    _ _ (terminalIsTerminal R)

variable [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]

/-- Global sections of arbitrary abelian sheaves are right exact over a
henselian local ring with separably closed residue field. -/
theorem globalSections_preservesFiniteColimits :
    PreservesFiniteColimits (globalSections.{u, v} R) :=
  CategoryTheory.SheafCohomology.SplitTerminal.sections_preservesFiniteColimits
    _ _ (terminalIsTerminal R) (covering_sieve_eq_top R)

/-- The actual constant integer sheaf in the small etale site is projective. -/
theorem constant_integer_projective :
    Projective ((constantSheaf (Scheme.smallEtaleTopology (Spec (.of R)))
      AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ))) :=
  CategoryTheory.SheafCohomology.SplitTerminal.constant_integer_projective
    _ _ (terminalIsTerminal R) (covering_sieve_eq_top R)

variable [HasExt.{w} (AbelianSheaf.{u, v} (Spec (.of R)))]

/-- Every element of the original Ext-based Sheaf.H in positive degree is zero. -/
theorem H_eq_zero (F : AbelianSheaf.{u, v} (Spec (.of R))) (q : ℕ) (hq : 0 < q)
    (x : Sheaf.H.{w} F q) : x = 0 :=
  CategoryTheory.SheafCohomology.SplitTerminal.H_eq_zero
    _ _ (terminalIsTerminal R) (covering_sieve_eq_top R) F q hq x

/-- Positive-degree small-etale cohomology is trivial at the declared value
and Ext universes, retaining their sheafification and Ext existence assumptions. -/
theorem subsingleton_H (F : AbelianSheaf.{u, v} (Spec (.of R))) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w} F q) :=
  CategoryTheory.SheafCohomology.SplitTerminal.subsingleton_H
    _ _ (terminalIsTerminal R) (covering_sieve_eq_top R) F q hq

end AlgebraicGeometry.Scheme.EtaleCohomology.StrictlyLocal
