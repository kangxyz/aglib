/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Cohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition

/-!
# Original abelian cohomology of injective genuine ZMod etale sheaves

The actual small-etale site supplies its native finite limits and the
identity terminal object. Coefficients have the standard value universe
one above schemes. Original abelian Ext may live in any independently
supplied universe; the explicit standard endpoint also supplies Ext from
the native enough-injectives theorem. No scheme finiteness or restriction
on the coefficient modulus is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u e

attribute [local instance] hasSheafifyLarge

/-- Actual scalar forgetting on genuine etale module sheaves preserves finite limits. -/
theorem zmodUnderlying_preservesFiniteLimits (X : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})) :=
  TorsionZMod.underlying_preservesFiniteLimits X.smallEtaleTopology n

/-- The same original small-etale coefficient functor preserves finite colimits. -/
theorem zmodUnderlying_preservesFiniteColimits (X : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})) :=
  TorsionZMod.underlying_preservesFiniteColimits X.smallEtaleTopology n

/-- Original positive abelian cohomology of an injective genuine etale module sheaf vanishes. -/
theorem zmodUnderlying_injective_cohomology_subsingleton (X : Scheme.{u}) (n : ℕ)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))) [Injective I] (k : ℕ) :
    Subsingleton (Sheaf.H.{e} ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).obj I) (k + 1)) :=
  TorsionZMod.underlying_injective_cohomology_subsingleton X.smallEtaleTopology n I
    (etaleTerminalIsTerminal X) k

/-- The original standard-sized abelian Ext model exists by native enough injectives. -/
theorem zmodUnderlyingAb_hasExtStandard (X : Scheme.{u}) :
    HasExt.{u + 1} (AbelianSheaf.{u, u + 1} X) := by
  let : EnoughInjectives (AbelianSheaf.{u, u + 1} X) :=
    Sheaf.LargeCohomology.enoughInjectivesLarge X.smallEtaleTopology
  exact hasExt_of_enoughInjectives _

attribute [local instance] zmodUnderlyingAb_hasExtStandard

/-- At the standard Ext size the original positive cohomology vanishes unconditionally. -/
theorem zmodUnderlying_injective_cohomology_subsingleton_standard (X : Scheme.{u}) (n : ℕ)
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))) [Injective I] (k : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).obj I) (k + 1)) :=
  zmodUnderlying_injective_cohomology_subsingleton X n I k

end AlgebraicGeometry.Scheme.EtaleCohomology
