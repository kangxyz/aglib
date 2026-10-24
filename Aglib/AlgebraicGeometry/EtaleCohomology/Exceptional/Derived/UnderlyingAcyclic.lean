/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ConstantRing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.HigherImageAcyclic
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.InjectiveAcyclic

/-!+# Direct-image acyclicity after forgetting arbitrary constant-ring scalars

The original underlying abelian sheaf of an injective constant-ring module has
vanishing positive Ext from every original free representable. Consequently,
its actual higher direct images vanish along every scheme morphism. This is an
acyclicity assertion, not injectivity after forgetting scalars.

The direct-image statement supplies the standard Ext existence witness
internally. It therefore places no restriction on the independent derived
universes of its consumers. No torsion, properness, or Noetherian assumption is
used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Sheaf.Hypercohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u e

attribute [local instance] hasSheafifyLarge
  TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- Every original free representable has vanishing positive Ext into the
underlying abelian sheaf of a genuine injective constant-ring module. -/
theorem moduleInjective_representedExt_subsingleton
    (X : Scheme.{u}) [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf X Λ) [Injective I]
    (U : X.Etale) (q : ℕ) :
    Subsingleton (Ext.{e} (freeAbelianSheaf.{u + 1} X.smallEtaleTopology U)
      ((SheafOfModules.toSheaf (constantRing X Λ)).obj I) (q + 1)) :=
  Sheaf.ModuleCoefficients.toSheaf_injective_ext_subsingleton_largeScalars
    (constantRing X Λ) I U q

/-- The original underlying abelian sheaf of an injective constant-ring module
is acyclic for the actual direct image, with Ext existence supplied internally. -/
theorem higherDirectImage_moduleInjective_isZero
    {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type (u + 1)) [Ring Λ]
    (I : ModuleSheaf X Λ) [Injective I] (q : ℕ) :
    IsZero ((higherDirectImage f (q + 1)).obj
      ((SheafOfModules.toSheaf (constantRing X Λ)).obj I)) := by
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} X) := hasExtStandard X
  exact Proper.Reduction.higherDirectImage_isZero_of_representedExt_vanishing.{u, u + 2}
    f ((SheafOfModules.toSheaf (constantRing X Λ)).obj I)
    (fun U k => moduleInjective_representedExt_subsingleton.{u, u + 2} X Λ I U k) q

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
