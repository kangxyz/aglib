/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackLimitCohomologyLeg
public import Aglib.CategoryTheory.Sites.SheafCohomology.OriginalSections.Zero

/-! # Degree-zero normalization of original cohomological transfer -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u e
attribute [local instance] hasSheafifyLarge
open Continuity

variable {X Y : Scheme.{u}}
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]

/-- The original degree-zero transfer is the native section pullback and coefficient map. -/
theorem cohomologyTransfer_equiv₀ (f : Y ⟶ X)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} Y}
    (φ : (inverseImage f).obj F ⟶ G) (x : Sheaf.H.{e} F 0) :
    Sheaf.H.equiv₀ G (etaleTerminalIsTerminal Y) (cohomologyTransfer f φ 0 x) =
      (globalSections Y).map φ
        (globalSectionsPullback f F (Sheaf.H.equiv₀ F (etaleTerminalIsTerminal X) x)) :=
  Adjunction.integerExtZeroSectionsEquiv_transfer
    (constantAdjunction X) (inverseImageAdjunction f) (constantAdjunction Y)
    (directImageGlobalSectionsIso f) (inverseImageConstantIso f)
    (inverseImageConstantCanonicalIso_eq f).symm φ x

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
