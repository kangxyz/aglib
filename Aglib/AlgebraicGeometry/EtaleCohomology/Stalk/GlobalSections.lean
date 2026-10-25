/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalGerms
public import Aglib.AlgebraicGeometry.EtaleCohomology.SlicePullback.SourceSquare

/-! # Original global cohomology classes as higher-image sections

The original represented integer augmentation supplies Ext restriction to
the actual base-changed terminal object. The existing original-presheaf
comparison then gives a genuine section of the original higher direct image.
Its stalk value is the existing original represented cohomology germ. No
properness, base-change isomorphism or finiteness of the value group is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

local instance globalSectionsTerminalClassSmall :
    Small.{u + 1} (Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      X.smallEtaleTopology F q ((siteBaseChange f).obj (etaleTerminal S))) :=
  originalCohomologyPresheaf_small f F q (op (etaleTerminal S))

/-- Original global Ext classes evaluated at the actual base-changed terminal
object, with the already normalized original integer augmentation. -/
def globalCohomologyTerminalClass : Sheaf.H.{w} F q →+
    Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1} X.smallEtaleTopology F q
      ((siteBaseChange f).obj (etaleTerminal S)) :=
  (Ext.mk₀ (representedIntegerAugmentation
    ((siteBaseChange f).obj (etaleTerminal S)))).precomp F (Nat.zero_add q)

/-- A genuine global section of the original higher direct image, constructed
from an original global cohomology class. -/
def cohomologyToHigherSections : Sheaf.H.{w} F q →+
    ((higherDirectImage f q).obj F).obj.obj (op (etaleTerminal S)) :=
  ((((resolutionCohomologyToHigherDirectImage f q).app F).app
    (op (etaleTerminal S))).hom.comp
      (originalCohomologyResolutionEquiv f (etaleTerminal S) F q).toAddMonoidHom).comp
        (globalCohomologyTerminalClass f F q)

/-- The section is exactly the original cohomology-presheaf comparison at the
terminal object, including its existing value-universe resizing. -/
theorem cohomologyToHigherSections_apply (x : Sheaf.H.{w} F q) :
    cohomologyToHigherSections f F q x =
      (originalCohomologyToHigherDirectImage f F q).app (op (etaleTerminal S))
        (Shrink.addEquiv.{u + 1, w}.symm (globalCohomologyTerminalClass f F q x)) := by
  change _ = (((resolutionCohomologyToHigherDirectImage f q).app F).app
    (op (etaleTerminal S)))
      (originalCohomologyResolutionEquiv f (etaleTerminal S) F q
        (Shrink.addEquiv.{u + 1, w}
          (Shrink.addEquiv.{u + 1, w}.symm (globalCohomologyTerminalClass f F q x))))
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- Every stalk value retains the actual represented original-cohomology germ.
A later proper base-change comparison must still identify this germ with the
original fibre restriction; that identification is not assumed here. -/
theorem cohomologyToHigherSections_germ {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (η : Spec (.of Ω) ⟶ S) (a : (pointSmallEtale η).fiber.obj (etaleTerminal S))
    (x : Sheaf.H.{w} F q) :
    (pointSmallEtale η).toPresheafFiber (etaleTerminal S) a
      ((higherDirectImage f q).obj F).obj (cohomologyToHigherSections f F q x) =
        originalCohomologyGerm f F q η (etaleTerminal S) a
          (globalCohomologyTerminalClass f F q x) := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
