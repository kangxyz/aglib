/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SlicePullback.SourceSquare
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalCohomology

/-! # The represented integer augmentation on actual sections

The existing represented augmentation retains the original global integer
section. At the actual base-changed terminal object it is exactly the inverse
of the native direct-image global-section transport. These are underived
source normalizations for arbitrary resolution terms, not higher-cohomology
comparison assumptions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf.Hypercohomology

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

/-- The original represented integer augmentation restricts the actual global
section represented by a map from the original constant integer sheaf. -/
theorem representedIntegerAugmentation_sections {X : Scheme.{u}} (U : X.Etale)
    (A : AbelianSheaf.{u, u + 1} X)
    (a : (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ A) :
    sectionsEquiv.{u + 1} (Scheme.smallEtaleTopology X) U A
        (representedIntegerAugmentation U ≫ a) =
      A.obj.map ((etaleTerminalIsTerminal X).from U).op
        (Sheaf.ModuleCoefficients.constantHomSectionsEquiv (etaleTerminalIsTerminal X) A a) :=
  Sheaf.OriginalSections.representedIntegerAugmentation_sections
    (Scheme.smallEtaleTopology X) (etaleTerminalIsTerminal X) U A a

/-- At the actual base-changed terminal object, the same original represented
source is the native terminal transport of the original global section. -/
theorem directImagePresheafRepresentedIso_augmentation {X S : Scheme.{u}} (f : X ⟶ S)
    (A : AbelianSheaf.{u, u + 1} X)
    (a : (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ A) :
    (directImagePresheafRepresentedIso f (etaleTerminal S)).hom.app A
        (representedIntegerAugmentation ((siteBaseChange f).obj (etaleTerminal S)) ≫ a) =
      (directImageGlobalSectionsIso f).inv.app A
        ((constantIntegerHomGlobalSectionsIso X).hom.app A a) :=
  Sheaf.SliceCohomology.representedIntegerAugmentation_transport
    (Scheme.smallEtaleTopology X) (etaleTerminalIsTerminal X) (siteBaseChangeTerminalIso f) A a

end AlgebraicGeometry.Scheme.EtaleCohomology
