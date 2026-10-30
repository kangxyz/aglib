/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.EtaleProductTests
public import Aglib.CategoryTheory.Sites.SheafCohomology.RepresentedTransfer.Trace
public import Aglib.CategoryTheory.Sites.SheafCohomology.RepresentedTransfer.Adjunction

/-! # Represented transfers induce natural sheaf transfers

A map from the free terminal sheaf to the free sheaf on an actual etale object
acts on product-test sheaves. Product symmetry and the terminal product
comparison turn this into a natural transformation from original restriction
followed by direct image to the identity. Its rank equation is normalized by
the original inverse-image/direct-image adjunction unit.
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

variable {X : Scheme.{u}} (U : X.Etale)
  (a : freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology X) (etaleTerminal X) ⟶
    freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology X) U)

local instance etaleProductTestsContinuous :
    ∀ V : X.Etale, (MorphismProperty.Over.productTest etaleMorphismProperty V).IsContinuous
      X.smallEtaleTopology X.smallEtaleTopology :=
  fun V => inferInstanceAs ((etaleProductTest V).IsContinuous
    X.smallEtaleTopology X.smallEtaleTopology)

/-- Evaluation of the original free arrow on the original product-test sheaves. -/
def etaleRepresentedRestrictionTrace :
    etaleProductSheaf U ⟶ 𝟭 (AbelianSheaf.{u, u + 1} X) :=
  representedRestrictionTrace.{u + 1, u, u + 1} etaleMorphismProperty X.smallEtaleTopology U a

/-- The represented rank relation gives the actual restriction-adjunction unit relation. -/
theorem etaleRepresentedRestrictionTrace_rank (n : ℕ)
    (ha : a ≫ (freeAbelianSheafFunctor.{u + 1} (Scheme.smallEtaleTopology X)).map
      ((etaleTerminalIsTerminal X).from U) = n • 𝟙 _)
    (F : AbelianSheaf.{u, u + 1} X) :
    ((siteEtalePostcomposeAdj (X := X) (S := U.left) U.hom).sheafPushforwardContinuous
      (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology U.left)
      (Scheme.smallEtaleTopology X)).unit.app F ≫
        (etaleRepresentedRestrictionTrace U a).app F = n • 𝟙 F :=
  representedRestrictionTrace_rank.{u + 1, u, u + 1}
    etaleMorphismProperty X.smallEtaleTopology U a n ha F

/-- The natural sheaf transfer with the original inverse image, not a replacement restriction. -/
def etaleRepresentedTrace :
    inverseImage (X := X) (S := U.left) U.hom ⋙
      directImage (X := X) (S := U.left) U.hom ⟶ 𝟭 (AbelianSheaf.{u, u + 1} X) :=
  Adjunction.traceThroughLeftAdjointUniq (inverseImageAdjunction (X := X) (S := U.left) U.hom)
    ((siteEtalePostcomposeAdj (X := X) (S := U.left) U.hom).sheafPushforwardContinuous
      (E := AddCommGrpCat.{u + 1}) U.left.smallEtaleTopology X.smallEtaleTopology)
    (etaleRepresentedRestrictionTrace U a)

/-- The exact original adjunction unit has composite equal to the represented rank. -/
theorem etaleRepresentedTrace_rank (n : ℕ)
    (ha : a ≫ (freeAbelianSheafFunctor.{u + 1} (Scheme.smallEtaleTopology X)).map
      ((etaleTerminalIsTerminal X).from U) = n • 𝟙 _)
    (F : AbelianSheaf.{u, u + 1} X) :
    (inverseImageAdjunction (X := X) (S := U.left) U.hom).unit.app F ≫
      (etaleRepresentedTrace U a).app F = n • 𝟙 F := by
  exact Adjunction.traceThroughLeftAdjointUniq_rank
    (inverseImageAdjunction (X := X) (S := U.left) U.hom)
    ((siteEtalePostcomposeAdj (X := X) (S := U.left) U.hom).sheafPushforwardContinuous
      (E := AddCommGrpCat.{u + 1}) U.left.smallEtaleTopology X.smallEtaleTopology)
    (etaleRepresentedRestrictionTrace U a) n F
    (etaleRepresentedRestrictionTrace_rank U a n ha F)

end AlgebraicGeometry.Scheme.EtaleCohomology
