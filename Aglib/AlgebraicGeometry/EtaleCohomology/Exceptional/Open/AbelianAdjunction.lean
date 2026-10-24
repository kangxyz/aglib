/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleSliceSheaves
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Adjunction
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Exact lower shriek on the small étale site

The actual slice equivalence and the hom-indexed coproduct construction give
an exact left adjoint to the original inverse image along an étale morphism.
In particular this supplies the abelian extension-by-zero functor for open
immersions. The adjunction retains its original slice unit and its comparison
with inverse image. No proper-base-change or coefficient torsion hypothesis
is used. Native constant-ring module sheaves are a separate coefficient bridge.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- Actual lower shriek, obtained from the genuine étale slice and its coproduct extension. -/
def etaleLowerShriek : AbelianSheaf.{u, u + 1} U ⥤ AbelianSheaf.{u, u + 1} X :=
  (etaleSliceSheafEquivalence (Scheme.Etale.mk j)).functor ⋙
    Sheaf.SliceCohomology.lowerShriek (Scheme.smallEtaleTopology X)
      AddCommGrpCat.{u + 1} (Scheme.Etale.mk j)

/-- The lower-shriek adjunction to literal restriction on the original étale chart. -/
def etaleLowerShriekRestrictionAdjunction : etaleLowerShriek j ⊣ etaleRestriction j :=
  (etaleSliceSheafEquivalence (Scheme.Etale.mk j)).toAdjunction.comp
    (Sheaf.SliceCohomology.lowerShriekAdjunction (Scheme.smallEtaleTopology X)
      AddCommGrpCat.{u + 1} (Scheme.Etale.mk j))

/-- The actual adjunction to the original scheme inverse image. -/
def etaleLowerShriekAdjunction : etaleLowerShriek j ⊣ inverseImage j :=
  (etaleLowerShriekRestrictionAdjunction j).ofNatIsoRight (inverseImageEtaleIso j).symm

instance etaleLowerShriek_isLeftAdjoint : (etaleLowerShriek j).IsLeftAdjoint :=
  (etaleLowerShriekAdjunction j).isLeftAdjoint

instance etaleLowerShriek_additive : (etaleLowerShriek j).Additive :=
  (etaleLowerShriekAdjunction j).left_adjoint_additive

instance etaleLowerShriek_preservesFiniteLimits :
    PreservesFiniteLimits (etaleLowerShriek j) := by
  let : PreservesLimitsOfSize.{0, 0}
      (etaleSliceSheafEquivalence (Scheme.Etale.mk j)).functor :=
    (etaleSliceSheafEquivalence (Scheme.Etale.mk j)).symm.toAdjunction.rightAdjoint_preservesLimits
  let : PreservesFiniteLimits (etaleSliceSheafEquivalence (Scheme.Etale.mk j)).functor :=
    PreservesLimitsOfSize0.preservesFiniteLimits _
  let : AB4OfSize.{u} AddCommGrpCat.{u + 1} :=
    Sheaf.SliceCohomology.abelianGroupsAB4OfSize.{u, u + 1}
  let : PreservesFiniteLimits
      (Sheaf.SliceCohomology.lowerShriek (Scheme.smallEtaleTopology X)
        AddCommGrpCat.{u + 1} (Scheme.Etale.mk j)) :=
    Sheaf.SliceCohomology.lowerShriek_preservesFiniteLimits
      (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1} (Scheme.Etale.mk j)
  exact comp_preservesFiniteLimits
    (etaleSliceSheafEquivalence (Scheme.Etale.mk j)).functor
    (Sheaf.SliceCohomology.lowerShriek (Scheme.smallEtaleTopology X)
      AddCommGrpCat.{u + 1} (Scheme.Etale.mk j))

instance etaleLowerShriek_preservesColimits : PreservesColimits (etaleLowerShriek j) := by
  infer_instance

/-- The constructed functor preserves the original short exact sequence. -/
theorem shortExact_etaleLowerShriek {S : ShortComplex (AbelianSheaf.{u, u + 1} U)}
    (hS : S.ShortExact) : (S.map (etaleLowerShriek j)).ShortExact :=
  hS.map_of_exact (etaleLowerShriek j)

/-- The inverse-image hom equivalence becomes the original restriction hom equivalence. -/
@[reassoc]
theorem etaleLowerShriekAdjunction_homEquiv
    (F : AbelianSheaf.{u, u + 1} U) (G : AbelianSheaf.{u, u + 1} X)
    (a : (etaleLowerShriek j).obj F ⟶ G) :
    (etaleLowerShriekAdjunction j).homEquiv F G a ≫ (inverseImageEtaleIso j).hom.app G =
      (etaleLowerShriekRestrictionAdjunction j).homEquiv F G a := by
  rw [etaleLowerShriekAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply]
  simp

/-- The chosen adjunction unit is normalized by the original inverse-image comparison. -/
@[reassoc]
theorem etaleLowerShriekAdjunction_unit (F : AbelianSheaf.{u, u + 1} U) :
    (etaleLowerShriekAdjunction j).unit.app F ≫
        (inverseImageEtaleIso j).hom.app ((etaleLowerShriek j).obj F) =
      (etaleLowerShriekRestrictionAdjunction j).unit.app F := by
  simpa only [Adjunction.homEquiv_id] using
    etaleLowerShriekAdjunction_homEquiv j F ((etaleLowerShriek j).obj F) (𝟙 _)

/-- The restriction unit is the actual equivalence unit followed by the slice unit. -/
theorem etaleLowerShriekRestrictionAdjunction_unit (F : AbelianSheaf.{u, u + 1} U) :
    (etaleLowerShriekRestrictionAdjunction j).unit.app F =
      (etaleSliceSheafEquivalence (Scheme.Etale.mk j)).toAdjunction.unit.app F ≫
        (etaleSliceSheafEquivalence (Scheme.Etale.mk j)).inverse.map
          ((Sheaf.SliceCohomology.lowerShriekAdjunction (Scheme.smallEtaleTopology X)
            AddCommGrpCat.{u + 1} (Scheme.Etale.mk j)).unit.app
              ((etaleSliceSheafEquivalence (Scheme.Etale.mk j)).functor.obj F)) :=
  Adjunction.comp_unit_app _ _ F

end AlgebraicGeometry.Scheme.EtaleCohomology
