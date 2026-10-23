/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.FiniteHypercovers
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.Restriction
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.SectionsColimit

/-! # Filtered coefficient colimits on affine étale objects

The finite affine étale covering theorem supplies the hypotheses of the generic
finite-hypercover continuity theorem. Restriction is the original dense-subsite
equivalence, so the conclusion concerns the original small étale sheaves with
coefficients in `AddCommGrpCat.{u + 1}`.

This file proves section continuity on affine étale objects. It does not assert
higher cohomological continuity or global-section continuity for nonaffine qcqs
objects.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits Opposite
open CategoryTheory.GrothendieckTopology.OneHypercoverFamily

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

variable (S : Scheme.{u}) {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]

/-- Native affine-site sections preserve filtered coefficient colimits. -/
abbrev affineSectionsPreservesFilteredColimits (U : S.AffineEtale) :
    PreservesColimitsOfShape I
      ((sheafSections (Scheme.AffineEtale.topology S) AddCommGrpCat.{u + 1}).obj (op U)) :=
  preservesFilteredColimitsSections (I := I)
    (EtaleAffineBasis.finiteOneHypercoverFamily S) (fun {_} _ h => h) U

/-- Original small étale sections at an affine étale object preserve filtered
colimits, without changing the coefficient universe. -/
abbrev etaleAffineSectionsPreservesFilteredColimits (U : S.AffineEtale) :
    PreservesColimitsOfShape I
      ((sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op ((Scheme.AffineEtale.Spec S).obj U))) := by
  let := affineSectionsPreservesFilteredColimits (I := I) S U
  change PreservesColimitsOfShape I
    (EtaleAffineBasis.abelianRestriction S ⋙
      (sheafSections (Scheme.AffineEtale.topology S) AddCommGrpCat.{u + 1}).obj (op U))
  infer_instance

variable (G : I ⥤ Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) [HasColimit G]

/-- The canonical coefficient-colimit isomorphism for original étale sections
at the actual affine étale object. -/
def etaleAffineSectionsFilteredColimitIso (U : S.AffineEtale) :
    colimit (G ⋙ (sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op ((Scheme.AffineEtale.Spec S).obj U))) ≅
      (colimit G).obj.obj (op ((Scheme.AffineEtale.Spec S).obj U)) := by
  letI := etaleAffineSectionsPreservesFilteredColimits (I := I) S U
  exact (preservesColimitIso
    ((sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op ((Scheme.AffineEtale.Spec S).obj U))) G).symm

/-- The map is the original universal colimit comparison. -/
theorem etaleAffineSectionsFilteredColimitIso_hom (U : S.AffineEtale) :
    (etaleAffineSectionsFilteredColimitIso S G U).hom =
      colimit.post G ((sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op ((Scheme.AffineEtale.Spec S).obj U))) := rfl

/-- Compatibility with every original coefficient-diagram cocone map. -/
theorem etaleAffineSectionsFilteredColimitIso_ι (U : S.AffineEtale) (i : I) :
    colimit.ι (G ⋙ (sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op ((Scheme.AffineEtale.Spec S).obj U))) i ≫
      (etaleAffineSectionsFilteredColimitIso S G U).hom =
      (colimit.ι G i).hom.app (op ((Scheme.AffineEtale.Spec S).obj U)) := by
  let := etaleAffineSectionsPreservesFilteredColimits (I := I) S U
  exact ι_preservesColimitIso_inv
    ((sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op ((Scheme.AffineEtale.Spec S).obj U))) G i

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
