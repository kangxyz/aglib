/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.AffineSections
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.AffineObjects
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.QcqsHypercover
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.FiniteMatchingCocone

/-!
# Filtered coefficient colimits of sections over qcqs étale objects

A finite affine one-hypercover reduces the original sections comparison to
its affine components. Both matching diagrams are limiting and filtered
colimits of abelian groups preserve their finite limits. The resulting map is
the native colimit comparison, not a replacement definition of sections.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

variable {S : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]

/-- The affine-object continuity result applies to any affine object of the
original small site, not only literal spectra. -/
abbrev affineObjectSectionsPreservesFilteredColimits (U : S.Etale) [IsAffine U.left] :
    PreservesColimitsOfShape I
      ((sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)) := by
  let := etaleAffineSectionsPreservesFilteredColimits (I := I) S
    (EtaleAffineBasis.affineModel U)
  exact preservesColimitsOfShape_of_natIso
    ((sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso
      (EtaleAffineBasis.affineModelIso U).op.symm)

variable (G : I ⥤ Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) [HasColimit G]

/-- The original comparison from the pointwise coefficient colimit to the
underlying presheaf of the sheaf colimit. -/
def pointwiseToSheafColimit :
    (G ⋙ sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).flip ⋙ colim ⟶
      (colimit G).obj :=
  (pointwiseIsColimit _).desc
    ((sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).mapCocone
      (colimit.cocone G))

omit [IsFiltered I] in
/-- Every component is precisely the universal sections-colimit comparison. -/
theorem pointwiseToSheafColimit_app (U : S.Etale) :
    (pointwiseToSheafColimit G).app (op U) =
      colimit.post G
        ((sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)) := by
  apply colimit.hom_ext
  intro i
  have h := congrArg (fun t ↦ t.app (op U))
    ((pointwiseIsColimit _).fac
      ((sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).mapCocone
        (colimit.cocone G)) i)
  have h' := colimit.ι_post G
    ((sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)) i
  simp only [Functor.mapCocone_ι_app, colimit.cocone_ι] at h
  exact h.trans h'.symm

/-- The canonical sections comparison is an isomorphism on every original
qcqs étale object. -/
theorem isIso_pointwiseToSheafColimit_qcqs (U : S.Etale)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left] :
    IsIso ((pointwiseToSheafColimit G).app (op U)) := by
  obtain ⟨E, h₀, h₁, hX, hY, _⟩ :=
    EtaleAffineBasis.exists_finite_affine_oneHypercover U ⊤
      (S.smallEtaleTopology.top_mem U)
  let : Finite E.I₀ := h₀
  let (i j : E.I₀) : Finite (E.I₁ i j) := h₁ i j
  let (i : E.I₀) : IsAffine (E.X i).left := hX i
  let (i j : E.I₀) (k : E.I₁ i j) : IsAffine (E.Y k).left := hY i j k
  let H := G ⋙ sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}
  let c := (sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).mapCocone
    (colimit.cocone G)
  have hU := E.isColimitEvaluationOfFiniteMatching H c
    (fun i => (G.obj i).property) (colimit G).property
    (fun i => by
      let := affineObjectSectionsPreservesFilteredColimits (I := I) (E.X i)
      exact isColimitOfPreserves
        ((sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op (E.X i)))
        (colimit.isColimit G))
    (fun i j k => by
      let := affineObjectSectionsPreservesFilteredColimits (I := I) (E.Y k)
      exact isColimitOfPreserves
        ((sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op (E.Y k)))
        (colimit.isColimit G))
  exact GrothendieckTopology.OneHypercover.isIso_pointwiseDesc_app_of_isColimit H c (op U) hU

/-- Sections over a qcqs original étale object commute with filtered
coefficient colimits in the original universe. -/
abbrev qcqsSectionsPreservesFilteredColimits (U : S.Etale)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left] :
    PreservesColimitsOfShape I
      ((sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)) where
  preservesColimit {G} := {
    preserves {c} hc := by
      let : HasColimit G := ⟨⟨c, hc⟩⟩
      have : IsIso (colimit.post G
          ((sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U))) := by
        rw [← pointwiseToSheafColimit_app]
        exact isIso_pointwiseToSheafColimit_qcqs G U
      let := preservesColimit_of_isIso_post
        ((sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)) G
      exact ⟨isColimitOfPreserves _ hc⟩ }

/-- The canonical filtered-colimit comparison for original qcqs sections. -/
def qcqsSectionsFilteredColimitIso (U : S.Etale)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left] :
    colimit (G ⋙ (sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)) ≅
      (colimit G).obj.obj (op U) := by
  letI := qcqsSectionsPreservesFilteredColimits (I := I) U
  exact (preservesColimitIso
    ((sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)) G).symm

/-- The displayed isomorphism uses the original universal colimit map. -/
theorem qcqsSectionsFilteredColimitIso_hom (U : S.Etale)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left] :
    (qcqsSectionsFilteredColimitIso G U).hom =
      colimit.post G
        ((sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)) := rfl

/-- Normalization at each original cocone injection. -/
theorem qcqsSectionsFilteredColimitIso_ι (U : S.Etale)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left] (i : I) :
    colimit.ι (G ⋙ (sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op U)) i ≫ (qcqsSectionsFilteredColimitIso G U).hom =
      (colimit.ι G i).hom.app (op U) := by
  let := qcqsSectionsPreservesFilteredColimits (I := I) U
  exact ι_preservesColimitIso_inv
    ((sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)) G i

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
