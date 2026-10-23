/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.AffineSections
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.AffineObjects
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.QcqsHypercover

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

private theorem isIso_app_of_multiforks {U : S.Etale}
    (E : S.smallEtaleTopology.OneHypercover.{u} U)
    {P Q : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (τ : P ⟶ Q)
    (hP : IsLimit (E.multifork P)) (hQ : IsLimit (E.multifork Q))
    [hτX : ∀ i, IsIso (τ.app (op (E.X i)))]
    [hτY : ∀ i j (k : E.I₁ i j), IsIso (τ.app (op (E.Y k)))] :
    IsIso (τ.app (op U)) := by
  let e : (E.multicospanIndex P).multicospan ≅ (E.multicospanIndex Q).multicospan :=
    WalkingMulticospan.functorExt
      (fun i ↦ @asIso _ _ _ _ (τ.app (op (E.X i))) (hτX i))
      (fun i ↦ @asIso _ _ _ _ (τ.app (op (E.Y i.2))) (hτY _ _ i.2))
      (fun i ↦ τ.naturality (E.p₁ i.2).op)
      (fun i ↦ τ.naturality (E.p₂ i.2).op)
  let hc := (IsLimit.postcomposeHomEquiv e (E.multifork P)).symm hP
  have heq : τ.app (op U) = (hc.conePointUniqueUpToIso hQ).hom := by
    apply Multifork.IsLimit.hom_ext hQ
    intro i
    have hi := (hc.conePointUniqueUpToIso_hom_comp hQ
      (WalkingMulticospan.left i)).symm
    have hi' : P.map (E.f i).op ≫ τ.app (op (E.X i)) =
        (hc.conePointUniqueUpToIso hQ).hom ≫ (E.multifork Q).ι i := by
      exact hi
    exact (τ.naturality (E.f i).op).symm.trans hi'
  rw [heq]
  exact Iso.isIso_hom _

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

private theorem isIso_pointwiseToSheafColimit_affine (U : S.Etale) [IsAffine U.left] :
    IsIso ((pointwiseToSheafColimit G).app (op U)) := by
  let := affineObjectSectionsPreservesFilteredColimits (I := I) U
  rw [pointwiseToSheafColimit_app]
  infer_instance

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
  let : Finite E.multicospanShape.L := inferInstanceAs (Finite E.I₀)
  let : Finite E.multicospanShape.R :=
    inferInstanceAs (Finite (Σ ij : E.I₀ × E.I₀, E.I₁ ij.1 ij.2))
  let (i : E.I₀) : IsAffine (E.X i).left := hX i
  let (i j : E.I₀) (k : E.I₁ i j) : IsAffine (E.Y k).left := hY i j k
  let (i : E.I₀) : IsIso ((pointwiseToSheafColimit G).app (op (E.X i))) :=
    isIso_pointwiseToSheafColimit_affine G (E.X i)
  let (i j : E.I₀) (k : E.I₁ i j) :
      IsIso ((pointwiseToSheafColimit G).app (op (E.Y k))) :=
    isIso_pointwiseToSheafColimit_affine G (E.Y k)
  let P := (G ⋙ sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).flip
  have hP : IsLimit (E.multifork P) := by
    apply evaluationJointlyReflectsLimits
    intro i
    exact (Multifork.isLimitMapEquiv (E.multifork P)
      ((CategoryTheory.evaluation I AddCommGrpCat.{u + 1}).obj i)).symm
      (E.isLimitMultifork (G.obj i))
  exact isIso_app_of_multiforks E (pointwiseToSheafColimit G)
    (Multifork.isLimitMapOfPreserves (E.multifork P) colim hP)
    (E.isLimitMultifork (colimit G))

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
