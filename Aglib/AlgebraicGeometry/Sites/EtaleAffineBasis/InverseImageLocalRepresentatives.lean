/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.FiniteRefinement
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Pullback
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Finite local representatives for the original inverse image

The original inverse-image functor is compared with its native construction by
left Kan extension and sheafification. Each section on a quasi-compact test
object admits a finite affine covering family on which it comes from an actual
section of the original coefficient sheaf. The representation uses the native
Kan unit and canonical sheaf-pullback construction comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u

open EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : S ⟶ X) (F : AbelianSheaf.{u, u + 1} X)

/-- The native presheaf left Kan extension underlying inverse image. -/
def inverseImagePresentation : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (siteBaseChange f).op.lan.obj F.obj

/-- Its canonical map into the original inverse image, not a replacement sheaf. -/
def inverseImagePresentationMap : inverseImagePresentation f F ⟶
    ((inverseImage f).obj F).obj :=
  toSheafify S.smallEtaleTopology (inverseImagePresentation f F) ≫
    ((Functor.sheafPullbackConstruction.sheafPullbackIso (siteBaseChange f)
      AddCommGrpCat.{u + 1} X.smallEtaleTopology S.smallEtaleTopology).inv.app F).hom

/-- The construction map is locally surjective because sheafification is. -/
instance inverseImagePresentationMap_isLocallySurjective :
    Presheaf.IsLocallySurjective S.smallEtaleTopology (inverseImagePresentationMap f F) := by
  let : EssentiallySmall.{u + 1} S.Etale := essentiallySmallSelf.{0, u, u + 1} S.Etale
  let : S.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    .ofEssentiallySmall S.smallEtaleTopology
  let e := (Functor.sheafPullbackConstruction.sheafPullbackIso (siteBaseChange f)
    AddCommGrpCat.{u + 1} X.smallEtaleTopology S.smallEtaleTopology).symm.app F
  have : IsIso e.hom.hom :=
    Iso.isIso_hom ((sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso e)
  let h₂ : Presheaf.IsLocallySurjective S.smallEtaleTopology e.hom.hom :=
    Presheaf.isLocallySurjective_of_iso S.smallEtaleTopology e.hom.hom
  let h₁ : Presheaf.IsLocallySurjective S.smallEtaleTopology
      (toSheafify S.smallEtaleTopology (inverseImagePresentation f F)) :=
    (S.smallEtaleTopology.W_toSheafify (inverseImagePresentation f F)).isLocallySurjective
  exact @Presheaf.isLocallySurjective_comp _ _ S.smallEtaleTopology
    _ _ _ _ _ _ _ _ _
    (toSheafify S.smallEtaleTopology (inverseImagePresentation f F)) e.hom.hom h₁ h₂

/-- Every element of the native Kan extension has an actual original-section
representative, since its costructured-arrow category is filtered. -/
theorem exists_inverseImagePresentation_representative (W : S.Etale)
    (s : (inverseImagePresentation f F).obj (op W)) :
    ∃ (U : X.Etale) (a : W ⟶ (siteBaseChange f).obj U) (t : F.obj.obj (op U)),
      (inverseImagePresentation f F).map a.op
        (((siteBaseChange f).op.lanUnit.app F.obj).app (op U) t) = s := by
  let G := siteBaseChange f
  let : RepresentablyFlat G := flat_of_preservesFiniteLimits G
  let : IsFiltered (CostructuredArrow G.op (op W)) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence G W)
  let : PreservesFilteredColimitsOfSize.{u, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let h := Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit G.op F.obj (op W)
  obtain ⟨a, t, ht⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{u + 1}) h) s
  exact ⟨a.left.unop, a.hom.unop, t, ht⟩

/-- Every section of the original inverse image on a quasi-compact test object
has finitely many affine local representatives in the original coefficient sheaf. -/
theorem exists_finite_affine_inverseImage_representatives (W : S.Etale)
    [CompactSpace W.left] (s : ((inverseImage f).obj F).obj.obj (op W)) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → S.Etale) (g : ∀ i, V i ⟶ W),
      (∀ i, IsAffine (V i).left) ∧
      (Sieve.ofArrows V g ∈ S.smallEtaleTopology W) ∧
      ∀ i, ∃ (U : X.Etale) (a : V i ⟶ (siteBaseChange f).obj U)
        (t : F.obj.obj (op U)),
        (inverseImagePresentationMap f F).app (op (V i))
          ((inverseImagePresentation f F).map a.op
            (((siteBaseChange f).op.lanUnit.app F.obj).app (op U) t)) =
          ((inverseImage f).obj F).obj.map (g i).op s := by
  let q := inverseImagePresentationMap f F
  obtain ⟨ι, hι, V, g, hV, hg, hcover⟩ := exists_finite_affine_family W
    (Presheaf.imageSieve q s) (Presheaf.imageSieve_mem S.smallEtaleTopology q s)
  refine ⟨ι, hι, V, g, hV, hcover, fun i ↦ ?_⟩
  obtain ⟨U, a, t, ht⟩ := exists_inverseImagePresentation_representative f F (V i)
    (Presheaf.localPreimage q s (g i) (hg i))
  refine ⟨U, a, t, ?_⟩
  rw [ht]
  exact Presheaf.app_localPreimage q s (g i) (hg i)

end AlgebraicGeometry.Scheme.EtaleAffineBasis
