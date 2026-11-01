/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DirectImageCoefficientSystem
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTestRightTailColimit
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.AffineSchemeCoverModels
public import Aglib.AlgebraicGeometry.Sites.AffineSheafification
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Filtered.Final

/-! # Original counit reconstruction on modeled étale tests

The actual right-image coefficient system has constant right tails through the
original structural triangles. The original evaluated right-tail continuity
therefore proves the counit comparison on every modeled qcqs test. No counit
comparison isomorphism is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Limits

/-- A map out of an actual colimit is invertible when every composite leg is
invertible and the original index is connected. -/
theorem isIso_of_colimit_composite_legs {J : Type*} [Category* J] [IsConnected J]
    {C : Type*} [Category* C] {D : J ⥤ C} (c : Cocone D) (hc : IsColimit c)
    {K : C} (f : c.pt ⟶ K) (h : ∀ j, IsIso (c.ι.app j ≫ f)) : IsIso f := by
  let : HasColimit D := ⟨c, hc⟩
  let d := c.extend f
  have (j : J) : IsIso (d.ι.app j) := h j
  have : IsIso d.ι := NatIso.isIso_of_isIso_app _
  let hd : IsColimit d := d.isColimitOfIsIsoColimMapι
  have he : f = (hc.coconePointUniqueUpToIso hd).hom := by
    apply hc.hom_ext
    intro j
    exact (hc.comp_coconePointUniqueUpToIso_hom hd j).symm
  rw [he]
  infer_instance

end CategoryTheory.Limits

namespace CategoryTheory.InjectiveSystem.AdjunctionData.Cone
universe uI vI uA vA uB vB
variable {I : Type uI} [Category.{vI} I]
  {A : I → Type uA} [∀ i, Category.{vA} (A i)]
  {D : AdjunctionData A} {B : Type uB} [Category.{vB} B]
  (P : D.Cone B) (K : B)
  [HasColimit (P.coefficientFunctor (P.rightImageSystem K))]

/-- Original adjunct insertion followed by the right image of the counit desc
is the original identity. -/
lemma adjointLeg_counitDesc (i : I) :
    P.adjointLeg (P.rightImageSystem K) i ≫
        (P.right i).map (colimit.desc _ (P.rightImageCounitCocone K)) = 𝟙 _ := by
  let δ := colimit.desc _ (P.rightImageCounitCocone K)
  have hn := (P.adj i).homEquiv_naturality_right
    (colimit.ι (P.coefficientFunctor (P.rightImageSystem K)) i) δ
  have hl : colimit.ι (P.coefficientFunctor (P.rightImageSystem K)) i ≫ δ =
      (P.adj i).counit.app K :=
    (colimit.ι_desc (P.rightImageCounitCocone K) i).trans
      (P.rightImageCounitCocone_ι K i)
  exact hn.symm.trans ((congrArg ((P.adj i).homEquiv ((P.right i).obj K) K) hl).trans
    ((congrArg ((P.adj i).homEquiv ((P.right i).obj K) K)
      ((P.adj i).homEquiv_symm_id K).symm).trans (Equiv.apply_symm_apply _ _)))

/-- Original right-tail legs followed by the comparison are precisely the
original right structural triangles, not a replacement constant diagram. -/
lemma rightTailLeg_counitDesc {i j : I} (a : i ⟶ j) :
    P.rightTailLeg (P.rightImageSystem K) a ≫
        (P.right i).map (colimit.desc _ (P.rightImageCounitCocone K)) =
      (P.rightTriangle a).hom.app K := by
  let δ := colimit.desc _ (P.rightImageCounitCocone K)
  have hn := (P.rightTriangle a).hom.naturality δ
  change (D.right a).map ((P.right j).map δ) ≫ (P.rightTriangle a).hom.app K =
    (P.rightTriangle a).hom.app _ ≫ (P.right i).map δ at hn
  have hm : (D.right a).map (P.adjointLeg (P.rightImageSystem K) j) ≫
      (D.right a).map ((P.right j).map δ) = 𝟙 ((D.right a).obj ((P.right j).obj K)) :=
    ((D.right a).map_comp _ _).symm.trans
      ((congrArg (D.right a).map (P.adjointLeg_counitDesc K j)).trans
        ((D.right a).map_id ((P.right j).obj K)))
  change ((D.right a).map (P.adjointLeg (P.rightImageSystem K) j) ≫
      (P.rightTriangle a).hom.app _) ≫ (P.right i).map δ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (D.right a).map (P.adjointLeg (P.rightImageSystem K) j) ≫ f)
      hn.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ (P.rightTriangle a).hom.app K) hm).trans
          (Category.id_comp _))))

end CategoryTheory.InjectiveSystem.AdjunctionData.Cone

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge
variable {I : Type u} [Category.{u} I] [hFiltered : IsFiltered I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (hc : IsColimit c)
  [hAffine : ∀ {j k} (m : j ⟶ k), IsAffineHom (X.map m).unop]
  (F : AbelianSheaf.{u, u + 1} c.pt.unop)
  [HasColimit (coneCoefficientFunctor X c (directImageCoefficientSystem X c F))]

include hc hFiltered hAffine

/-- The original comparison is invertible on each actual qcqs stage test,
after the original direct image along the original cone projection. -/
theorem isIso_directImageCounitComparison_stageTest (i : I)
    (T : (X.obj i).unop.Etale) [CompactSpace T.left] [QuasiSeparatedSpace T.left] :
    IsIso (((directImage (c.ι.app i).unop).map
      (directImageCounitComparison X c F)).hom.app (op T)) := by
  have : IsConnected (Under i) := IsFiltered.isConnected (Under i)
  let E := (sheafSections (X.obj i).unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op T)
  apply isIso_of_colimit_composite_legs
    (E.mapCocone (diagramRightTailCocone X (directImageCoefficientSystem X c F) c i))
    (isColimitDiagramRightTailEvaluation X c hc i T (directImageCoefficientSystem X c F))
  intro a
  have h := (diagramConeAdjunctionData X c).rightTailLeg_counitDesc F a.hom
  have he := congrArg E.map h
  rw [Functor.map_comp] at he
  change IsIso (E.map (diagramRightTailLeg X (directImageCoefficientSystem X c F) c a.hom) ≫
    E.map ((directImage (c.ι.app i).unop).map (directImageCounitComparison X c F)))
  have hi : IsIso (E.map (((diagramConeAdjunctionData X c).rightTriangle a.hom).hom.app F)) :=
    inferInstance
  exact he.symm ▸ hi

omit hAffine in
/-- Every affine étale test on an affine inverse limit is an actual base change
of an affine stage test. The auxiliary identity chart merely makes a cover. -/
lemma exists_affine_stage_model [∀ i, IsAffine (X.obj i).unop]
    (W : c.pt.unop.Etale) [IsAffine W.left] :
    ∃ (i : I) (T : (X.obj i).unop.Etale),
      IsAffine T.left ∧ Nonempty ((siteBaseChange (c.ι.app i).unop).obj T ≅ W) := by
  classical
  let D := X.leftOp
  let C := coneLeftOpOfCocone c
  have hC : IsLimit C := isLimitConeLeftOpOfCocone X hc
  have (i : Iᵒᵖ) : IsAffine (D.obj i) :=
    inferInstanceAs (IsAffine (X.obj i.unop).unop)
  have : IsAffine c.pt.unop := Scheme.isAffine_of_isLimit C hC
  have : Nonempty I := IsFiltered.nonempty
  let i₀ : I := Classical.arbitrary I
  let Y : Bool → Over c.pt.unop := fun b =>
    match b with
    | false => Over.mk W.hom
    | true => Over.mk (𝟙 c.pt.unop)
  have (b : Bool) : IsAffine (Y b).left := by
    cases b <;> dsimp [Y] <;> infer_instance
  have (b : Bool) : Etale (Y b).hom := by
    cases b <;> dsimp [Y] <;> infer_instance
  have hcover : ∀ x : c.pt.unop, ∃ b, ∃ y : (Y b).left, (Y b).hom y = x := by
    intro x
    exact ⟨true, x, rfl⟩
  obtain ⟨k, _q, Z, hZ, hEt, hm, _⟩ :=
    EtaleAffineBasis.exists_affineScheme_cover_model_above D C hC (op i₀) Y hcover
  let : Etale (Z false).hom := hEt false
  let T : (X.obj k.unop).unop.Etale := Etale.mk (Z false).hom
  let e := Classical.choice (hm false)
  refine ⟨k.unop, T, hZ false, ⟨?_⟩⟩
  exact MorphismProperty.Over.isoMk
    ((Over.forget c.pt.unop).mapIso e) (Over.w e.hom)

/-- The original comparison is an isomorphism for an actual affine inverse
limit, for arbitrary original abelian coefficients. -/
theorem isIso_directImageCounitComparison [∀ i, IsAffine (X.obj i).unop] :
    IsIso (directImageCounitComparison X c F) := by
  let δ := directImageCounitComparison X c F
  have h : ∀ W : c.pt.unop.Etale, IsAffine W.left → IsIso (δ.hom.app (op W)) := by
    intro W hW
    let := hW
    obtain ⟨i, T, hT, ⟨e⟩⟩ := exists_affine_stage_model X c hc W
    let := hT
    have hp : IsIso (δ.hom.app (op ((siteBaseChange (c.ι.app i).unop).obj T))) :=
      isIso_directImageCounitComparison_stageTest X c hc F i T
    exact (NatTrans.isIso_app_iff_of_iso δ.hom e.op).mpr hp
  let : Presheaf.IsLocallyInjective c.pt.unop.smallEtaleTopology δ.hom :=
    Etale.locallyInjective_of_affine c.pt.unop δ.hom (fun W hW => by
      let := h W hW
      exact (ConcreteCategory.bijective_of_isIso (δ.hom.app (op W))).injective)
  let : Presheaf.IsLocallySurjective c.pt.unop.smallEtaleTopology δ.hom :=
    Etale.locallySurjective_of_affine c.pt.unop δ.hom (fun W hW => by
      let := h W hW
      exact (ConcreteCategory.bijective_of_isIso (δ.hom.app (op W))).surjective)
  exact (Sheaf.isLocallyBijective_iff_isIso δ).mp ⟨inferInstance, inferInstance⟩

/-- The actual counit cocone is colimiting; its legs remain the original
counits from `directImageCounitCocone_ι`. -/
def isColimitDirectImageCounitCocone [∀ i, IsAffine (X.obj i).unop] :
    IsColimit (directImageCounitCocone X c F) := by
  letI : IsIso (directImageCounitComparison X c F) :=
    isIso_directImageCounitComparison X c hc F
  let e : colimit (coneCoefficientFunctor X c (directImageCoefficientSystem X c F)) ≅ F :=
    asIso (directImageCounitComparison X c F)
  exact IsColimit.ofIsoColimit (colimit.isColimit _)
    (Cocone.ext e (fun i => colimit.ι_desc (directImageCounitCocone X c F) i))

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
