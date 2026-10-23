/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.Normalization

/-!
# The canonical underived étale base-change map

For the commuting square with top arrow `g' : X' ⟶ X`, bottom arrow
`g : S' ⟶ S`, and vertical arrows `f' : X' ⟶ S'` and `f : X ⟶ S`,
this file constructs `g* f_* ⟶ f'_* g'*` as the mate of the original
inverse-image composition comparison. A commuting square suffices for the map;
no cartesianness or invertibility of the resulting map is asserted.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge

/-- The ordinary direct image of the identity, normalized by the original site comparison. -/
def directImageIdIso (X : Scheme.{u}) : directImage (𝟙 X) ≅ 𝟭 (AbelianSheaf.{u, u + 1} X) :=
  Functor.sheafPushforwardContinuousId' (siteBaseChangeId X)
    AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X)

section CompositionCoherence

open CategoryTheory.Limits

/-- Transport along equality of base maps preserves the first pullback projection. -/
@[reassoc (attr := simp)]
theorem siteBaseChange_eqToHom_fst {X S : Scheme.{u}} {f g : S ⟶ X}
    (h : f = g) (U : X.Etale) :
    (eqToHom (congrArg (fun k => (siteBaseChange k).obj U) h)).left ≫
        pullback.fst U.hom g = pullback.fst U.hom f := by
  subst g
  change (𝟙 _) ≫ pullback.fst U.hom f = _
  exact Category.id_comp _

/-- Transport along equality of base maps preserves the structural pullback projection. -/
@[reassoc (attr := simp)]
theorem siteBaseChange_eqToHom_snd {X S : Scheme.{u}} {f g : S ⟶ X}
    (h : f = g) (U : X.Etale) :
    (eqToHom (congrArg (fun k => (siteBaseChange k).obj U) h)).left ≫
        pullback.snd U.hom g = pullback.snd U.hom f := by
  subst g
  change (𝟙 _) ≫ pullback.snd U.hom f = _
  exact Category.id_comp _

/-- Underlying scheme maps of composable étale arrows compose without extra transports. -/
@[simp]
theorem etaleHom_comp_left {X : Scheme.{u}} {U V W : X.Etale}
    (a : U ⟶ V) (b : V ⟶ W) : (a ≫ b).left = a.left ≫ b.left := rfl

/-- The underlying map of the identity étale arrow. -/
@[simp]
theorem etaleHom_id_left {X : Scheme.{u}} (U : X.Etale) :
    (𝟙 U : U ⟶ U).left = 𝟙 U.left := rfl

/-- The structural arrow of the original base-changed étale object. -/
@[simp]
theorem siteBaseChange_obj_hom {X S : Scheme.{u}} (f : S ⟶ X) (U : X.Etale) :
    ((siteBaseChange f).obj U).hom = pullback.snd U.hom f := rfl

/-- The first projection of the original site base-change map. -/
@[reassoc (attr := simp)]
theorem siteBaseChange_map_fst {X S : Scheme.{u}} (f : S ⟶ X)
    {U V : X.Etale} (a : U ⟶ V) :
    ((siteBaseChange f).map a).left ≫ pullback.fst V.hom f =
      pullback.fst U.hom f ≫ a.left := by
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

/-- The structural projection of the original site base-change map. -/
@[reassoc (attr := simp)]
theorem siteBaseChange_map_snd {X S : Scheme.{u}} (f : S ⟶ X)
    {U V : X.Etale} (a : U ⟶ V) :
    ((siteBaseChange f).map a).left ≫ pullback.snd V.hom f = pullback.snd U.hom f := by
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
  exact pullback.lift_snd _ _ _

/-- The original composition comparison preserves the projection to the étale object. -/
@[reassoc (attr := simp)]
theorem siteBaseChangeComp_hom_fst_fst {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (U : X.Etale) :
    ((siteBaseChangeComp f g).hom.app U).left ≫
        pullback.fst (pullback.snd U.hom f) g ≫ pullback.fst U.hom f =
      pullback.fst U.hom (g ≫ f) :=
  MorphismProperty.Over.pullbackComp_left_fst_fst g f U

/-- The middle structural projection of the original composition comparison. -/
@[reassoc (attr := simp)]
theorem siteBaseChangeComp_hom_fst_snd {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (U : X.Etale) :
    ((siteBaseChangeComp f g).hom.app U).left ≫
        pullback.fst (pullback.snd U.hom f) g ≫ pullback.snd U.hom f =
      pullback.snd U.hom (g ≫ f) ≫ g := by
  simp [siteBaseChangeComp]

/-- The final structural projection of the original composition comparison. -/
@[reassoc (attr := simp)]
theorem siteBaseChangeComp_hom_snd {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (U : X.Etale) :
    ((siteBaseChangeComp f g).hom.app U).left ≫
        pullback.snd (pullback.snd U.hom f) g = pullback.snd U.hom (g ≫ f) :=
  MorphismProperty.Over.w ((siteBaseChangeComp f g).hom.app U)

/-- The identity site comparison is its original first pullback projection. -/
@[simp]
theorem siteBaseChangeId_hom_left (X : Scheme.{u}) (U : X.Etale) :
    ((siteBaseChangeId X).hom.app U).left = pullback.fst U.hom (𝟙 X) := rfl

/-- The original site pullback comparisons satisfy associativity on every étale object. -/
@[reassoc]
theorem siteBaseChangeComp_assoc {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T) (U : X.Etale) :
    (siteBaseChangeComp f (h ≫ g)).hom.app U ≫
        (siteBaseChangeComp g h).hom.app ((siteBaseChange f).obj U) =
      (eqToIso (congrArg (fun k => (siteBaseChange k).obj U) (Category.assoc h g f))).hom ≫
        (siteBaseChangeComp (g ≫ f) h).hom.app U ≫
        (siteBaseChange h).map ((siteBaseChangeComp f g).hom.app U) := by
  have hff := siteBaseChangeComp_hom_fst_fst g h ((siteBaseChange f).obj U)
  have hfs := siteBaseChangeComp_hom_fst_snd g h ((siteBaseChange f).obj U)
  have hs := siteBaseChangeComp_hom_snd g h ((siteBaseChange f).obj U)
  simp only [siteBaseChange_obj_hom] at hff hfs hs
  have hfff := congrArg (fun a => a ≫ pullback.fst U.hom f) hff
  have hffs := congrArg (fun a => a ≫ pullback.snd U.hom f) hff
  simp only [Category.assoc] at hfff hffs
  have hMF := siteBaseChange_map_fst h ((siteBaseChangeComp f g).hom.app U)
  have hMS := siteBaseChange_map_snd h ((siteBaseChangeComp f g).hom.app U)
  simp only [Functor.comp_obj, siteBaseChange_obj_hom] at hMF hMS
  have hMFF := congrArg (fun a => a ≫ pullback.fst (pullback.snd U.hom f) g ≫
    pullback.fst U.hom f) hMF
  have hMFS := congrArg (fun a => a ≫ pullback.fst (pullback.snd U.hom f) g ≫
    pullback.snd U.hom f) hMF
  have hMSF := congrArg (fun a => a ≫ pullback.snd (pullback.snd U.hom f) g) hMF
  simp only [Category.assoc, siteBaseChangeComp_hom_fst_fst] at hMFF
  simp only [Category.assoc, siteBaseChangeComp_hom_fst_snd] at hMFS
  simp only [Category.assoc, siteBaseChangeComp_hom_snd] at hMSF
  have hCF := siteBaseChangeComp_hom_fst_fst (g ≫ f) h U
  have hCFS := siteBaseChangeComp_hom_fst_snd (g ≫ f) h U
  have hCS := siteBaseChangeComp_hom_snd (g ≫ f) h U
  have hCFSg := congrArg (fun a => a ≫ g) hCFS
  simp only [Category.assoc] at hCFSg
  have htF := siteBaseChange_eqToHom_fst (Category.assoc h g f) U
  have htS := siteBaseChange_eqToHom_snd (Category.assoc h g f) U
  have htSh := congrArg (fun a => a ≫ h) htS
  have htShg := congrArg (fun a => a ≫ h ≫ g) htS
  simp only [Category.assoc] at htSh htShg
  apply MorphismProperty.Over.Hom.ext
  simp only [etaleHom_comp_left]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, siteBaseChange_obj_hom, eqToIso.hom,
          siteBaseChangeComp_hom_fst_fst, hfff]
        rw [hMFF, hCF]
        exact htF.symm
      · simp only [Category.assoc, siteBaseChange_obj_hom, eqToIso.hom,
          siteBaseChangeComp_hom_fst_snd, hffs]
        rw [hMFS, hCFSg]
        exact htShg.symm
    · simp only [Category.assoc, siteBaseChange_obj_hom, eqToIso.hom,
        siteBaseChangeComp_hom_snd_assoc, hfs]
      rw [hMSF, hCFS]
      exact htSh.symm
  · simp only [Category.assoc, siteBaseChange_obj_hom, eqToIso.hom,
      siteBaseChangeComp_hom_snd, hs]
    rw [hMS, hCS]
    exact htS.symm

/-- The site comparison with an identity in the second position is normalized by
its original pullback projection. -/
@[reassoc]
theorem siteBaseChangeComp_comp_id {X S : Scheme.{u}} (f : S ⟶ X) (U : X.Etale) :
    (siteBaseChangeComp f (𝟙 S)).hom.app U ≫
        (siteBaseChangeId S).hom.app ((siteBaseChange f).obj U) =
      eqToHom (congrArg (fun k => (siteBaseChange k).obj U) (Category.id_comp f)) := by
  apply MorphismProperty.Over.Hom.ext
  simp only [etaleHom_comp_left, siteBaseChangeId_hom_left]
  apply pullback.hom_ext
  · simp only [Category.assoc, siteBaseChange_obj_hom,
      siteBaseChangeComp_hom_fst_fst]
    exact (siteBaseChange_eqToHom_fst (Category.id_comp f) U).symm
  · simp only [Category.assoc, siteBaseChange_obj_hom,
      siteBaseChangeComp_hom_fst_snd, Category.comp_id]
    exact (siteBaseChange_eqToHom_snd (Category.id_comp f) U).symm

/-- The site comparison with an identity in the first position is normalized by
its original pullback projection. -/
@[reassoc]
theorem siteBaseChangeComp_id_comp {X S : Scheme.{u}} (f : S ⟶ X) (U : X.Etale) :
    (siteBaseChangeComp (𝟙 X) f).hom.app U ≫
        (siteBaseChange f).map ((siteBaseChangeId X).hom.app U) =
      eqToHom (congrArg (fun k => (siteBaseChange k).obj U) (Category.comp_id f)) := by
  apply MorphismProperty.Over.Hom.ext
  simp only [etaleHom_comp_left]
  apply pullback.hom_ext
  · simp only [Category.assoc, siteBaseChange_map_fst, siteBaseChangeId_hom_left,
      siteBaseChange_obj_hom,
      siteBaseChangeComp_hom_fst_fst]
    exact (siteBaseChange_eqToHom_fst (Category.comp_id f) U).symm
  · simp only [Category.assoc, siteBaseChange_map_snd, siteBaseChange_obj_hom,
      siteBaseChangeComp_hom_snd]
    exact (siteBaseChange_eqToHom_snd (Category.comp_id f) U).symm

/-- Equality transport of direct images is the contravariant transport on test objects. -/
theorem directImage_eqToHom_hom_app {X S : Scheme.{u}} {f g : S ⟶ X}
    (h : f = g) (F : AbelianSheaf.{u, u + 1} S) (U : X.Etaleᵒᵖ) :
    (eqToHom (congrArg (fun k => (directImage k).obj F) h)).hom.app U =
      F.obj.map (eqToHom
        (congrArg (fun k => (siteBaseChange k).obj U.unop) h.symm)).op := by
  subst g
  change (𝟙 _) = F.obj.map (𝟙 _)
  exact (F.obj.map_id _).symm

/-- Direct-image composition associates on the original coefficient sheaf, including
transport between the two parenthesizations of the composite scheme morphism. -/
@[reassoc]
theorem directImageCompIso_assoc_app {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T) (F : AbelianSheaf.{u, u + 1} V) :
    (directImage f).map ((directImageCompIso g h).hom.app F) ≫
        (directImageCompIso f (h ≫ g)).hom.app F ≫
        (eqToIso (congrArg (fun k => (directImage k).obj F) (Category.assoc h g f))).hom =
      (directImageCompIso f g).hom.app ((directImage h).obj F) ≫
        (directImageCompIso (g ≫ f) h).hom.app F := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map
      ((siteBaseChangeComp g h).hom.app ((siteBaseChange f).obj U.unop)).op ≫
      F.obj.map ((siteBaseChangeComp f (h ≫ g)).hom.app U.unop).op ≫
      (eqToHom (congrArg (fun k => (directImage k).obj F)
        (Category.assoc h g f))).hom.app U =
    F.obj.map ((siteBaseChange h).map ((siteBaseChangeComp f g).hom.app U.unop)).op ≫
      F.obj.map ((siteBaseChangeComp (g ≫ f) h).hom.app U.unop).op
  rw [directImage_eqToHom_hom_app]
  · simp only [← F.obj.map_comp, ← op_comp]
    apply congrArg F.obj.map
    · apply congrArg Quiver.Hom.op
      · have hs := congrArg
          (fun k => eqToHom (congrArg (fun a => (siteBaseChange a).obj U.unop)
            (Category.assoc h g f).symm) ≫ k) (siteBaseChangeComp_assoc f g h U.unop)
        simpa only [Category.assoc, eqToIso.hom, eqToHom_trans_assoc,
          eqToHom_refl, Category.id_comp] using hs
      · exact Category.assoc h g f

/-- The inverse-image composition comparison is conjugate to the native direct-image one. -/
theorem conjugateEquiv_inverseImageComp_hom {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) :
    conjugateEquiv ((inverseImageAdjunction f).comp (inverseImageAdjunction g))
        (inverseImageAdjunction (g ≫ f)) (inverseImageComp f g).hom =
      (directImageCompIso f g).hom :=
  Adjunction.conjugateEquiv_leftAdjointCompIso_inv
    (inverseImageAdjunction f) (inverseImageAdjunction g)
    (inverseImageAdjunction (g ≫ f)) (directImageCompIso f g)

/-- Equality transport for inverse images conjugates to the reversed direct-image transport. -/
theorem conjugateEquiv_inverseImage_eqToHom {X S : Scheme.{u}} {f g : S ⟶ X}
    (h : f = g) :
    conjugateEquiv (inverseImageAdjunction g) (inverseImageAdjunction f)
        (eqToHom (congrArg (fun k : S ⟶ X => inverseImage k) h)) =
      eqToHom (congrArg (fun k : S ⟶ X => directImage k) h.symm) := by
  subst g
  simp

/-- The native inverse-image comparisons associate for arbitrary abelian étale sheaves. -/
theorem inverseImageComp_assoc {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T) :
    inverseImageComp f (h ≫ g) ≪≫
        Functor.isoWhiskerLeft (inverseImage f) (inverseImageComp g h) =
      eqToIso (congrArg (fun k : V ⟶ X => inverseImage k) (Category.assoc h g f)) ≪≫
        inverseImageComp (g ≫ f) h ≪≫
        Functor.isoWhiskerRight (inverseImageComp f g) (inverseImage h) ≪≫
        Functor.associator (inverseImage f) (inverseImage g) (inverseImage h) := by
  let af := inverseImageAdjunction f
  let ag := inverseImageAdjunction g
  let ah := inverseImageAdjunction h
  let afg := inverseImageAdjunction (g ≫ f)
  let agh := inverseImageAdjunction (h ≫ g)
  let adjTotal := inverseImageAdjunction ((h ≫ g) ≫ f)
  let adjTotalAssoc := inverseImageAdjunction (h ≫ (g ≫ f))
  have hL : conjugateEquiv (af.comp (ag.comp ah)) adjTotal
      ((inverseImageComp f (h ≫ g)).hom ≫
        Functor.whiskerLeft (inverseImage f) (inverseImageComp g h).hom) =
      Functor.whiskerRight (directImageCompIso g h).hom (directImage f) ≫
        (directImageCompIso f (h ≫ g)).hom := by
    rw [← conjugateEquiv_comp _ (af.comp agh), conjugateEquiv_whiskerLeft]
    rw [conjugateEquiv_inverseImageComp_hom, conjugateEquiv_inverseImageComp_hom]
  have hR : conjugateEquiv (af.comp (ag.comp ah)) adjTotal
      (eqToHom (congrArg (fun k : V ⟶ X => inverseImage k) (Category.assoc h g f)) ≫
        (inverseImageComp (g ≫ f) h).hom ≫
        Functor.whiskerRight (inverseImageComp f g).hom (inverseImage h) ≫
        (Functor.associator (inverseImage f) (inverseImage g) (inverseImage h)).hom) =
      (Functor.associator (directImage h) (directImage g) (directImage f)).hom ≫
        Functor.whiskerLeft (directImage h) (directImageCompIso f g).hom ≫
        (directImageCompIso (g ≫ f) h).hom ≫
        eqToHom (congrArg (fun k : V ⟶ X => directImage k) (Category.assoc h g f).symm) := by
    rw [← conjugateEquiv_comp _ adjTotalAssoc, ← conjugateEquiv_comp _ (afg.comp ah),
      ← conjugateEquiv_comp _ ((af.comp ag).comp ah),
      conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight]
    rw [conjugateEquiv_inverseImageComp_hom, conjugateEquiv_inverseImageComp_hom,
      conjugateEquiv_inverseImage_eqToHom]
    all_goals simp only [Category.assoc]
  apply Iso.ext
  apply (conjugateEquiv (af.comp (ag.comp ah)) adjTotal).injective
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    eqToIso.hom]
  rw [hL, hR]
  apply NatTrans.ext
  funext F
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp, eqToHom_app]
  apply (cancel_mono (eqToIso
    (congrArg (fun k => (directImage k).obj F) (Category.assoc h g f))).hom).mp
  simpa only [Category.assoc, eqToIso.hom, eqToHom_trans, eqToHom_refl,
    Category.comp_id] using directImageCompIso_assoc_app f g h F

/-- Direct-image composition with the source identity uses the original identity comparison. -/
theorem directImageCompIso_comp_id {X S : Scheme.{u}} (f : S ⟶ X) :
    (directImageCompIso f (𝟙 S)).symm ≪≫
        Functor.isoWhiskerRight (directImageIdIso S) (directImage f) ≪≫
        Functor.leftUnitor (directImage f) =
      eqToIso (congrArg (fun k : S ⟶ X => directImage k) (Category.id_comp f)) := by
  apply Iso.ext_inv
  apply NatTrans.ext
  funext F
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, Category.id_comp, eqToIso.inv, eqToHom_app]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map ((siteBaseChangeId S).hom.app ((siteBaseChange f).obj U.unop)).op ≫
      F.obj.map ((siteBaseChangeComp f (𝟙 S)).hom.app U.unop).op =
    (eqToHom (congrArg (fun k => (directImage k).obj F)
      (Category.id_comp f).symm)).hom.app U
  rw [directImage_eqToHom_hom_app (Category.id_comp f).symm]
  rw [← F.obj.map_comp, ← op_comp, siteBaseChangeComp_comp_id]

/-- Direct-image composition with the target identity uses the original identity comparison. -/
theorem directImageCompIso_id_comp {X S : Scheme.{u}} (f : S ⟶ X) :
    (directImageCompIso (𝟙 X) f).symm ≪≫
        Functor.isoWhiskerLeft (directImage f) (directImageIdIso X) ≪≫
        Functor.rightUnitor (directImage f) =
      eqToIso (congrArg (fun k : S ⟶ X => directImage k) (Category.comp_id f)) := by
  apply Iso.ext_inv
  apply NatTrans.ext
  funext F
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.rightUnitor_inv_app, Category.id_comp, eqToIso.inv, eqToHom_app]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map ((siteBaseChange f).map ((siteBaseChangeId X).hom.app U.unop)).op ≫
      F.obj.map ((siteBaseChangeComp (𝟙 X) f).hom.app U.unop).op =
    (eqToHom (congrArg (fun k => (directImage k).obj F)
      (Category.comp_id f).symm)).hom.app U
  rw [directImage_eqToHom_hom_app (Category.comp_id f).symm]
  rw [← F.obj.map_comp, ← op_comp, siteBaseChangeComp_id_comp]

/-- The original inverse-image identity comparison is conjugate to the direct-image identity. -/
theorem conjugateEquiv_inverseImageId_hom (X : Scheme.{u}) :
    conjugateEquiv Adjunction.id (inverseImageAdjunction (𝟙 X))
        (inverseImageId X).hom = (directImageIdIso X).inv := by
  apply NatTrans.ext
  funext F
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((inverseImageAdjunction (𝟙 X)).ofNatIsoRight (directImageIdIso X)) Adjunction.id F
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit] at h
  change ((inverseImageAdjunction (𝟙 X)).unit.app F ≫
      (directImage (𝟙 X)).map ((inverseImageId X).hom.app F)) ≫
      (directImageIdIso X).hom.app F = 𝟙 F at h
  have hc := unit_conjugateEquiv Adjunction.id (inverseImageAdjunction (𝟙 X))
    (inverseImageId X).hom F
  change (𝟙 F) ≫ _ = _ at hc
  simp only [Category.id_comp, Functor.id_obj] at hc
  apply (cancel_mono ((directImageIdIso X).hom.app F)).1
  rw [hc, Iso.inv_hom_id_app]
  exact h

/-- The native inverse-image comparison with the source identity is normalized. -/
theorem inverseImageComp_comp_id {X S : Scheme.{u}} (f : S ⟶ X) :
    inverseImageComp f (𝟙 S) ≪≫
        Functor.isoWhiskerLeft (inverseImage f) (inverseImageId S) ≪≫
        Functor.rightUnitor (inverseImage f) =
      eqToIso (congrArg (fun k : S ⟶ X => inverseImage k) (Category.id_comp f)) := by
  let af := inverseImageAdjunction f
  let ai := inverseImageAdjunction (𝟙 S)
  let atotal := inverseImageAdjunction (𝟙 S ≫ f)
  have hc : conjugateEquiv af atotal
      ((inverseImageComp f (𝟙 S)).hom ≫
        Functor.whiskerLeft (inverseImage f) (inverseImageId S).hom ≫
        (Functor.rightUnitor (inverseImage f)).hom) =
      (Functor.leftUnitor (directImage f)).inv ≫
        Functor.whiskerRight (directImageIdIso S).inv (directImage f) ≫
        (directImageCompIso f (𝟙 S)).hom := by
    rw [← conjugateEquiv_comp _ (af.comp ai),
      ← conjugateEquiv_comp _ (af.comp Adjunction.id),
      conjugateEquiv_rightUnitor_hom, conjugateEquiv_whiskerLeft,
      conjugateEquiv_inverseImageId_hom, conjugateEquiv_inverseImageComp_hom]
    simp only [Category.assoc]
  apply Iso.ext
  apply (conjugateEquiv af atotal).injective
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, eqToIso.hom]
  rw [hc, conjugateEquiv_inverseImage_eqToHom (Category.id_comp f)]
  simpa only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv,
    eqToIso.inv, Category.assoc] using congrArg Iso.inv (directImageCompIso_comp_id f)

/-- The native inverse-image comparison with the target identity is normalized. -/
theorem inverseImageComp_id_comp {X S : Scheme.{u}} (f : S ⟶ X) :
    inverseImageComp (𝟙 X) f ≪≫
        Functor.isoWhiskerRight (inverseImageId X) (inverseImage f) ≪≫
        Functor.leftUnitor (inverseImage f) =
      eqToIso (congrArg (fun k : S ⟶ X => inverseImage k) (Category.comp_id f)) := by
  let af := inverseImageAdjunction f
  let ai := inverseImageAdjunction (𝟙 X)
  let atotal := inverseImageAdjunction (f ≫ 𝟙 X)
  have hc : conjugateEquiv af atotal
      ((inverseImageComp (𝟙 X) f).hom ≫
        Functor.whiskerRight (inverseImageId X).hom (inverseImage f) ≫
        (Functor.leftUnitor (inverseImage f)).hom) =
      (Functor.rightUnitor (directImage f)).inv ≫
        Functor.whiskerLeft (directImage f) (directImageIdIso X).inv ≫
        (directImageCompIso (𝟙 X) f).hom := by
    rw [← conjugateEquiv_comp _ (ai.comp af),
      ← conjugateEquiv_comp _ (Adjunction.id.comp af),
      conjugateEquiv_leftUnitor_hom, conjugateEquiv_whiskerRight,
      conjugateEquiv_inverseImageId_hom, conjugateEquiv_inverseImageComp_hom]
    simp only [Category.assoc]
  apply Iso.ext
  apply (conjugateEquiv af atotal).injective
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, eqToIso.hom]
  rw [hc, conjugateEquiv_inverseImage_eqToHom (Category.comp_id f)]
  simpa only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    eqToIso.inv, Category.assoc] using congrArg Iso.inv (directImageCompIso_id_comp f)

end CompositionCoherence

variable {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- The native inverse-image composition isomorphisms give the commuting pullback square. -/
def inverseImageSquareIso :
    inverseImage g ⋙ inverseImage f' ≅ inverseImage f ⋙ inverseImage g' :=
  (inverseImageComp g f').symm ≪≫
    eqToIso (congrArg (fun k : X' ⟶ S => inverseImage k) h) ≪≫ inverseImageComp f g'

/-- The canonical underived exchange is the mate under the two vertical adjunctions. -/
def baseChangeMap :
    directImage f ⋙ inverseImage g ⟶ inverseImage g' ⋙ directImage f' :=
  (mateEquiv (inverseImageAdjunction f) (inverseImageAdjunction f')
    (TwoSquare.mk _ _ _ _ (inverseImageSquareIso f f' g g' h).hom)).natTrans

/-- The exchange component uses the original target unit and source counit. -/
@[reassoc]
theorem baseChangeMap_app (F : AbelianSheaf.{u, u + 1} X) :
    (baseChangeMap f f' g g' h).app F =
      (inverseImageAdjunction f').unit.app ((inverseImage g).obj ((directImage f).obj F)) ≫
        (directImage f').map
          ((inverseImageSquareIso f f' g g' h).hom.app ((directImage f).obj F)) ≫
        (directImage f').map ((inverseImage g').map ((inverseImageAdjunction f).counit.app F)) :=
  mateEquiv_app_eq (inverseImageAdjunction f) (inverseImageAdjunction f') _ F

/-- The adjoint of the canonical exchange is the inverse-image square followed by the counit. -/
@[reassoc]
theorem baseChangeMap_counit (F : AbelianSheaf.{u, u + 1} X) :
    (inverseImage f').map ((baseChangeMap f f' g g' h).app F) ≫
        (inverseImageAdjunction f').counit.app ((inverseImage g').obj F) =
      (inverseImageSquareIso f f' g g' h).hom.app ((directImage f).obj F) ≫
        (inverseImage g').map ((inverseImageAdjunction f).counit.app F) :=
  mateEquiv_counit (inverseImageAdjunction f) (inverseImageAdjunction f') _ F

/-- The original counit equation characterizes the underived base-change map uniquely. -/
theorem eq_baseChangeMap_iff
    (β : directImage f ⋙ inverseImage g ⟶ inverseImage g' ⋙ directImage f') :
    β = baseChangeMap f f' g g' h ↔
      ∀ F : AbelianSheaf.{u, u + 1} X,
        (inverseImage f').map (β.app F) ≫
            (inverseImageAdjunction f').counit.app ((inverseImage g').obj F) =
          (inverseImageSquareIso f f' g g' h).hom.app ((directImage f).obj F) ≫
            (inverseImage g').map ((inverseImageAdjunction f).counit.app F) :=
  eq_mateEquiv_iff (inverseImageAdjunction f) (inverseImageAdjunction f') _ β

/-- Coefficient maps commute with the canonical underived exchange. -/
@[reassoc]
theorem baseChangeMap_naturality {F G : AbelianSheaf.{u, u + 1} X} (a : F ⟶ G) :
    (inverseImage g).map ((directImage f).map a) ≫ (baseChangeMap f f' g g' h).app G =
      (baseChangeMap f f' g g' h).app F ≫ (directImage f').map ((inverseImage g').map a) :=
  (baseChangeMap f f' g g' h).naturality a

/-- The actual inverse-image square over identity horizontal maps is normalized by the
original inverse-image identity comparisons. -/
theorem inverseImageSquareIso_id (e : f ≫ 𝟙 S = 𝟙 X ≫ f) :
    inverseImageSquareIso f f (𝟙 S) (𝟙 X) e ≪≫
        Functor.isoWhiskerLeft (inverseImage f) (inverseImageId X) ≪≫
        Functor.rightUnitor (inverseImage f) =
      Functor.isoWhiskerRight (inverseImageId S) (inverseImage f) ≪≫
        Functor.leftUnitor (inverseImage f) := by
  apply Iso.ext
  apply (cancel_epi (inverseImageComp (𝟙 S) f).hom).1
  simp only [inverseImageSquareIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  have hA := congrArg Iso.hom (inverseImageComp_id_comp f)
  have hB := congrArg Iso.hom (inverseImageComp_comp_id f)
  simp only [Iso.trans_hom] at hA hB
  rw [hB, hA]
  simp only [eqToIso.hom, eqToHom_trans]

/-- The canonical exchange for identity horizontal maps is the identity after the
original inverse-image identity comparisons, not a newly chosen exchange. -/
@[reassoc]
theorem baseChangeMap_id (e : f ≫ 𝟙 S = 𝟙 X ≫ f)
    (F : AbelianSheaf.{u, u + 1} X) :
    (baseChangeMap f f (𝟙 S) (𝟙 X) e).app F ≫
        (directImage f).map ((inverseImageId X).hom.app F) =
      (inverseImageId S).hom.app ((directImage f).obj F) := by
  have hα : ∀ A : AbelianSheaf.{u, u + 1} S,
      (inverseImage f).map ((inverseImageId S).hom.app A) ≫
          (TwoSquare.hId (inverseImage f)).app A =
        (inverseImageSquareIso f f (𝟙 S) (𝟙 X) e).hom.app A ≫
          (inverseImageId X).hom.app ((inverseImage f).obj A) := by
    intro A
    have he := congrArg (fun i => i.hom.app A) (inverseImageSquareIso_id f e)
    simpa [TwoSquare.hId] using he.symm
  have he := mateEquiv_top_bottom_naturality (inverseImageAdjunction f)
    (inverseImageAdjunction f)
    (TwoSquare.mk _ _ _ _ (inverseImageSquareIso f f (𝟙 S) (𝟙 X) e).hom)
    (TwoSquare.hId (inverseImage f)) (inverseImageId S).hom (inverseImageId X).hom hα F
  simpa [baseChangeMap, mateEquiv_hId, TwoSquare.vId] using he.symm

end AlgebraicGeometry.Scheme.EtaleCohomology
