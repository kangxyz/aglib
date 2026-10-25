/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.AffineIntegralConstants.SheafColimit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleDirectImageMate

/-! # Original finite-constant pushforwards restricted to an étale chart

The original Over adjunction fixes represented section transport. Its
normalization against the original inverse-image unit allows the actual
étale base-change isomorphism to be used on the original represented
coordinates, including the frozen copyObj transitions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

universe u

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

open AffineIntegralConstants SchemeTorsorBaseChange

variable {X T : Scheme.{u}} (g : T ⟶ X)

/-- The original Over adjunction identifies actual group sections on all
relative test schemes, retaining their additive structure and universe lift. -/
def sectionFunctorBaseChangeIso (H : Grp (Over X)) [IsCommMonObj H.X] :
    (Over.map g).op ⋙ sectionFunctor H ≅ sectionFunctor (baseChangedGroup g H) :=
  NatIso.ofComponents (fun U => AddEquiv.toAddCommGrpIso
    ((AddEquiv.ulift.trans (pullbackSectionMulEquiv g U.unop H).toAdditive).trans
      AddEquiv.ulift.symm)) (by
    intro U V a
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply ULift.ext
    change Additive.ofMul
        ((pullbackSectionEquiv g V.unop H.X)
          ((Over.map g).map a.unop ≫ s.down.toMul)) =
      Additive.ofMul (a.unop ≫ (pullbackSectionEquiv g U.unop H.X) s.down.toMul)
    exact congrArg Additive.ofMul
      ((Over.mapPullbackAdj g).homEquiv_naturality_left a.unop s.down.toMul))

/-- An actual finite commutative étale coefficient isomorphism recovers an
actual group-scheme isomorphism by the proved small-site Yoneda equivalence. -/
def representedGroupIsoOfSheafIso
    {H K : Grp (Over T)} [IsCommMonObj H.X] [IsCommMonObj K.X]
    [IsFinite H.X.hom] [Etale H.X.hom] [IsFinite K.X.hom] [Etale K.X.hom]
    (e : representedSheaf H ≅ representedSheaf K) : H ≅ K where
  hom := representedSheafGroupPreimage e.hom
  inv := representedSheafGroupPreimage e.inv
  hom_inv_id := by
    apply (representedSheafHomEquiv H H).injective
    change representedSheafMap (_ ≫ _) = representedSheafMap (𝟙 H)
    rw [representedSheafMap_comp, representedSheafMap_preimage,
      representedSheafMap_preimage, representedSheafMap_id, e.hom_inv_id]
  inv_hom_id := by
    apply (representedSheafHomEquiv K K).injective
    change representedSheafMap (_ ≫ _) = representedSheafMap (𝟙 K)
    rw [representedSheafMap_comp, representedSheafMap_preimage,
      representedSheafMap_preimage, representedSheafMap_id, e.inv_hom_id]

private theorem isoPostcompose_hom_inv
    {C : Type*} [Category* C] {A D U : C} (e : A ≅ D) (s : U ⟶ A) :
    (s ≫ e.hom) ≫ e.inv = s :=
  ((Category.assoc s e.hom e.inv).trans
    (congrArg (fun k => s ≫ k) e.hom_inv_id)).trans (Category.comp_id s)

/-- Actual postcomposition gives the additive equivalence on one typed
scheme-valued section group, before any functor-object coercions are involved. -/
def sectionGroupPostcomposeEquiv
    {H K : Grp (Over T)} [IsCommMonObj H.X] [IsCommMonObj K.X] (e : H ≅ K) :
    ∀ U : Over T, RepresentedSections H U ≃+ RepresentedSections K U := by
  let e₀ := (Grp.forget (Over T)).mapIso e
  intro U
  exact {
    toEquiv := {
      toFun := fun s => ULift.up (Additive.ofMul (s.down.toMul ≫ e₀.hom))
      invFun := fun s => ULift.up (Additive.ofMul (s.down.toMul ≫ e₀.inv))
      left_inv := fun s => by
        apply ULift.ext
        exact congrArg Additive.ofMul (isoPostcompose_hom_inv e₀ s.down.toMul)
      right_inv := fun s => by
        apply ULift.ext
        exact congrArg Additive.ofMul (isoPostcompose_hom_inv e₀.symm s.down.toMul) }
    map_add' := fun s t => by
      apply ULift.ext
      exact congrArg Additive.ofMul
        (MonObj.mul_comp s.down.toMul t.down.toMul e.hom.hom.hom) }

/-- Postcomposition with an actual group-scheme isomorphism is natural on
all original scheme-valued section objects, including nonétale tests. -/
def sectionFunctorGroupIso
    {H K : Grp (Over T)} [IsCommMonObj H.X] [IsCommMonObj K.X] (e : H ≅ K) :
    sectionFunctor H ≅ sectionFunctor K :=
  NatIso.ofComponents
    (fun U => AddEquiv.toAddCommGrpIso (sectionGroupPostcomposeEquiv e U.unop)) (by
    intro U V a
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply ULift.ext
    exact congrArg Additive.ofMul
      (Category.assoc a.unop s.down.toMul e.hom.hom.hom))

/-- The fixed actual finite constant group at the new base is the original
pullback group, transported through the original constant coefficient maps. -/
def constantGroupBaseChangeIso (B : Type u) [AddCommGroup B] [Finite B] :
    baseChangedGroup g (ConstantFinite.representation B X).group ≅
      (ConstantFinite.representation B T).group :=
  representedGroupIsoOfSheafIso
    ((representedSheafBaseChangeIso g (ConstantFinite.representation B X).group).symm ≪≫
      (inverseImage g).mapIso (ConstantFinite.representation B X).iso ≪≫
        (inverseImageConstantIso g).app (ConstantFinite.value B) ≪≫
          (ConstantFinite.representation B T).iso.symm)

/-- The coordinate functor has exactly the accepted direct-image maps:
copyObj transports only along the specified original coordinate isomorphisms. -/
def constantCoordinateFunctor {S : Scheme.{u}}
    (B : Type u) [AddCommGroup B] [Finite B] :
    (Over S)ᵒᵖ ⥤ (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  (constantRepresentedDirectImageFunctor (X := S) B ⋙
    sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).copyObj
    (fun Y => constantDirectImageCoordinates B Y.unop)
    (fun Y => constantDirectImageCoordinatesIso B Y.unop)

/-- The original coordinate comparisons are a natural isomorphism for the
entire relative-object functor, with its actual represented maps. -/
def constantCoordinateFunctorIso {S : Scheme.{u}}
    (B : Type u) [AddCommGroup B] [Finite B] :
    constantRepresentedDirectImageFunctor (X := S) B ⋙
        sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} ≅
      constantCoordinateFunctor B :=
  (constantRepresentedDirectImageFunctor (X := S) B ⋙
    sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).isoCopyObj _ _

/-- The coordinate functor comparison retains its specified original component. -/
theorem constantCoordinateFunctorIso_hom_app {S : Scheme.{u}}
    (B : Type u) [AddCommGroup B] [Finite B] (Y : Over S) :
    (constantCoordinateFunctorIso (S := S) B).hom.app (op Y) =
      (constantDirectImageCoordinatesIso B Y).hom := rfl

/-- The inverse component is the inverse of that same original comparison. -/
theorem constantCoordinateFunctorIso_inv_app {S : Scheme.{u}}
    (B : Type u) [AddCommGroup B] [Finite B] (Y : Over S) :
    (constantCoordinateFunctorIso (S := S) B).inv.app (op Y) =
      (constantDirectImageCoordinatesIso B Y).inv := rfl

/-- The transported map remains the literal accepted section-coordinate map. -/
theorem constantCoordinateFunctor_map {S : Scheme.{u}}
    (B : Type u) [AddCommGroup B] [Finite B] {Y Z : (Over S)ᵒᵖ} (a : Y ⟶ Z) :
    (constantCoordinateFunctor B).map a =
      constantDirectImageCoordinateMap B a.unop := by
  change (constantDirectImageCoordinatesIso B Y.unop).inv ≫
      (constantRepresentedDirectImageMap B a.unop).hom ≫
      (constantDirectImageCoordinatesIso B Z.unop).hom = _
  rw [constantRepresentedDirectImageMap_coordinates, Iso.inv_hom_id_assoc]

private theorem isoChainCancelRight
    {C : Type*} [Category* C] {A D E Q : C}
    (a : A ≅ D) (b : D ≅ E) (c : Q ≅ E) :
    (a ≪≫ b ≪≫ c.symm).hom ≫ c.hom = a.hom ≫ b.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

section CopyObjRestriction

variable {I J C D : Type*} [Category* I] [Category* J] [Category* C] [Category* D]
  (P : I ⥤ C) (Q : J ⥤ D) (K : C ⥤ D) (R : I ⥤ J)
  (p : I → C) (ep : ∀ i, P.obj i ≅ p i)
  (q : J → D) (eqv : ∀ j, Q.obj j ≅ q j)

/-- Transport a whole restriction isomorphism through its specified copyObj
comparisons. No objectwise re-elaboration of the actual carriers is needed. -/
def copyObjRestrictionIso
    (h : P.copyObj p ep ⋙ K ≅ R ⋙ Q.copyObj q eqv) : P ⋙ K ≅ R ⋙ Q :=
  Functor.isoWhiskerRight (P.isoCopyObj p ep) K ≪≫ h ≪≫
    Functor.isoWhiskerLeft R (Q.isoCopyObj q eqv).symm

private theorem copyObjRestrictionIso_normalization
    (h : P.copyObj p ep ⋙ K ≅ R ⋙ Q.copyObj q eqv) :
    (copyObjRestrictionIso P Q K R p ep q eqv h).hom ≫
        (Functor.isoWhiskerLeft R (Q.isoCopyObj q eqv)).hom =
      (Functor.isoWhiskerRight (P.isoCopyObj p ep) K).hom ≫ h.hom := by
  exact isoChainCancelRight (Functor.isoWhiskerRight (P.isoCopyObj p ep) K) h
    (Functor.isoWhiskerLeft R (Q.isoCopyObj q eqv))

end CopyObjRestriction

variable [Etale g]

/-- On an étale chart the original scheme-section adjunction is an actual
isomorphism from literal sheaf restriction to the represented pullback. -/
def representedEtaleRestrictionIso (H : Grp (Over X)) [IsCommMonObj H.X] :
    (etaleRestriction g).obj (representedSheaf H) ≅
      representedSheaf (baseChangedGroup g H) :=
  ObjectProperty.isoMk _
    (Functor.isoWhiskerLeft (Scheme.Etale.forget T).op (sectionFunctorBaseChangeIso g H))

/-- The literal restriction comparison sends the literal restriction-unit
sections to their actual scheme pullbacks. -/
theorem representedEtaleRestrictionIso_unit (H : Grp (Over X)) [IsCommMonObj H.X] :
    (((siteEtalePostcomposeAdj g).sheafPushforwardContinuous
      (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology T)
      (Scheme.smallEtaleTopology X)).unit.app (representedSheaf H)) ≫
        (directImage g).map (representedEtaleRestrictionIso g H).hom =
      representedCoefficientUnit g H := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply ULift.ext
  change Additive.ofMul
      ((pullbackSectionEquiv g
        ((Scheme.Etale.forget T).obj ((siteBaseChange g).obj U.unop)) H.X)
        ((Scheme.Etale.forget X).map ((siteEtalePostcomposeAdj g).counit.app U.unop) ≫
          s.down.toMul)) =
    Additive.ofMul ((Over.pullback g).map s.down.toMul)
  apply congrArg Additive.ofMul
  apply (pullbackSectionEquiv g
    ((Scheme.Etale.forget T).obj ((siteBaseChange g).obj U.unop)) H.X).symm.injective
  rw [Equiv.symm_apply_apply]
  change (Over.mapPullbackAdj g).counit.app ((Scheme.Etale.forget X).obj U.unop) ≫
      s.down.toMul =
    (pullbackSectionEquiv g
      ((Over.pullback g).obj ((Scheme.Etale.forget X).obj U.unop)) H.X).symm
      ((Over.pullback g).map s.down.toMul)
  exact (pullbackSectionEquiv_symm_map g s.down.toMul).symm

/-- Original unit normalization identifies the actual section comparison
with the original inverse-image and represented-base-change isomorphisms. -/
theorem representedEtaleRestrictionIso_original
    (H : Grp (Over X)) [IsCommMonObj H.X] [Etale H.X.hom] :
    (inverseImageEtaleIso g).inv.app (representedSheaf H) ≫
        (representedSheafBaseChangeIso g H).hom =
      (representedEtaleRestrictionIso g H).hom := by
  apply (cancel_epi ((inverseImageEtaleIso g).hom.app (representedSheaf H))).mp
  rw [Iso.hom_inv_id_app_assoc]
  apply ((inverseImageAdjunction g).homEquiv _ _).injective
  change (inverseImageAdjunction g).unit.app (representedSheaf H) ≫
      (directImage g).map (representedSheafBaseChangeIso g H).hom =
    (inverseImageAdjunction g).unit.app (representedSheaf H) ≫
      (directImage g).map ((inverseImageEtaleIso g).hom.app (representedSheaf H) ≫
        (representedEtaleRestrictionIso g H).hom)
  rw [Functor.map_comp, ← Category.assoc, inverseImageEtaleIso_unit,
    representedSheafBaseChangeIso_unit, representedEtaleRestrictionIso_unit]

/-- The actual test schemes are identified by native pullback symmetry and
pasting, in the order used by the literal Over pullback functor. -/
def restrictionTestSchemeIso (Y : Over X) (U : T.Etale) :
    pullback U.hom (pullback.snd Y.hom g) ≅ pullback (U.hom ≫ g) Y.hom :=
  pullbackSymmetry U.hom (pullback.snd Y.hom g) ≪≫
    pullbackLeftPullbackSndIso Y.hom g U.hom ≪≫
      pullbackSymmetry Y.hom (U.hom ≫ g)

omit [Etale g] in
/-- The comparison retains the original étale-test projection. -/
@[reassoc]
theorem restrictionTestSchemeIso_fst (Y : Over X) (U : T.Etale) :
    (restrictionTestSchemeIso g Y U).hom ≫ pullback.fst (U.hom ≫ g) Y.hom =
      pullback.fst U.hom (pullback.snd Y.hom g) := by
  simp only [restrictionTestSchemeIso, Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd,
    pullbackLeftPullbackSndIso_hom_snd]

omit [Etale g] in
/-- The second projection is the original projection to the relative scheme. -/
@[reassoc]
theorem restrictionTestSchemeIso_snd (Y : Over X) (U : T.Etale) :
    (restrictionTestSchemeIso g Y U).hom ≫ pullback.snd (U.hom ≫ g) Y.hom =
      pullback.snd U.hom (pullback.snd Y.hom g) ≫ pullback.fst Y.hom g := by
  simp only [restrictionTestSchemeIso, Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_snd,
    pullbackSymmetry_hom_comp_fst_assoc, pullbackLeftPullbackSndIso_hom_fst]

/-- The native test comparison is an actual isomorphism over the original
base; no identification of endpoints is substituted for its original maps. -/
def restrictionTestOverIso (Y : Over X) (U : T.Etale) :
    (Over.map g).obj
        ((directImageTests ((Over.pullback g).obj Y)).obj U) ≅
      (directImageTests Y).obj ((siteEtalePostcompose g).obj U) :=
  Over.isoMk (restrictionTestSchemeIso g Y U) (by
    change (restrictionTestSchemeIso g Y U).hom ≫
        (pullback.snd (U.hom ≫ g) Y.hom ≫ Y.hom) =
      (pullback.snd U.hom (pullback.snd Y.hom g) ≫ pullback.snd Y.hom g) ≫ g
    rw [← Category.assoc, restrictionTestSchemeIso_snd]
    rw [Category.assoc, pullback.condition, ← Category.assoc])

private theorem postcomposedTestMap_fst (Y : Over X) {U V : T.Etale} (b : U ⟶ V) :
    ((siteBaseChange Y.hom).map ((siteEtalePostcompose g).map b)).left ≫
        pullback.fst (V.hom ≫ g) Y.hom =
      pullback.fst (U.hom ≫ g) Y.hom ≫ b.left :=
  siteBaseChange_map_fst Y.hom ((siteEtalePostcompose g).map b)

private theorem postcomposedTestMap_snd (Y : Over X) {U V : T.Etale} (b : U ⟶ V) :
    ((siteBaseChange Y.hom).map ((siteEtalePostcompose g).map b)).left ≫
        pullback.snd (V.hom ≫ g) Y.hom =
      pullback.snd (U.hom ≫ g) Y.hom :=
  siteBaseChange_map_snd Y.hom ((siteEtalePostcompose g).map b)

/-- Naturality in the original small-etale test schemes. -/
def restrictionTestsIso (Y : Over X) :
    directImageTests ((Over.pullback g).obj Y) ⋙ Over.map g ≅
      siteEtalePostcompose g ⋙ directImageTests Y :=
  NatIso.ofComponents (restrictionTestOverIso g Y) (by
    intro U V b
    apply Over.OverMorphism.ext
    change ((siteBaseChange (pullback.snd Y.hom g)).map b).left ≫
        (restrictionTestSchemeIso g Y V).hom =
      (restrictionTestSchemeIso g Y U).hom ≫
        ((siteBaseChange Y.hom).map ((siteEtalePostcompose g).map b)).left
    apply pullback.hom_ext
    · simp only [Category.assoc, restrictionTestSchemeIso_fst, siteBaseChange_map_fst]
      rw [postcomposedTestMap_fst g Y b, ← Category.assoc,
        restrictionTestSchemeIso_fst g Y U]
    · simp only [Category.assoc, restrictionTestSchemeIso_snd,
        siteBaseChange_map_snd_assoc]
      rw [postcomposedTestMap_snd g Y b, restrictionTestSchemeIso_snd g Y U])

omit [Etale g] in
private theorem relativePullbackMap_fst {Y Z : Over X} (a : Y ⟶ Z) :
    ((Over.pullback g).map a).left ≫ pullback.fst Z.hom g =
      pullback.fst Y.hom g ≫ a.left :=
  pullback.lift_fst _ _ _

private theorem relativeSourceTestMap_fst {Y Z : Over X} (a : Y ⟶ Z) (U : T.Etale) :
    (baseChangedTestMap ((Scheme.Etale.forget X).obj
      ((siteEtalePostcompose g).obj U)) a).left ≫ pullback.fst (U.hom ≫ g) Z.hom =
      pullback.fst (U.hom ≫ g) Y.hom :=
  baseChangedTestMap_fst _ a

private theorem relativeSourceTestMap_snd {Y Z : Over X} (a : Y ⟶ Z) (U : T.Etale) :
    (baseChangedTestMap ((Scheme.Etale.forget X).obj
      ((siteEtalePostcompose g).obj U)) a).left ≫ pullback.snd (U.hom ≫ g) Z.hom =
      pullback.snd (U.hom ≫ g) Y.hom ≫ a.left :=
  baseChangedTestMap_snd _ a

omit [Etale g] in
private theorem relativeTargetTestMap_fst {Y Z : Over X} (a : Y ⟶ Z) (U : T.Etale) :
    (baseChangedTestMap ((Scheme.Etale.forget T).obj U) ((Over.pullback g).map a)).left ≫
        pullback.fst U.hom (pullback.snd Z.hom g) =
      pullback.fst U.hom (pullback.snd Y.hom g) :=
  baseChangedTestMap_fst _ ((Over.pullback g).map a)

omit [Etale g] in
private theorem relativeTargetTestMap_snd {Y Z : Over X} (a : Y ⟶ Z) (U : T.Etale) :
    (baseChangedTestMap ((Scheme.Etale.forget T).obj U) ((Over.pullback g).map a)).left ≫
        pullback.snd U.hom (pullback.snd Z.hom g) =
      pullback.snd U.hom (pullback.snd Y.hom g) ≫ ((Over.pullback g).map a).left :=
  baseChangedTestMap_snd _ ((Over.pullback g).map a)

/-- The same comparison is natural in EVERY original relative-object map,
using the accepted original test-map lifts on both sides. -/
theorem restrictionTestsIso_relative {Y Z : Over X} (a : Y ⟶ Z) (U : T.Etale) :
    (Over.map g).map
        ((directImageTestsMap ((Over.pullback g).map a)).app U) ≫
      (restrictionTestsIso g Z).hom.app U =
    (restrictionTestsIso g Y).hom.app U ≫
      (directImageTestsMap a).app ((siteEtalePostcompose g).obj U) := by
  apply Over.OverMorphism.ext
  change (baseChangedTestMap ((Scheme.Etale.forget T).obj U)
        ((Over.pullback g).map a)).left ≫ (restrictionTestSchemeIso g Z U).hom =
    (restrictionTestSchemeIso g Y U).hom ≫
      (baseChangedTestMap ((Scheme.Etale.forget X).obj
        ((siteEtalePostcompose g).obj U)) a).left
  apply pullback.hom_ext
  · simp only [Category.assoc, restrictionTestSchemeIso_fst]
    rw [relativeTargetTestMap_fst g a U, relativeSourceTestMap_fst g a U,
      restrictionTestSchemeIso_fst g Y U]
  · simp only [Category.assoc, restrictionTestSchemeIso_snd]
    rw [relativeSourceTestMap_snd g a U, ← Category.assoc,
      relativeTargetTestMap_snd g a U, Category.assoc, relativePullbackMap_fst g a,
      restrictionTestSchemeIso_snd_assoc]

variable (B : Type u) [AddCommGroup B] [Finite B]

/-- Original represented coordinates restrict by the native test-pullback
isomorphism, original Over adjunction, and fixed actual coefficient group map. -/
def coordinateRestrictionIso (Y : Over X) :
    (siteEtalePostcompose g).op ⋙ constantDirectImageCoordinates B Y ≅
      constantDirectImageCoordinates B ((Over.pullback g).obj Y) := by
  let H := (ConstantFinite.representation B X).group
  let DX := directImageTests Y
  let D := directImageTests ((Over.pullback g).obj Y)
  let e := restrictionTestsIso g Y
  let e₀ : (siteEtalePostcompose g ⋙ DX).op ⋙ sectionFunctor H ≅
      (D ⋙ Over.map g).op ⋙ sectionFunctor H :=
    Functor.isoWhiskerRight (NatIso.op e) (sectionFunctor H)
  change (siteEtalePostcompose g).op ⋙ (DX.op ⋙ sectionFunctor H) ≅
    D.op ⋙ sectionFunctor (ConstantFinite.representation B T).group
  exact (Functor.associator (siteEtalePostcompose g).op DX.op (sectionFunctor H)).symm ≪≫
    Functor.isoWhiskerRight (Functor.opComp (siteEtalePostcompose g) DX).symm
      (sectionFunctor H) ≪≫ e₀ ≪≫
    Functor.isoWhiskerRight (Functor.opComp D (Over.map g)) (sectionFunctor H) ≪≫
    Functor.associator D.op (Over.map g).op (sectionFunctor H) ≪≫
    Functor.isoWhiskerLeft D.op (sectionFunctorBaseChangeIso g H) ≪≫
    Functor.isoWhiskerLeft D.op (sectionFunctorGroupIso (constantGroupBaseChangeIso g B))

/-- Every section is transported by the original test morphism and the
actual Over-adjunction section map, followed by the fixed group comparison. -/
theorem coordinateRestrictionIso_apply (Y : Over X) (U : T.Etale)
    (s : (constantDirectImageCoordinates B Y).obj (op ((siteEtalePostcompose g).obj U))) :
    (coordinateRestrictionIso g B Y).hom.app (op U) s =
      ULift.up (Additive.ofMul
        ((pullbackSectionEquiv g
          ((directImageTests ((Over.pullback g).obj Y)).obj U)
          (ConstantFinite.representation B X).group.X)
          ((restrictionTestsIso g Y).hom.app U ≫ s.down.toMul) ≫
            (constantGroupBaseChangeIso g B).hom.hom.hom)) := rfl

/-- The whole original relative-object square commutes in coordinates.
The relative maps are precisely the accepted original pullback lifts. -/
theorem coordinateRestrictionIso_relative {Y Z : Over X} (a : Y ⟶ Z) :
    Functor.whiskerLeft (siteEtalePostcompose g).op
        (constantDirectImageCoordinateMap B a) ≫
      (coordinateRestrictionIso g B Y).hom =
    (coordinateRestrictionIso g B Z).hom ≫
      constantDirectImageCoordinateMap B ((Over.pullback g).map a) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply ULift.ext
  let H := (ConstantFinite.representation B X).group
  let DY := (directImageTests ((Over.pullback g).obj Y)).obj U.unop
  let DZ := (directImageTests ((Over.pullback g).obj Z)).obj U.unop
  let t : DY ⟶ DZ := (directImageTestsMap ((Over.pullback g).map a)).app U.unop
  let q := (constantGroupBaseChangeIso g B).hom.hom.hom
  change Additive.ofMul
      ((pullbackSectionEquiv g DY H.X)
        ((restrictionTestsIso g Y).hom.app U.unop ≫
          ((directImageTestsMap a).app ((siteEtalePostcompose g).obj U.unop) ≫
            s.down.toMul)) ≫ q) =
    Additive.ofMul (t ≫
      ((pullbackSectionEquiv g DZ H.X)
        ((restrictionTestsIso g Z).hom.app U.unop ≫ s.down.toMul) ≫ q))
  rw [← Category.assoc t]
  apply congrArg (fun k => Additive.ofMul (k ≫ q))
  rw [← Category.assoc, ← restrictionTestsIso_relative, Category.assoc]
  exact (Over.mapPullbackAdj g).homEquiv_naturality_left t
    ((restrictionTestsIso g Z).hom.app U.unop ≫ s.down.toMul)

/-- Whole relative-object coordinate restriction, with the actual frozen
maps on both coordinate functors. -/
def constantCoordinateRestrictionIso :
    constantCoordinateFunctor (S := X) B ⋙
        (Functor.whiskeringLeft T.Etaleᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
          (siteEtalePostcompose g).op ≅
      (Over.pullback g).op ⋙ constantCoordinateFunctor (S := T) B :=
  NatIso.ofComponents (fun Y => coordinateRestrictionIso g B Y.unop) (by
    intro Y Z a
    change Functor.whiskerLeft (siteEtalePostcompose g).op
          ((constantCoordinateFunctor (S := X) B).map a) ≫
        (coordinateRestrictionIso g B Z.unop).hom =
      (coordinateRestrictionIso g B Y.unop).hom ≫
        (constantCoordinateFunctor (S := T) B).map
          (((Over.pullback g).map a.unop).op)
    rw [constantCoordinateFunctor_map, constantCoordinateFunctor_map]
    exact coordinateRestrictionIso_relative g B a.unop)

/-- The whole coordinate comparison keeps its specified original component. -/
theorem constantCoordinateRestrictionIso_hom_app (Y : Over X) :
    (constantCoordinateRestrictionIso g B).hom.app (op Y) =
      (coordinateRestrictionIso g B Y).hom := rfl

/-- The source coordinate comparison is the native whisker of the original
isoCopyObj data, on the whole original restricted direct-image functor. -/
def representedRestrictionSourceCoordinatesIso :
    (constantRepresentedDirectImageFunctor (X := X) B ⋙ etaleRestriction g) ⋙
        sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ≅
      constantCoordinateFunctor (S := X) B ⋙
        (Functor.whiskeringLeft T.Etaleᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
          (siteEtalePostcompose g).op :=
  Functor.isoWhiskerRight (constantCoordinateFunctorIso (S := X) B)
    ((Functor.whiskeringLeft T.Etaleᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
      (siteEtalePostcompose g).op)

/-- The target coordinate comparison retains the original coordinate iso
on every literal Over pullback, before any component carriers are expanded. -/
def representedRestrictionTargetCoordinatesIso :
    ((Over.pullback g).op ⋙ constantRepresentedDirectImageFunctor (X := T) B) ⋙
        sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ≅
      (Over.pullback g).op ⋙ constantCoordinateFunctor (S := T) B :=
  Functor.isoWhiskerLeft (Over.pullback g).op (constantCoordinateFunctorIso (S := T) B)

/-- The whole comparison before forgetting sheaf conditions, retaining the
specified original coordinate isomorphisms at both ends. -/
def representedDirectImageRestrictionPresheafIso :
    (constantRepresentedDirectImageFunctor (X := X) B ⋙ etaleRestriction g) ⋙
        sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ≅
      ((Over.pullback g).op ⋙ constantRepresentedDirectImageFunctor (X := T) B) ⋙
        sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  copyObjRestrictionIso
    (constantRepresentedDirectImageFunctor (X := X) B ⋙
      sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (constantRepresentedDirectImageFunctor (X := T) B ⋙
      sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    ((Functor.whiskeringLeft T.Etaleᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
      (siteEtalePostcompose g).op)
    (Over.pullback g).op
    (fun Y => constantDirectImageCoordinates B Y.unop)
    (fun Y => constantDirectImageCoordinatesIso B Y.unop)
    (fun Z => constantDirectImageCoordinates B Z.unop)
    (fun Z => constantDirectImageCoordinatesIso B Z.unop)
    (constantCoordinateRestrictionIso g B)

/-- Full faithfulness of forgetting sheaf conditions lifts the original
coordinate comparison, including its entire relative-object naturality. -/
def representedDirectImageRestrictionIso :
    constantRepresentedDirectImageFunctor (X := X) B ⋙ etaleRestriction g ≅
      (Over.pullback g).op ⋙ constantRepresentedDirectImageFunctor (X := T) B :=
  ((Functor.FullyFaithful.ofFullyFaithful
      (sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})).whiskeringRight
        (Over X)ᵒᵖ).preimageIso (representedDirectImageRestrictionPresheafIso g B)

/-- The whole sheaf comparison obeys the original coordinate equation.
The source and target comparisons are the specified original isoCopyObj maps. -/
theorem representedDirectImageRestrictionIso_coordinates_whole :
    Functor.whiskerRight (representedDirectImageRestrictionIso g B).hom
        (sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ≫
      (representedRestrictionTargetCoordinatesIso g B).hom =
    (representedRestrictionSourceCoordinatesIso g B).hom ≫
      (constantCoordinateRestrictionIso g B).hom := by
  let FF := (Functor.FullyFaithful.ofFullyFaithful
    (sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})).whiskeringRight
      (Over X)ᵒᵖ
  have hRaw := FF.map_preimage (representedDirectImageRestrictionPresheafIso g B).hom
  change Functor.whiskerRight (representedDirectImageRestrictionIso g B).hom
      (sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) =
    (representedDirectImageRestrictionPresheafIso g B).hom at hRaw
  rw [hRaw]
  have hCoordinates := copyObjRestrictionIso_normalization
    (constantRepresentedDirectImageFunctor (X := X) B ⋙
      sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (constantRepresentedDirectImageFunctor (X := T) B ⋙
      sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    ((Functor.whiskeringLeft T.Etaleᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
      (siteEtalePostcompose g).op)
    (Over.pullback g).op
    (fun V => constantDirectImageCoordinates B V.unop)
    (fun V => constantDirectImageCoordinatesIso B V.unop)
    (fun Z => constantDirectImageCoordinates B Z.unop)
    (fun Z => constantDirectImageCoordinatesIso B Z.unop)
    (constantCoordinateRestrictionIso g B)
  exact hCoordinates

/-- Projecting the whole original coordinate equation gives the actual
component equation without reconstructing its scheme-valued section carriers. -/
theorem representedDirectImageRestrictionIso_coordinates (Y : Over X) :
    (Functor.whiskerRight (representedDirectImageRestrictionIso g B).hom
        (sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ≫
      (representedRestrictionTargetCoordinatesIso g B).hom).app (op Y) =
    ((representedRestrictionSourceCoordinatesIso g B).hom ≫
      (constantCoordinateRestrictionIso g B).hom).app (op Y) :=
  congrArg (fun k => k.app (op Y))
    (representedDirectImageRestrictionIso_coordinates_whole g B)

/-- The actual symmetry identifies the native étale-base-change object
with the literal object selected by Over.pullback. -/
def pullbackSymmetryOverIso (Y : Over X) :
    Over.mk (pullback.fst g Y.hom) ≅ (Over.pullback g).obj Y :=
  Over.isoMk (pullbackSymmetry g Y.hom) (pullbackSymmetry_hom_comp_snd g Y.hom)

/-- The component formed from the existing original étale exchange, its
original constant transport, and the actual original symmetry coordinate map. -/
def constantPushforwardEtaleBaseChangeComponent (Y : Over X) :
    (inverseImage g).obj
        ((directImage Y.hom).obj (ConstantFinite.coefficient B Y.left)) ≅
      (directImage (pullback.snd Y.hom g)).obj
        (ConstantFinite.coefficient B (pullback Y.hom g)) :=
  (etaleBaseChangeIso Y.hom g).app (ConstantFinite.coefficient B Y.left) ≪≫
    (directImage (pullback.fst g Y.hom)).mapIso
      ((inverseImageConstantIso (pullback.snd g Y.hom)).app (ConstantFinite.value B)) ≪≫
        (constantPushforwardFunctor (X := T) B).mapIso
          (Iso.op (pullbackSymmetryOverIso g Y).symm)

/-- The native component uses the original exchange mate and the exact
original constant and relative-object symmetry maps. -/
theorem constantPushforwardEtaleBaseChangeComponent_hom (Y : Over X) :
    (constantPushforwardEtaleBaseChangeComponent g B Y).hom =
      (baseChangeMap Y.hom (pullback.fst g Y.hom) g (pullback.snd g Y.hom)
        pullback.condition).app (ConstantFinite.coefficient B Y.left) ≫
      (directImage (pullback.fst g Y.hom)).map
        ((inverseImageConstantIso (pullback.snd g Y.hom)).hom.app (ConstantFinite.value B)) ≫
      (constantPushforwardFunctor (X := T) B).map ((pullbackSymmetryOverIso g Y).inv.op) := by
  change (etaleBaseChangeIso Y.hom g).hom.app (ConstantFinite.coefficient B Y.left) ≫
      (directImage (pullback.fst g Y.hom)).map
        ((inverseImageConstantIso (pullback.snd g Y.hom)).hom.app (ConstantFinite.value B)) ≫
      (constantPushforwardFunctor (X := T) B).map ((pullbackSymmetryOverIso g Y).inv.op) = _
  rw [etaleBaseChangeIso_hom]

/-- The original constant-pushforward functor restricts to the original
constant-pushforward functor on the literal Over pullbacks. All transitions
are the fixed represented-coordinate and copyObj maps. -/
def constantPushforwardRestrictionIso :
    constantPushforwardFunctor (X := X) B ⋙ inverseImage g ≅
      (Over.pullback g).op ⋙ constantPushforwardFunctor (X := T) B :=
  Functor.isoWhiskerRight (constantPushforwardFunctorIso (X := X) B).symm
      (inverseImage g) ≪≫
    Functor.isoWhiskerLeft (constantRepresentedDirectImageFunctor (X := X) B)
      (inverseImageEtaleIso g) ≪≫
        representedDirectImageRestrictionIso g B ≪≫
          Functor.isoWhiskerLeft (Over.pullback g).op
            (constantPushforwardFunctorIso (X := T) B)

/-- Whole relative-object naturality for the exact original pushforward
maps and the actual original inverse-image functor. -/
@[reassoc]
theorem constantPushforwardRestrictionIso_naturality
    {Y Z : Over X} (a : Y ⟶ Z) :
    (inverseImage g).map ((constantPushforwardFunctor B).map a.op) ≫
        (constantPushforwardRestrictionIso g B).hom.app (op Y) =
      (constantPushforwardRestrictionIso g B).hom.app (op Z) ≫
        (constantPushforwardFunctor B).map (((Over.pullback g).map a).op) :=
  (constantPushforwardRestrictionIso g B).hom.naturality a.op

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
