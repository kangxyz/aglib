/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.OpenLocalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ClosedStalk
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.DirectImageEvaluationComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.EtaleTraceStalk
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.GlobalEvaluationIso
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.StalkUniverse
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# The original lower-shriek to direct-image comparison

The clopen diagonal of a separated étale morphism gives a canonical map from
the identity to inverse image of direct image. Its mate under the original
lower-shriek adjunction is the comparison with direct image. The constructions
retain the original identity, composition, base-change and clopen-support maps.
The whole mate equations precede evaluation on a coefficient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u uC vC uD vD

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

section UnitNormalization

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- Whole inverse-comparison transport from the original unit normalization.
Only the given functors, maps and their two equations are needed. -/
private theorem whiskerRight_inv_comp_of_unit {L P G : C ⥤ D} (R : D ⥤ C)
    (e : L ≅ P) (η : 𝟭 C ⟶ L ⋙ R) (ε : P ⋙ R ⟶ 𝟭 C) [IsIso ε]
    (hη : η ≫ Functor.whiskerRight e.hom R = (asIso ε).inv)
    (t : L ⟶ G) (α : 𝟭 C ⟶ G ⋙ R)
    (ht : η ≫ Functor.whiskerRight t R = α) :
    Functor.whiskerRight (e.inv ≫ t) R = ε ≫ α := by
  have he : ε ≫ η = Functor.whiskerRight e.inv R := by
    apply (cancel_mono (Functor.whiskerRight e.hom R)).mp
    rw [Category.assoc, hη]
    simpa only [asIso_hom, ← Functor.whiskerRight_comp, Iso.inv_hom_id,
      Functor.whiskerRight_id'] using (asIso ε).hom_inv_id
  rw [Functor.whiskerRight_comp, ← he, Category.assoc, ht]

end UnitNormalization

/-- The original closed-support comparison specializes to a clopen immersion. -/
def etaleLowerShriekClopenIso {Y X : Scheme.{u}} (i : Y ⟶ X)
    [IsOpenImmersion i] [IsClosedImmersion i] : etaleLowerShriek i ≅ directImage i :=
  (Functor.leftUnitor (etaleLowerShriek i)).symm ≪≫
    Functor.isoWhiskerRight (directImageIdIso Y).symm (etaleLowerShriek i) ≪≫
      etaleLowerShriekDirectImageIso i (𝟙 Y) ≪≫
        eqToIso (congrArg (fun g : Y ⟶ X => directImage g) (Category.id_comp i))

/-- The whole clopen comparison is normalized by the original lower-shriek
unit and the inverse of the original inverse-image/direct-image counit. -/
theorem etaleLowerShriekClopenIso_unit {Y X : Scheme.{u}} (i : Y ⟶ X)
    [IsOpenImmersion i] [IsClosedImmersion i] :
    (etaleLowerShriekAdjunction i).unit ≫
      Functor.whiskerRight (etaleLowerShriekClopenIso i).hom (inverseImage i) =
        (asIso (inverseImageAdjunction i).counit).inv := by
  apply NatTrans.ext
  funext F
  let e := (directImageIdIso Y).app F
  let c := (directImageCompIso i (𝟙 Y)).app F
  let q := (eqToIso
    (congrArg (fun g : Y ⟶ X => directImage g) (Category.id_comp i))).app F
  let r := (inverseImageDirectImageCompIso i (𝟙 Y)).app F
  let ε := asIso (inverseImageAdjunction i).counit
  have hr : r.hom = (inverseImage i).map c.inv ≫
      ε.hom.app ((directImage (𝟙 Y)).obj F) := by
    simp only [r, c, ε, inverseImageDirectImageCompIso, Iso.app_hom, Iso.trans_hom,
      Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.rightUnitor_hom_app, Category.id_comp,
      asIso_hom]
    exact congrArg
      (fun a => (inverseImage i).map ((directImageCompIso i (𝟙 Y)).inv.app F) ≫ a)
      (Category.comp_id ((inverseImageAdjunction i).counit.app ((directImage (𝟙 Y)).obj F)))
  have hrInv : r.inv = ε.inv.app ((directImage (𝟙 Y)).obj F) ≫
      (inverseImage i).map c.hom := by
    apply (cancel_mono r.hom).mp
    rw [r.inv_hom_id, hr]
    simp only [Category.assoc, ← (inverseImage i).map_comp_assoc,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.inv_hom_id_app]
    rfl
  have hi := congrArg (fun z => z.hom.app F) (directImageCompIso_comp_id i)
  change c.inv ≫ (directImage i).map e.hom ≫ 𝟙 _ = q.hom at hi
  rw [Category.comp_id] at hi
  have hcancel : (directImage i).map e.inv ≫ c.hom ≫ q.hom = 𝟙 _ := by
    rw [← hi, c.hom_inv_id_assoc, ← (directImage i).map_comp,
      e.inv_hom_id, CategoryTheory.Functor.map_id]
  have he := ε.inv.naturality e.inv
  change e.inv ≫ ε.inv.app ((directImage (𝟙 Y)).obj F) =
    ε.inv.app F ≫ (inverseImage i).map ((directImage i).map e.inv) at he
  have hmap : (etaleLowerShriekClopenIso i).hom.app F =
      (etaleLowerShriek i).map e.inv ≫ (etaleLowerShriek i).map r.inv ≫
        (etaleLowerShriekAdjunction i).counit.app ((directImage (𝟙 Y ≫ i)).obj F) ≫ q.hom := by
    simp only [etaleLowerShriekClopenIso, etaleLowerShriekDirectImageIso, e, r, q,
      Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.leftUnitor_inv_app, Functor.associator_hom_app,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
      NatTrans.comp_app, Category.id_comp, asIso_hom, Category.assoc]
    exact congrArg
      (fun a => (etaleLowerShriek i).map e.inv ≫ (etaleLowerShriek i).map r.inv ≫
        (etaleLowerShriekAdjunction i).counit.app ((directImage (𝟙 Y ≫ i)).obj F) ≫ a)
      (Category.id_comp q.hom)
  have hε : (etaleLowerShriekAdjunction i).homEquiv _ _
      ((etaleLowerShriekAdjunction i).counit.app ((directImage (𝟙 Y ≫ i)).obj F)) = 𝟙 _ := by
    rw [← (etaleLowerShriekAdjunction i).homEquiv_symm_id]
    exact Equiv.apply_symm_apply _ _
  change (etaleLowerShriekAdjunction i).homEquiv _ _
      ((etaleLowerShriekClopenIso i).hom.app F) = ε.inv.app F
  rw [hmap, Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  dsimp only [Functor.comp_obj] at hε ⊢
  rw [hε]
  simp only [Category.id_comp]
  rw [hrInv]
  simp only [Category.assoc]
  rw [reassoc_of% he]
  simp only [← (inverseImage i).map_comp]
  rw [hcancel]
  exact (congrArg (fun a => ε.inv.app F ≫ a)
    ((inverseImage i).map_id ((directImage i).obj F))).trans (Category.comp_id (ε.inv.app F))

variable {Y X : Scheme.{u}} (f : Y ⟶ X)

/-- Pullback along the actual diagonal and second projection is the original identity. -/
def etaleDiagonalInverseImageIso :
    𝟭 (AbelianSheaf.{u, u + 1} Y) ≅
      inverseImage (pullback.snd f f) ⋙ inverseImage (pullback.diagonal f) :=
  (inverseImageId Y).symm ≪≫
    eqToIso (congrArg (fun g : Y ⟶ Y => inverseImage g) (pullback.diagonal_snd f).symm) ≪≫
      inverseImageComp (pullback.snd f f) (pullback.diagonal f)

/-- The whole inverse diagonal comparison retains the original composition,
equality transport and identity maps. -/
theorem etaleDiagonalInverseImageIso_inv :
    (etaleDiagonalInverseImageIso f).inv =
      (inverseImageComp (pullback.snd f f) (pullback.diagonal f)).inv ≫
        eqToHom (congrArg (fun a : Y ⟶ Y => inverseImage a) (pullback.diagonal_snd f)) ≫
        (inverseImageId Y).hom := by
  simp only [etaleDiagonalInverseImageIso, Iso.trans_inv, Iso.symm_inv,
    eqToIso.inv, Category.assoc]

/-- Direct image along the actual diagonal and first projection is the original identity. -/
def etaleDiagonalDirectImageIso :
    𝟭 (AbelianSheaf.{u, u + 1} Y) ≅
      directImage (pullback.diagonal f) ⋙ directImage (pullback.fst f f) :=
  (directImageIdIso Y).symm ≪≫
    eqToIso (congrArg (fun g : Y ⟶ Y => directImage g) (pullback.diagonal_fst f).symm) ≪≫
      (directImageCompIso (pullback.fst f f) (pullback.diagonal f)).symm

/-- The whole original direct-image diagonal identity cancels its two pointed
evaluations. The proof specializes the original composition, congruence and
identity laws before evaluating any coefficient. -/
theorem etaleDiagonalDirectImageIso_evaluation
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ Y) :
    Functor.whiskerRight (etaleDiagonalDirectImageIso f).hom
        ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})) ≫
      (Functor.associator (directImage (pullback.diagonal f))
        (directImage (pullback.fst f f))
        ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1}))).hom ≫
      Functor.whiskerLeft (directImage (pullback.diagonal f))
        (pointedDirectImageEvaluationNatTrans (pullback.fst f f)
          (η ≫ pullback.diagonal f) η (by simp [Category.assoc])) ≫
      pointedDirectImageEvaluationNatTrans (pullback.diagonal f) η
        (η ≫ pullback.diagonal f) rfl =
      (Functor.leftUnitor ((pointSmallEtale η).sheafFiber
        (A := AddCommGrpCat.{u + 1}))).hom := by
  let H := (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})
  let e := Functor.isoWhiskerRight (directImageIdIso Y) H
  let q := Functor.isoWhiskerRight
    (eqToIso (congrArg (fun a : Y ⟶ Y => directImage a) (pullback.diagonal_fst f).symm)) H
  let c := Functor.isoWhiskerRight
    (directImageCompIso (pullback.fst f f) (pullback.diagonal f)) H
  have hmap : Functor.whiskerRight (etaleDiagonalDirectImageIso f).hom H =
      e.inv ≫ q.hom ≫ c.inv := by
    simp only [etaleDiagonalDirectImageIso, e, q, c, Iso.trans_hom, Iso.symm_hom,
      Functor.whiskerRight_comp, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv]
  have hcomp := pointedDirectImageEvaluationNatTrans_comp (pullback.fst f f)
    (η ≫ pullback.diagonal f) η (by simp [Category.assoc]) (pullback.diagonal f) η rfl
  have hcongr := pointedDirectImageEvaluationNatTrans_congr
    (pullback.diagonal f ≫ pullback.fst f f) η η (by simp)
    (pullback.diagonal_fst f) (Category.comp_id η)
  have hcongr' : q.inv ≫
      pointedDirectImageEvaluationNatTrans (𝟙 Y) η η (Category.comp_id η) =
    pointedDirectImageEvaluationNatTrans (pullback.diagonal f ≫ pullback.fst f f)
      η η (by simp) := by
    simpa only [q, Functor.isoWhiskerRight_inv, eqToIso.inv] using hcongr
  rw [hmap, ← hcomp, ← hcongr', pointedDirectImageEvaluationNatTrans_id]
  change (e.inv ≫ q.hom ≫ c.inv) ≫ c.hom ≫ q.inv ≫ e.hom ≫
    (Functor.leftUnitor H).hom = (Functor.leftUnitor H).hom
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

/-- The original diagonal inverse-image comparison is marked by the two
original pointed stalk units, as a whole coefficient-family equation. -/
theorem etaleDiagonalInverseImageIso_stalk_unit
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ Y) :
    (Functor.leftUnitor ((pointSmallEtale η).sheafFiber
        (A := AddCommGrpCat.{u + 1}))).hom ≫
      (pointedStalkUnitNatIso (pullback.snd f f) (η ≫ pullback.diagonal f) η
        (by simp [Category.assoc])).hom ≫
      Functor.whiskerLeft (inverseImage (pullback.snd f f))
        (pointedStalkUnitNatIso (pullback.diagonal f) η (η ≫ pullback.diagonal f) rfl).hom =
      Functor.whiskerRight (etaleDiagonalInverseImageIso f).hom
          ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})) ≫
        (Functor.associator (inverseImage (pullback.snd f f))
          (inverseImage (pullback.diagonal f))
          ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1}))).hom := by
  apply NatTrans.ext
  funext F
  simp only [NatTrans.comp_app, Functor.leftUnitor_hom_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    pointedStalkUnitNatIso_hom_app, Category.comp_id]
  let H := (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})
  let e := H.mapIso ((etaleDiagonalInverseImageIso f).app F)
  have hi := NatTrans.congr_app (etaleDiagonalInverseImageIso_inv f) F
  simp only [NatTrans.comp_app, eqToHom_app] at hi
  have h := CoefficientStalkBaseChange.section_stalkUnit η
    (pullback.snd f f) (pullback.diagonal f) (pullback.diagonal_snd f) F
  erw [← hi] at h
  change CoefficientStalkBaseChange.pointedStalkUnit (pullback.snd f f)
      (η ≫ pullback.diagonal f) F η (by simp [Category.assoc]) ≫
    CoefficientStalkBaseChange.pointedStalkUnit (pullback.diagonal f) η
      ((inverseImage (pullback.snd f f)).obj F) (η ≫ pullback.diagonal f) rfl = e.hom
  apply (cancel_mono e.inv).mp
  calc
    _ = 𝟙 _ := by
      dsimp only [e, H, Functor.id_obj] at h ⊢
      simpa only [Functor.mapIso_inv, Iso.app_inv, Category.assoc] using h
    _ = e.hom ≫ e.inv := e.hom_inv_id.symm

variable [Etale f]

/-- The original diagonal pullback identity transposes through the actual open adjunction. -/
def etaleDiagonalLowerShriekMap :
    etaleLowerShriek (pullback.diagonal f) ⟶ inverseImage (pullback.snd f f) where
  app F := ((etaleLowerShriekAdjunction (pullback.diagonal f)).homEquiv _ _).symm
    ((etaleDiagonalInverseImageIso f).hom.app F)
  naturality F G a := by
    apply ((etaleLowerShriekAdjunction (pullback.diagonal f)).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    simpa only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map] using
      (etaleDiagonalInverseImageIso f).hom.naturality a

/-- The whole original diagonal unit, before coefficient or section evaluation. -/
theorem etaleDiagonalLowerShriekMap_unit :
    (etaleLowerShriekAdjunction (pullback.diagonal f)).unit ≫
        Functor.whiskerRight (etaleDiagonalLowerShriekMap f)
          (inverseImage (pullback.diagonal f)) = (etaleDiagonalInverseImageIso f).hom := by
  apply NatTrans.ext
  funext F
  change (etaleLowerShriekAdjunction (pullback.diagonal f)).homEquiv _ _
      ((etaleDiagonalLowerShriekMap f).app F) = (etaleDiagonalInverseImageIso f).hom.app F
  exact Equiv.apply_symm_apply _ _

variable [IsSeparated f]

/-- The whole comparison along the actual clopen diagonal pulls back to the
original inverse-image counit followed by the original diagonal identity.
This is the normalization used for its on-diagonal stalk coordinate. -/
theorem etaleDiagonalLowerShriekMap_inverseImage :
    Functor.whiskerRight
        ((etaleLowerShriekClopenIso (pullback.diagonal f)).inv ≫
          etaleDiagonalLowerShriekMap f) (inverseImage (pullback.diagonal f)) =
      (inverseImageAdjunction (pullback.diagonal f)).counit ≫
        (etaleDiagonalInverseImageIso f).hom :=
  whiskerRight_inv_comp_of_unit
    (inverseImage (pullback.diagonal f)) (etaleLowerShriekClopenIso (pullback.diagonal f))
    (etaleLowerShriekAdjunction (pullback.diagonal f)).unit
    (inverseImageAdjunction (pullback.diagonal f)).counit
    (etaleLowerShriekClopenIso_unit (pullback.diagonal f))
    (etaleDiagonalLowerShriekMap f) (etaleDiagonalInverseImageIso f).hom
    (etaleDiagonalLowerShriekMap_unit f)


open CoefficientStalkBaseChange in
/-- The original diagonal coefficient comparison is normalized at the actual
diagonal point by its original stalk unit and direct-image evaluation. -/
theorem etaleDiagonalLowerShriekMap_pointed_unit
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ Y)
    (F : AbelianSheaf.{u, u + 1} Y) :
    (pointSmallEtale (η ≫ pullback.diagonal f)).sheafFiber.map
        ((etaleLowerShriekClopenIso (pullback.diagonal f)).inv.app F ≫
          (etaleDiagonalLowerShriekMap f).app F) ≫
        pointedStalkUnit (pullback.diagonal f) η ((inverseImage (pullback.snd f f)).obj F)
          (η ≫ pullback.diagonal f) rfl =
      pointedDirectImageEvaluation (pullback.diagonal f) η
          (η ≫ pullback.diagonal f) rfl F ≫
        (pointSmallEtale η).sheafFiber.map ((etaleDiagonalInverseImageIso f).hom.app F) := by
  let H := (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})
  let c := (etaleLowerShriekClopenIso (pullback.diagonal f)).inv.app F ≫
    (etaleDiagonalLowerShriekMap f).app F
  have h := NatTrans.congr_app (etaleDiagonalLowerShriekMap_inverseImage f) F
  change (inverseImage (pullback.diagonal f)).map c =
    (inverseImageAdjunction (pullback.diagonal f)).counit.app F ≫
      (etaleDiagonalInverseImageIso f).hom.app F at h
  rw [pointedStalkUnit_naturality, h, H.map_comp]
  simp only [pointedDirectImageEvaluation, Category.assoc, H]

/-- The original clopen diagonal defines its inclusion into inverse image of direct image. -/
def etaleDirectImageDiagonalMap :
    𝟭 (AbelianSheaf.{u, u + 1} Y) ⟶ directImage f ⋙ inverseImage f :=
  (etaleDiagonalDirectImageIso f).hom ≫
    Functor.whiskerRight (etaleLowerShriekClopenIso (pullback.diagonal f)).inv
      (directImage (pullback.fst f f)) ≫
    Functor.whiskerRight (etaleDiagonalLowerShriekMap f) (directImage (pullback.fst f f)) ≫
    (etaleBaseChangeIso f f).inv

/-- The whole diagonal inclusion, after the original base-change comparison,
is exactly the original direct-image diagonal followed by the diagonal map. -/
theorem etaleDirectImageDiagonalMap_baseChange :
    etaleDirectImageDiagonalMap f ≫ (etaleBaseChangeIso f f).hom =
      (etaleDiagonalDirectImageIso f).hom ≫
        Functor.whiskerRight
          ((etaleLowerShriekClopenIso (pullback.diagonal f)).inv ≫
            etaleDiagonalLowerShriekMap f) (directImage (pullback.fst f f)) := by
  simp only [etaleDirectImageDiagonalMap, Functor.whiskerRight_comp, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The WHOLE on-diagonal coordinate of the original diagonal inclusion is
the original inverse-image identity, with its pointed unit marking retained. -/
theorem etaleDirectImageDiagonalMap_on_diagonal_unit
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ Y) :
    Functor.whiskerRight (etaleDirectImageDiagonalMap f)
        ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})) ≫
      Functor.whiskerRight (etaleBaseChangeIso f f).hom
        ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})) ≫
      (Functor.associator (inverseImage (pullback.snd f f))
        (directImage (pullback.fst f f))
        ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1}))).hom ≫
      Functor.whiskerLeft (inverseImage (pullback.snd f f))
        (pointedDirectImageEvaluationNatTrans (pullback.fst f f)
          (η ≫ pullback.diagonal f) η (by simp [Category.assoc])) ≫
      Functor.whiskerLeft (inverseImage (pullback.snd f f))
        (pointedStalkUnitNatIso (pullback.diagonal f) η (η ≫ pullback.diagonal f) rfl).hom =
      Functor.whiskerRight (etaleDiagonalInverseImageIso f).hom
          ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})) ≫
        (Functor.associator (inverseImage (pullback.snd f f))
          (inverseImage (pullback.diagonal f))
          ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1}))).hom := by
  apply NatTrans.ext
  funext F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, pointedStalkUnitNatIso_hom_app,
    Category.id_comp, Category.comp_id]
  let H := (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})
  let K := (pointSmallEtale (η ≫ pullback.diagonal f)).sheafFiber
    (A := AddCommGrpCat.{u + 1})
  let c := (etaleLowerShriekClopenIso (pullback.diagonal f)).inv.app F ≫
    (etaleDiagonalLowerShriekMap f).app F
  let G := (inverseImage (pullback.snd f f)).obj F
  have hb := NatTrans.congr_app (etaleDirectImageDiagonalMap_baseChange f) F
  change (etaleDirectImageDiagonalMap f).app F ≫ (etaleBaseChangeIso f f).hom.app F =
    (etaleDiagonalDirectImageIso f).hom.app F ≫ (directImage (pullback.fst f f)).map c at hb
  have hn := pointedDirectImageEvaluation_naturality (pullback.fst f f)
    (η ≫ pullback.diagonal f) η (by simp [Category.assoc]) c
  have hu := etaleDiagonalLowerShriekMap_pointed_unit f η F
  change K.map c ≫ CoefficientStalkBaseChange.pointedStalkUnit (pullback.diagonal f)
      η G (η ≫ pullback.diagonal f) rfl =
    pointedDirectImageEvaluation (pullback.diagonal f) η (η ≫ pullback.diagonal f) rfl F ≫
      H.map ((etaleDiagonalInverseImageIso f).hom.app F) at hu
  have he := NatTrans.congr_app (etaleDiagonalDirectImageIso_evaluation f η) F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.leftUnitor_hom_app, Category.id_comp,
    pointedDirectImageEvaluationNatTrans_app] at he
  change H.map ((etaleDirectImageDiagonalMap f).app F) ≫
    H.map ((etaleBaseChangeIso f f).hom.app F) ≫
    pointedDirectImageEvaluation (pullback.fst f f) (η ≫ pullback.diagonal f) η
      (by simp [Category.assoc]) G ≫
    CoefficientStalkBaseChange.pointedStalkUnit (pullback.diagonal f) η G
      (η ≫ pullback.diagonal f) rfl = H.map ((etaleDiagonalInverseImageIso f).hom.app F)
  erw [← Category.assoc, ← H.map_comp, hb, H.map_comp, Category.assoc,
    reassoc_of% hn, hu]
  have hfinal := congrArg
    (fun a => a ≫ H.map ((etaleDiagonalInverseImageIso f).hom.app F)) he
  dsimp only [H, G, Functor.comp_obj, Functor.id_obj] at hfinal ⊢
  simpa only [Category.assoc, Category.id_comp] using hfinal

/-- The WHOLE actual on-diagonal coordinate is the original second-projection
pointed stalk unit. The target coefficient and its marking are unchanged. -/
theorem etaleDirectImageDiagonalMap_on_diagonal
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ Y) :
    Functor.whiskerRight (etaleDirectImageDiagonalMap f)
        ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})) ≫
      Functor.whiskerRight (etaleBaseChangeIso f f).hom
        ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})) ≫
      (Functor.associator (inverseImage (pullback.snd f f))
        (directImage (pullback.fst f f))
        ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1}))).hom ≫
      Functor.whiskerLeft (inverseImage (pullback.snd f f))
        (pointedDirectImageEvaluationNatTrans (pullback.fst f f)
          (η ≫ pullback.diagonal f) η (by simp [Category.assoc])) =
      (Functor.leftUnitor ((pointSmallEtale η).sheafFiber
        (A := AddCommGrpCat.{u + 1}))).hom ≫
        (pointedStalkUnitNatIso (pullback.snd f f) (η ≫ pullback.diagonal f) η
          (by simp [Category.assoc])).hom := by
  apply (cancel_mono
    (Functor.whiskerLeft (inverseImage (pullback.snd f f))
      (pointedStalkUnitNatIso (pullback.diagonal f) η
        (η ≫ pullback.diagonal f) rfl).hom)).mp
  have h := (etaleDirectImageDiagonalMap_on_diagonal_unit f η).trans
    (etaleDiagonalInverseImageIso_stalk_unit f η).symm
  simpa only [Category.assoc] using h

/-- Away from the actual diagonal, every original stalk coordinate of the
diagonal inclusion is zero. The coefficient and stalk carriers are unchanged. -/
theorem etaleDirectImageDiagonalMap_off_diagonal
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (η : Spec (.of Ω) ⟶ Y) (t : Spec (.of Ω) ⟶ pullback f f)
    (ht : t ≫ pullback.fst f f = η)
    (hδ : ∀ ζ : Spec (.of Ω) ⟶ Y, ζ ≫ pullback.diagonal f ≠ t)
    (F : AbelianSheaf.{u, u + 1} Y) :
    (pointSmallEtale η).sheafFiber.map ((etaleDirectImageDiagonalMap f).app F) ≫
      (pointSmallEtale η).sheafFiber.map ((etaleBaseChangeIso f f).hom.app F) ≫
        pointedDirectImageEvaluation (pullback.fst f f) t η ht
          ((inverseImage (pullback.snd f f)).obj F) = 0 := by
  let A := (directImage (pullback.diagonal f)).obj F
  let B := (inverseImage (pullback.snd f f)).obj F
  let c : A ⟶ B := (etaleLowerShriekClopenIso (pullback.diagonal f)).inv.app F ≫
    (etaleDiagonalLowerShriekMap f).app F
  let H := (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})
  let K := (pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})
  have hn : H.map ((directImage (pullback.fst f f)).map c) ≫
      pointedDirectImageEvaluation (pullback.fst f f) t η ht B =
    pointedDirectImageEvaluation (pullback.fst f f) t η ht A ≫ K.map c :=
    pointedDirectImageEvaluation_naturality (pullback.fst f f) t η ht c
  have hz := isZero_closedDirectImage_stalk_of_no_lift (pullback.diagonal f) t hδ F
  have hc : K.map c = 0 := hz.eq_of_src _ _
  have hw := NatTrans.congr_app (etaleDirectImageDiagonalMap_baseChange f) F
  change (etaleDirectImageDiagonalMap f).app F ≫ (etaleBaseChangeIso f f).hom.app F =
    (etaleDiagonalDirectImageIso f).hom.app F ≫ (directImage (pullback.fst f f)).map c at hw
  change H.map ((etaleDirectImageDiagonalMap f).app F) ≫
    H.map ((etaleBaseChangeIso f f).hom.app F) ≫
      pointedDirectImageEvaluation (pullback.fst f f) t η ht B = 0
  rw [← Category.assoc, ← H.map_comp, hw, H.map_comp, Category.assoc, hn, hc,
    comp_zero, comp_zero]

/-- The original lower-shriek comparison is the mate of the actual diagonal inclusion. -/
def etaleLowerShriekToDirectImage : etaleLowerShriek f ⟶ directImage f where
  app F := ((etaleLowerShriekAdjunction f).homEquiv _ _).symm
    ((etaleDirectImageDiagonalMap f).app F)
  naturality F G a := by
    apply ((etaleLowerShriekAdjunction f).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    simpa only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map] using
      (etaleDirectImageDiagonalMap f).naturality a

/-- The whole comparison is normalized by the original lower-shriek unit and diagonal map. -/
theorem etaleLowerShriekToDirectImage_unit :
    (etaleLowerShriekAdjunction f).unit ≫
        Functor.whiskerRight (etaleLowerShriekToDirectImage f) (inverseImage f) =
      etaleDirectImageDiagonalMap f := by
  apply NatTrans.ext
  funext F
  change (etaleLowerShriekAdjunction f).homEquiv _ _
      ((etaleLowerShriekToDirectImage f).app F) = (etaleDirectImageDiagonalMap f).app F
  exact Equiv.apply_symm_apply _ _

/-- Every component uses the original lower-shriek map and original counit. -/
theorem etaleLowerShriekToDirectImage_app (F : AbelianSheaf.{u, u + 1} Y) :
    (etaleLowerShriekToDirectImage f).app F =
      (etaleLowerShriek f).map ((etaleDirectImageDiagonalMap f).app F) ≫
        (etaleLowerShriekAdjunction f).counit.app ((directImage f).obj F) := rfl

/-- The actual diagonal coordinate, written directly in the original finite
direct-image stalk coordinates. -/
theorem etaleDirectImageDiagonalMap_stalk_on_diagonal
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (η : Spec (.of Ω) ⟶ Y) (x : Spec (.of Ω) ⟶ X) (hη : η ≫ f = x)
    (F : AbelianSheaf.{u, u + 1} Y) :
    (pointSmallEtale η).sheafFiber.map ((etaleDirectImageDiagonalMap f).app F) ≫
      (pointedStalkUnitNatIso f η x hη).inv.app ((directImage f).obj F) ≫
      pointedDirectImageEvaluation f η x hη F = 𝟙 _ := by
  let H := (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})
  let e := (pointedStalkUnitNatIso f η x hη).app ((directImage f).obj F)
  let k := (pointedStalkUnitNatIso (pullback.snd f f)
    (η ≫ pullback.diagonal f) η (by simp [Category.assoc])).hom.app F
  have hb := pointedDirectImageEvaluation_baseChange f (pullback.fst f f) f
    (pullback.snd f f) pullback.condition η x (η ≫ pullback.diagonal f) η
    hη hη (by simp [Category.assoc]) (by simp [Category.assoc]) F
  rw [← etaleBaseChangeIso_hom] at hb
  have hd := NatTrans.congr_app (etaleDirectImageDiagonalMap_on_diagonal f η) F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.leftUnitor_hom_app, Category.id_comp,
    pointedDirectImageEvaluationNatTrans_app] at hd
  change H.map ((etaleDirectImageDiagonalMap f).app F) ≫
      H.map ((etaleBaseChangeIso f f).hom.app F) ≫
      pointedDirectImageEvaluation (pullback.fst f f) (η ≫ pullback.diagonal f) η
        (by simp [Category.assoc]) ((inverseImage (pullback.snd f f)).obj F) = k at hd
  simp only [← pointedStalkUnitNatIso_hom_app] at hb
  change e.hom ≫ H.map ((etaleBaseChangeIso f f).hom.app F) ≫
      pointedDirectImageEvaluation (pullback.fst f f) (η ≫ pullback.diagonal f) η
        (by simp [Category.assoc]) ((inverseImage (pullback.snd f f)).obj F) =
    pointedDirectImageEvaluation f η x hη F ≫ k at hb
  change H.map ((etaleDirectImageDiagonalMap f).app F) ≫ e.inv ≫
    pointedDirectImageEvaluation f η x hη F = 𝟙 _
  apply (cancel_mono k).mp
  simp only [Category.assoc, Category.id_comp]
  rw [← hb, e.inv_hom_id_assoc]
  exact hd

/-- Distinct actual lifts give a zero matrix entry for the original diagonal
map in the original finite direct-image stalk coordinates. -/
theorem etaleDirectImageDiagonalMap_stalk_off_diagonal
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (η ζ : Spec (.of Ω) ⟶ Y) (x : Spec (.of Ω) ⟶ X)
    (hη : η ≫ f = x) (hζ : ζ ≫ f = x) (hne : ζ ≠ η)
    (F : AbelianSheaf.{u, u + 1} Y) :
    (pointSmallEtale η).sheafFiber.map ((etaleDirectImageDiagonalMap f).app F) ≫
      (pointedStalkUnitNatIso f η x hη).inv.app ((directImage f).obj F) ≫
      pointedDirectImageEvaluation f ζ x hζ F = 0 := by
  let H := (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})
  let e := (pointedStalkUnitNatIso f η x hη).app ((directImage f).obj F)
  let t : Spec (.of Ω) ⟶ pullback f f := pullback.lift η ζ (hη.trans hζ.symm)
  have ht : t ≫ pullback.fst f f = η := pullback.lift_fst _ _ _
  have hs : t ≫ pullback.snd f f = ζ := pullback.lift_snd _ _ _
  let k := (pointedStalkUnitNatIso (pullback.snd f f) t ζ hs).hom.app F
  have hno : ∀ w : Spec (.of Ω) ⟶ Y, w ≫ pullback.diagonal f ≠ t := by
    intro w hw
    have h₁ : w = η := by
      have h := congrArg (fun a => a ≫ pullback.fst f f) hw
      simpa only [Category.assoc, pullback.diagonal_fst, Category.comp_id, ht] using h
    have h₂ : w = ζ := by
      have h := congrArg (fun a => a ≫ pullback.snd f f) hw
      simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id, hs] using h
    exact hne (h₂.symm.trans h₁)
  have hb := pointedDirectImageEvaluation_baseChange f (pullback.fst f f) f
    (pullback.snd f f) pullback.condition ζ x t η hζ hη ht hs F
  rw [← etaleBaseChangeIso_hom] at hb
  simp only [← pointedStalkUnitNatIso_hom_app] at hb
  change e.hom ≫ H.map ((etaleBaseChangeIso f f).hom.app F) ≫
      pointedDirectImageEvaluation (pullback.fst f f) t η ht
        ((inverseImage (pullback.snd f f)).obj F) =
    pointedDirectImageEvaluation f ζ x hζ F ≫ k at hb
  change H.map ((etaleDirectImageDiagonalMap f).app F) ≫ e.inv ≫
    pointedDirectImageEvaluation f ζ x hζ F = 0
  apply (cancel_mono k).mp
  simp only [Category.assoc, zero_comp]
  rw [← hb, e.inv_hom_id_assoc]
  exact etaleDirectImageDiagonalMap_off_diagonal f η t ht hno F

section MatrixTriangles

variable {C : Type uC} [Category.{vC} C] [Preadditive C]

private theorem row_sum_of_matrix {A B D E : C} {I : Type*} [Fintype I]
    (a : A ⟶ B) (b : B ⟶ D) (q : I → (D ⟶ E)) (r : A ⟶ E)
    (i₀ : I) (h₀ : a ≫ b ≫ q i₀ = r)
    (hz : ∀ i ≠ i₀, a ≫ b ≫ q i = 0) :
    a ≫ b ≫ ∑ i, q i = r := by
  classical
  simp only [Preadditive.comp_sum]
  rw [Finset.sum_eq_single i₀]
  · exact h₀
  · intro i _ hi
    exact hz i hi
  · simp

omit [Preadditive C] in
private theorem row_on_of_matrix {A B D E : C}
    {a : A ⟶ B} {b : B ⟶ D} {v : D ⟶ A}
    (r : A ⟶ E) (h : a ≫ b ≫ v = 𝟙 A) :
    a ≫ b ≫ (v ≫ r) = r := by
  simpa only [Category.assoc, Category.id_comp] using congrArg (fun z => z ≫ r) h

private theorem row_off_of_matrix {A B D E F : C}
    {a : A ⟶ B} {b : B ⟶ D} {v : D ⟶ E}
    (r : E ⟶ F) (h : a ≫ b ≫ v = 0) :
    a ≫ b ≫ (v ≫ r) = 0 := by
  simpa only [Category.assoc, zero_comp] using congrArg (fun z => z ≫ r) h

omit [Preadditive C] in
private theorem right_triangle_of_raw_row {A B D E : C}
    {a : A ⟶ B} {vh : D ⟶ B} {vi : B ⟶ D}
    {eh : E ⟶ A} {ei : A ⟶ E} {t : D ⟶ E} {m : B ⟶ A}
    (hv : vi ≫ vh = 𝟙 B) (he : ei ≫ eh = 𝟙 A)
    (hn : vh ≫ m = t ≫ eh) (hs : a ≫ vi ≫ t = ei) : a ≫ m = 𝟙 A := by
  calc
    a ≫ m = a ≫ vi ≫ vh ≫ m := by
      rw [← Category.assoc vi vh m, hv, Category.id_comp]
    _ = a ≫ vi ≫ t ≫ eh := by rw [hn]
    _ = ei ≫ eh := by rw [reassoc_of% hs]
    _ = 𝟙 A := he

private theorem column_sum_of_matrix {A B E : C} {I : Type*} [Fintype I]
    (a : A ⟶ B) (q : I → (B ⟶ A)) (b : A ⟶ E) (i₀ : I)
    (h₀ : a ≫ q i₀ ≫ b = b)
    (hz : ∀ i ≠ i₀, a ≫ q i ≫ b = 0) :
    a ≫ (∑ i, q i) ≫ b = b := by
  classical
  simp only [Preadditive.comp_sum, Preadditive.sum_comp]
  rw [Finset.sum_eq_single i₀]
  · exact h₀
  · intro i _ hi
    exact hz i hi
  · simp

omit [Preadditive C] in
private theorem column_on_of_matrix {A B T D : C}
    {a : A ⟶ B} {v : B ⟶ T} {b : A ⟶ D} {δ : D ⟶ T} {u : T ⟶ A}
    (hn : a ≫ v = b ≫ δ) (hδ : δ ≫ u ≫ b = 𝟙 D) :
    a ≫ (v ≫ u) ≫ b = b := by
  simp only [Category.assoc]
  rw [reassoc_of% hn, hδ, Category.comp_id]

private theorem column_off_of_matrix {A B T D E : C}
    {a : A ⟶ B} {v : B ⟶ T} {b : A ⟶ D} {δ : D ⟶ T}
    {u : T ⟶ A} {z : A ⟶ E}
    (hn : a ≫ v = b ≫ δ) (hδ : δ ≫ u ≫ z = 0) :
    a ≫ (v ≫ u) ≫ z = 0 := by
  simp only [Category.assoc]
  rw [reassoc_of% hn, hδ, comp_zero]

private theorem right_triangle_of_trace {A B D E : C} {J : Type*} [Fintype J]
    {a : A ⟶ B} {vh : D ⟶ B} {vi : B ⟶ D}
    {eh : E ⟶ A} {ei : A ⟶ E} {t : D ⟶ E} {m : B ⟶ A}
    {q : J → (D ⟶ E)}
    (hv : vi ≫ vh = 𝟙 B) (he : ei ≫ eh = 𝟙 A)
    (hn : vh ≫ m = t ≫ eh) (ht : t = ∑ j, q j)
    (j₀ : J) (h₀ : a ≫ vi ≫ q j₀ = ei)
    (hz : ∀ j ≠ j₀, a ≫ vi ≫ q j = 0) : a ≫ m = 𝟙 A := by
  apply right_triangle_of_raw_row hv he hn
  rw [ht]
  exact row_sum_of_matrix a vi q ei j₀ h₀ hz

private theorem column_sum_of_trace {A B E : C} {J : Type*} [Fintype J]
    {a : A ⟶ B} {t : B ⟶ A} {q : J → (B ⟶ A)} {b : A ⟶ E}
    (ht : t = ∑ j, q j) (j₀ : J) (h₀ : a ≫ q j₀ ≫ b = b)
    (hz : ∀ j ≠ j₀, a ≫ q j ≫ b = 0) : a ≫ t ≫ b = b := by
  rw [ht]
  exact column_sum_of_matrix a q b j₀ h₀ hz

end MatrixTriangles

section FiniteEtaleTriangles

attribute [local instance] Fintype.ofFinite

variable {S : Scheme.{u}} (Z : Scheme.FiniteEtale S)
  (d : ℕ) (hd : ∀ x : S, Z.obj.hom.finrank x = d)

include d hd

/-- Component evaluation of the proved whole canonical stalk-SUM law. -/
theorem finiteEtaleSheafTrace_stalk_app
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ S)
    (G : AbelianSheaf.{u, u + 1} S) :
    (pointSmallEtale x).sheafFiber.map ((finiteEtaleSheafTrace Z d hd).app G) =
      ∑ y : Scheme.FiniteEtale.Fiber x Z,
        pointedDirectImageEvaluation Z.obj.hom y.left x (Over.w y)
            ((inverseImage Z.obj.hom).obj G) ≫
          (pointedStalkUnitNatIso Z.obj.hom y.left x (Over.w y)).inv.app G := by
  have h := NatTrans.congr_app (finiteEtaleSheafTrace_stalk x Z d hd) G
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    NatTrans.app_sum, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Category.id_comp, pointedDirectImageEvaluationNatTrans_app] at h
  dsimp only [Functor.comp_obj, Functor.id_obj] at h ⊢
  simpa only [Category.comp_id] using h

/-- The original diagonal and canonical SUM satisfy the inverse-image triangle
at each original geometric stalk. -/
theorem finiteEtaleDirectImage_right_triangle_stalk
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (η : Spec (.of Ω) ⟶ Z.obj.left)
    (G : AbelianSheaf.{u, u + 1} S) :
    (pointSmallEtale η).sheafFiber.map
        ((etaleDirectImageDiagonalMap Z.obj.hom).app ((inverseImage Z.obj.hom).obj G)) ≫
      (pointSmallEtale η).sheafFiber.map
        ((inverseImage Z.obj.hom).map ((finiteEtaleSheafTrace Z d hd).app G)) = 𝟙 _ := by
  classical
  have ht := finiteEtaleSheafTrace_stalk_app Z d hd (η ≫ Z.obj.hom) G
  have hn := ((pointedStalkUnitNatIso Z.obj.hom η (η ≫ Z.obj.hom) rfl).hom.naturality
    ((finiteEtaleSheafTrace Z d hd).app G)).symm
  have hv := (pointedStalkUnitNatIso Z.obj.hom η (η ≫ Z.obj.hom) rfl).inv_hom_id_app
    ((directImage Z.obj.hom).obj ((inverseImage Z.obj.hom).obj G))
  have he := (pointedStalkUnitNatIso Z.obj.hom η (η ≫ Z.obj.hom) rfl).inv_hom_id_app G
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map] at hn hv he
  refine right_triangle_of_trace hv he hn ht (Over.homMk η rfl) ?_ ?_
  · have h := etaleDirectImageDiagonalMap_stalk_on_diagonal Z.obj.hom η
      (η ≫ Z.obj.hom) rfl ((inverseImage Z.obj.hom).obj G)
    exact row_on_of_matrix
      ((pointedStalkUnitNatIso Z.obj.hom η (η ≫ Z.obj.hom) rfl).inv.app G) h
  · intro y hy
    have hne : y.left ≠ η := by
      intro h
      exact hy (Over.OverMorphism.ext h)
    have h := etaleDirectImageDiagonalMap_stalk_off_diagonal Z.obj.hom η y.left
      (η ≫ Z.obj.hom) rfl (Over.w y) hne ((inverseImage Z.obj.hom).obj G)
    exact row_off_of_matrix
      ((pointedStalkUnitNatIso Z.obj.hom y.left (η ≫ Z.obj.hom) (Over.w y)).inv.app G) h

/-- The whole original inverse-image triangle, detected on the original
jointly faithful geometric stalks. -/
theorem finiteEtaleDirectImage_right_triangle
    (G : AbelianSheaf.{u, u + 1} S) :
    (etaleDirectImageDiagonalMap Z.obj.hom).app ((inverseImage Z.obj.hom).obj G) ≫
      (inverseImage Z.obj.hom).map ((finiteEtaleSheafTrace Z d hd).app G) = 𝟙 _ := by
  have (x : FibrewiseClosed.Index (𝟙 Z.obj.left)) : PreservesFiniteLimits
      ((pointSmallEtale (FibrewiseClosed.geometricPoint x.val)).sheafFiber
        (A := AddCommGrpCat.{u + 1})) :=
    preservesFiniteLimits_of_natIso
      (StalkUniverse.sheafFiberIso (FibrewiseClosed.geometricPoint x.val))
  apply (StalkUniverse.originalStalks_jointlyReflectIsomorphisms
    (𝟙 Z.obj.left)).jointlyFaithful.map_injective
  intro x
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  exact finiteEtaleDirectImage_right_triangle_stalk Z d hd
    (FibrewiseClosed.geometricPoint x.val) G

/-- The original direct-image triangle in each original stalk and each of its
actual pointed evaluation coordinates. -/
theorem finiteEtaleDirectImage_left_triangle_stalk_coordinate
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S)
    (ζ : Spec (.of Ω) ⟶ Z.obj.left) (hζ : ζ ≫ Z.obj.hom = x)
    (F : AbelianSheaf.{u, u + 1} Z.obj.left) :
    (pointSmallEtale x).sheafFiber.map
        ((directImage Z.obj.hom).map ((etaleDirectImageDiagonalMap Z.obj.hom).app F)) ≫
      (pointSmallEtale x).sheafFiber.map
        ((finiteEtaleSheafTrace Z d hd).app ((directImage Z.obj.hom).obj F)) ≫
      pointedDirectImageEvaluation Z.obj.hom ζ x hζ F =
        pointedDirectImageEvaluation Z.obj.hom ζ x hζ F := by
  classical
  have ht := finiteEtaleSheafTrace_stalk_app Z d hd x ((directImage Z.obj.hom).obj F)
  refine column_sum_of_trace ht (Over.homMk ζ hζ) ?_ ?_
  · have hn := pointedDirectImageEvaluation_naturality Z.obj.hom ζ x hζ
      ((etaleDirectImageDiagonalMap Z.obj.hom).app F)
    have hδ := etaleDirectImageDiagonalMap_stalk_on_diagonal Z.obj.hom ζ x hζ F
    exact column_on_of_matrix hn hδ
  · intro y hy
    have hne : ζ ≠ y.left := by
      intro h
      exact hy (Over.OverMorphism.ext h.symm)
    have hn := pointedDirectImageEvaluation_naturality Z.obj.hom y.left x (Over.w y)
      ((etaleDirectImageDiagonalMap Z.obj.hom).app F)
    have hδ := etaleDirectImageDiagonalMap_stalk_off_diagonal Z.obj.hom y.left ζ x
      (Over.w y) hζ hne F
    exact column_off_of_matrix hn hδ

/-- The whole original direct-image triangle, using the existing finite stalk
isomorphism with its original pointed evaluation coordinates. -/
theorem finiteEtaleDirectImage_left_triangle
    (F : AbelianSheaf.{u, u + 1} Z.obj.left) :
    (directImage Z.obj.hom).map ((etaleDirectImageDiagonalMap Z.obj.hom).app F) ≫
      (finiteEtaleSheafTrace Z d hd).app ((directImage Z.obj.hom).obj F) = 𝟙 _ := by
  have (x : FibrewiseClosed.Index (𝟙 S)) : PreservesFiniteLimits
      ((pointSmallEtale (FibrewiseClosed.geometricPoint x.val)).sheafFiber
        (A := AddCommGrpCat.{u + 1})) :=
    preservesFiniteLimits_of_natIso
      (StalkUniverse.sheafFiberIso (FibrewiseClosed.geometricPoint x.val))
  apply (StalkUniverse.originalStalks_jointlyReflectIsomorphisms
    (𝟙 S)).jointlyFaithful.map_injective
  intro z
  let x := FibrewiseClosed.geometricPoint z.val
  let H := (pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  apply (cancel_mono (Finite.finiteDirectImageEvaluationIso Z.obj.hom x F).hom).mp
  apply ConcreteCategory.hom_ext
  intro a
  funext y
  change pointedDirectImageEvaluation Z.obj.hom y.val x y.property F
      ((H.map ((directImage Z.obj.hom).map ((etaleDirectImageDiagonalMap Z.obj.hom).app F)) ≫
        H.map ((finiteEtaleSheafTrace Z d hd).app ((directImage Z.obj.hom).obj F))) a) =
    pointedDirectImageEvaluation Z.obj.hom y.val x y.property F a
  exact ConcreteCategory.congr_hom
    (finiteEtaleDirectImage_left_triangle_stalk_coordinate Z d hd x y.val y.property F) a

/-- Finite direct image is left adjoint to original inverse image with the
proved original diagonal as unit and the original canonical SUM as counit. -/
def finiteEtaleDirectImageAdjunction : directImage Z.obj.hom ⊣ inverseImage Z.obj.hom where
  unit := etaleDirectImageDiagonalMap Z.obj.hom
  counit := finiteEtaleSheafTrace Z d hd
  left_triangle_components := finiteEtaleDirectImage_left_triangle Z d hd
  right_triangle_components := finiteEtaleDirectImage_right_triangle Z d hd

/-- Left-adjoint uniqueness identifies its isomorphism with the existing
lower-shriek comparison, because their actual original unit mates coincide. -/
theorem finiteEtaleLowerShriekToDirectImage_eq_leftAdjointUniq :
    etaleLowerShriekToDirectImage Z.obj.hom =
      ((etaleLowerShriekAdjunction Z.obj.hom).leftAdjointUniq
        (finiteEtaleDirectImageAdjunction Z d hd)).hom := by
  apply NatTrans.ext
  funext F
  apply ((etaleLowerShriekAdjunction Z.obj.hom).homEquiv _ _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  exact Equiv.apply_symm_apply _ _

/-- The existing original comparison is invertible for a genuine finite-etale
map of the specified actual rank, without any coefficient or coprimality restriction. -/
theorem finiteEtaleLowerShriekToDirectImage_isIso :
    IsIso (etaleLowerShriekToDirectImage Z.obj.hom) := by
  rw [finiteEtaleLowerShriekToDirectImage_eq_leftAdjointUniq Z d hd]
  infer_instance

/-- The isomorphism is the existing original comparison, with no new chosen map. -/
def finiteEtaleLowerShriekDirectImageIso :
    etaleLowerShriek Z.obj.hom ≅ directImage Z.obj.hom := by
  letI := finiteEtaleLowerShriekToDirectImage_isIso Z d hd
  exact asIso (etaleLowerShriekToDirectImage Z.obj.hom)

@[simp] theorem finiteEtaleLowerShriekDirectImageIso_hom :
    (finiteEtaleLowerShriekDirectImageIso Z d hd).hom =
      etaleLowerShriekToDirectImage Z.obj.hom := rfl

/-- The same original comparison carries the existing lower-shriek counit to
the original canonical finite-etale SUM, as a whole coefficient-family law. -/
theorem finiteEtaleLowerShriekToDirectImage_counit :
    Functor.whiskerLeft (inverseImage Z.obj.hom)
        (etaleLowerShriekToDirectImage Z.obj.hom) ≫
      finiteEtaleSheafTrace Z d hd = (etaleLowerShriekAdjunction Z.obj.hom).counit := by
  rw [finiteEtaleLowerShriekToDirectImage_eq_leftAdjointUniq Z d hd]
  exact Adjunction.leftAdjointUniq_hom_counit
    (etaleLowerShriekAdjunction Z.obj.hom) (finiteEtaleDirectImageAdjunction Z d hd)

end FiniteEtaleTriangles

end AlgebraicGeometry.Scheme.EtaleCohomology
