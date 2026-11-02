/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.LowerShriekUnderlying

/-!
# Original lower-shriek exchange over an invertible right mate

The given inverse-image square has its original adjunction mate. When that
mate and the source lower-shriek unit are invertible, they construct the
restriction comparison. Its mate under the target lower-shriek adjunction
is the exchange map. The whole normalizations and the coefficient-unit law
are proved over independent categories before any geometric specialization.
-/

@[expose] public noncomputable section

open CategoryTheory

universe uX vX uY vY uU vU uV vV

namespace CategoryTheory.Adjunction.LowerShriekExchange

variable {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
  {U : Type uU} [Category.{vU} U] {V : Type uV} [Category.{vV} V]
  {P : X ⥤ Y} {RP : Y ⥤ X} {F : U ⥤ V} {RF : V ⥤ U}
  {I : X ⥤ U} {LI : U ⥤ X} {J : Y ⥤ V} {LJ : V ⥤ Y}
  (ap : P ⊣ RP) (af : F ⊣ RF) (ai : LI ⊣ I) (aj : LJ ⊣ J)
  (α : I ⋙ F ⟶ P ⋙ J)

/-- The original right-adjoint exchange, constructed by the native mate correspondence. -/
def rightMap : RP ⋙ I ⟶ J ⋙ RF :=
  (mateEquiv ap af (TwoSquare.mk I P F J α)).natTrans

/-- The entire original right mate is normalized by the two original units. -/
theorem rightMap_unit :
    (Functor.leftUnitor I).inv ≫ Functor.whiskerRight ap.unit I ≫
        (Functor.associator P RP I).hom ≫ Functor.whiskerLeft P (rightMap ap af α) =
      (Functor.rightUnitor I).inv ≫ Functor.whiskerLeft I af.unit ≫
        (Functor.associator I F RF).inv ≫ Functor.whiskerRight α RF ≫
        (Functor.associator P J RF).hom := by
  apply NatTrans.ext
  funext A
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id]
  exact unit_mateEquiv ap af (TwoSquare.mk I P F J α) A

/-- The entire original right mate is normalized by the two original counits. -/
theorem rightMap_counit :
    Functor.whiskerRight (rightMap ap af α) F ≫ (Functor.associator J RF F).hom ≫
        Functor.whiskerLeft J af.counit ≫ (Functor.rightUnitor J).hom =
      (Functor.associator RP I F).hom ≫ Functor.whiskerLeft RP α ≫
        (Functor.associator RP P J).inv ≫ Functor.whiskerRight ap.counit J ≫
        (Functor.leftUnitor J).hom := by
  apply NatTrans.ext
  funext A
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id]
  exact mateEquiv_counit ap af (TwoSquare.mk I P F J α) A

/-- Evaluating the whole right-unit law retains the original mate and square. -/
theorem rightMap_unit_app (A : X) :
    I.map (ap.unit.app A) ≫ (rightMap ap af α).app (P.obj A) =
      af.unit.app (I.obj A) ≫ RF.map (α.app A) :=
  unit_mateEquiv ap af (TwoSquare.mk I P F J α) A

variable (β : RP ⋙ I ⟶ J ⋙ RF) [IsIso β] [IsIso aj.unit]

/-- Original restriction comparison from the invertible right mate and inverse source unit. -/
def restrictionIso : (LJ ⋙ RP) ⋙ I ≅ RF :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft LJ (asIso β) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso aj.unit).symm RF ≪≫ Functor.leftUnitor RF

/-- The whole inverse restriction comparison followed by right exchange is
the original source unit, with the actual associators retained. -/
theorem restrictionIso_inv_rightMap :
    (restrictionIso aj β).inv ≫ (Functor.associator LJ RP I).hom ≫
        Functor.whiskerLeft LJ β =
      (Functor.leftUnitor RF).inv ≫ Functor.whiskerRight aj.unit RF ≫
        (Functor.associator LJ J RF).hom := by
  let a := Functor.associator LJ RP I ≪≫
    Functor.isoWhiskerLeft LJ (asIso β)
  let b := (Functor.associator LJ J RF).symm ≪≫
    Functor.isoWhiskerRight (asIso aj.unit).symm RF ≪≫ Functor.leftUnitor RF
  have he : (restrictionIso aj β).hom = a.hom ≫ b.hom := by
    simp only [restrictionIso, a, b, Iso.trans_hom, Category.assoc]
  have hi := Iso.inv_comp_of_hom_eq_comp (restrictionIso aj β) a b he
  simpa only [a, b, Iso.trans_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_inv, asIso_hom,
    Category.assoc] using hi

/-- Component evaluation of the whole restriction normalization. -/
theorem restrictionIso_inv_rightMap_app (D : V) :
    (restrictionIso aj β).inv.app D ≫ β.app (LJ.obj D) =
      RF.map (aj.unit.app D) := by
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.leftUnitor_inv_app,
    Category.id_comp, Category.comp_id] using
      NatTrans.congr_app (restrictionIso_inv_rightMap aj β) D

/-- Original lower-shriek exchange, transposed from the constructed restriction comparison. -/
def comparison : RF ⋙ LI ⟶ LJ ⋙ RP where
  app D := (ai.homEquiv _ _).symm ((restrictionIso aj β).inv.app D)
  naturality D E a := by
    dsimp only [Functor.comp_map]
    apply (ai.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    simpa only [Functor.comp_map] using (restrictionIso aj β).inv.naturality a

/-- The whole comparison has precisely the original target lower-shriek unit. -/
theorem comparison_unit :
    (Functor.rightUnitor RF).inv ≫ Functor.whiskerLeft RF ai.unit ≫
        (Functor.associator RF LI I).inv ≫
        Functor.whiskerRight (comparison ai aj β) I =
      (restrictionIso aj β).inv := by
  apply NatTrans.ext
  funext D
  simp only [NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Category.id_comp]
  change ai.homEquiv _ _ ((comparison ai aj β).app D) =
    (restrictionIso aj β).inv.app D
  exact Equiv.apply_symm_apply _ _

/-- The original comparison component is lower shriek of restriction followed by counit. -/
theorem comparison_app (D : V) :
    (comparison ai aj β).app D =
      LI.map ((restrictionIso aj β).inv.app D) ≫ ai.counit.app (RP.obj (LJ.obj D)) := rfl

/-- The complete compatible-coefficient unit square for the constructed original
exchange. The only coefficient hypothesis is its literal inverse-image square. -/
theorem coefficient_unit {A : X} {B : U} {C : Y} {D : V}
    (a : I.obj A ≅ B) (b : P.obj A ≅ C) (c : F.obj B ≅ D) (e : J.obj C ≅ D)
    (hcoeff : F.map a.inv ≫ α.app A ≫ J.map b.hom = c.hom ≫ e.inv)
    (hβ : β = rightMap ap af α) :
    LI.map (af.unit.app B) ≫ LI.map (RF.map c.hom) ≫
        (comparison ai aj β).app D ≫ RP.map (LJ.map e.inv ≫ aj.counit.app C) =
      (LI.map a.inv ≫ ai.counit.app A) ≫ ap.unit.app A ≫ RP.map b.hom := by
  let exta : LI.obj B ⟶ A := LI.map a.inv ≫ ai.counit.app A
  let exte : LJ.obj D ⟶ C := LJ.map e.inv ≫ aj.counit.app C
  have ha : ai.homEquiv _ _ exta = a.inv := Equiv.apply_symm_apply _ _
  have he : aj.unit.app D ≫ J.map exte = e.inv := by
    change aj.homEquiv _ _ ((aj.homEquiv _ _).symm e.inv) = e.inv
    exact Equiv.apply_symm_apply _ _
  have hκ : ai.homEquiv _ _ ((comparison ai aj β).app D) =
      (restrictionIso aj β).inv.app D := Equiv.apply_symm_apply _ _
  have hβe := β.naturality exte
  change I.map (RP.map exte) ≫ β.app C =
    β.app (LJ.obj D) ≫ RF.map (J.map exte) at hβe
  have hL : (restrictionIso aj β).inv.app D ≫ I.map (RP.map exte) ≫
      β.app C = RF.map e.inv := by
    rw [hβe, ← Category.assoc, restrictionIso_inv_rightMap_app, ← RF.map_comp, he]
  have hβb := β.naturality b.hom
  change I.map (RP.map b.hom) ≫ β.app C =
    β.app (P.obj A) ≫ RF.map (J.map b.hom) at hβb
  have hu := rightMap_unit_app ap af α A
  rw [← hβ] at hu
  have hη := af.unit.naturality a.inv
  change a.inv ≫ af.unit.app (I.obj A) = af.unit.app B ≫ RF.map (F.map a.inv) at hη
  have hR : a.inv ≫ I.map (ap.unit.app A) ≫ I.map (RP.map b.hom) ≫
      β.app C = af.unit.app B ≫ RF.map (F.map a.inv ≫ α.app A ≫ J.map b.hom) := by
    rw [hβb, reassoc_of% hu, ← Category.assoc a.inv (af.unit.app (I.obj A)), hη]
    simp only [Functor.map_comp, Category.assoc]
  apply (ai.homEquiv _ _).injective
  change ai.homEquiv _ _ (LI.map (af.unit.app B) ≫ LI.map (RF.map c.hom) ≫
      (comparison ai aj β).app D ≫ RP.map exte) =
    ai.homEquiv _ _ (exta ≫ ap.unit.app A ≫ RP.map b.hom)
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right, hκ, Adjunction.homEquiv_naturality_right, ha]
  conv_rhs => rw [I.map_comp]
  apply (cancel_mono (β.app C)).mp
  simp only [Category.assoc]
  rw [hL, hR, hcoeff, Functor.map_comp]

end CategoryTheory.Adjunction.LowerShriekExchange
