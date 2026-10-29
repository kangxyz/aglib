/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.Cone

/-! # The original right-tail cocone from an actual adjunction cone

The actual adjoints of coefficient-colimit injections give legs on the original
right-adjoint tail. Their naturality follows from the system transitions and
the structural composition law of the supplied cone. No sheaf or continuity
property, and no colimit property of the right-tail cocone, is assumed.
-/

@[expose] public noncomputable section

namespace CategoryTheory.InjectiveSystem.AdjunctionData.Cone

open Limits

universe uI vI uA vA uB vB

variable {I : Type uI} [Category.{vI} I]
  {A : I → Type uA} [∀ i, Category.{vA} (A i)]
  {D : AdjunctionData A} {B : Type uB} [Category.{vB} B]
  (P : D.Cone B) (F : System D) [HasColimit (P.coefficientFunctor F)]

/-- The literal right image of the original adjunct leg, followed by the
original structural right triangle. -/
def rightTailLeg {i j : I} (a : i ⟶ j) :
    (D.right a).obj (F.obj j) ⟶ (P.right i).obj (colimit (P.coefficientFunctor F)) :=
  (D.right a).map (P.adjointLeg F j) ≫
    (P.rightTriangle a).hom.app (colimit (P.coefficientFunctor F))

/-- Structural right-comparison composition and actual adjunct naturality
give the whole right-tail leg equation. -/
theorem rightTailLeg_step {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    System.rightStep D F a b ≫ P.rightTailLeg F (a ≫ b) = P.rightTailLeg F a := by
  let K := colimit (P.coefficientFunctor F)
  have hn : (D.compIso a b).inv.app (F.obj k) ≫
      (D.right (a ≫ b)).map (P.adjointLeg F k) =
        (D.right a).map ((D.right b).map (P.adjointLeg F k)) ≫
          (D.compIso a b).inv.app ((P.right k).obj K) :=
    ((D.compIso a b).inv.naturality (P.adjointLeg F k)).symm
  calc
    System.rightStep D F a b ≫ P.rightTailLeg F (a ≫ b) =
        (D.right a).map (F.map b) ≫
          ((D.compIso a b).inv.app (F.obj k) ≫
            (D.right (a ≫ b)).map (P.adjointLeg F k)) ≫
              (P.rightTriangle (a ≫ b)).hom.app K := by
      simp only [System.rightStep, rightTailLeg, Category.assoc, K]
    _ = (D.right a).map (F.map b) ≫
        ((D.right a).map ((D.right b).map (P.adjointLeg F k)) ≫
          (D.compIso a b).inv.app ((P.right k).obj K)) ≫
            (P.rightTriangle (a ≫ b)).hom.app K :=
      congrArg (fun f => (D.right a).map (F.map b) ≫ f ≫
        (P.rightTriangle (a ≫ b)).hom.app K) hn
    _ = ((D.right a).map (F.map b) ≫
        (D.right a).map ((D.right b).map (P.adjointLeg F k))) ≫
          ((D.compIso a b).inv.app ((P.right k).obj K) ≫
            (P.rightTriangle (a ≫ b)).hom.app K) := by
      simp only [Category.assoc]
    _ = ((D.right a).map (F.map b) ≫
        (D.right a).map ((D.right b).map (P.adjointLeg F k))) ≫
          ((D.right a).map ((P.rightTriangle b).hom.app K) ≫
            (P.rightTriangle a).hom.app K) :=
      congrArg (fun f => ((D.right a).map (F.map b) ≫
        (D.right a).map ((D.right b).map (P.adjointLeg F k))) ≫ f)
        (P.right_comp a b K).symm
    _ = (D.right a).map (F.map b ≫ (D.right b).map (P.adjointLeg F k) ≫
        (P.rightTriangle b).hom.app K) ≫ (P.rightTriangle a).hom.app K := by
      simp only [Functor.map_comp, Category.assoc]
    _ = P.rightTailLeg F a := by
      rw [← P.adjointLeg_naturality F b]
      rfl

/-- The same leg equation retains a supplied equality of actual index arrows. -/
theorem rightTailLeg_transition {i j k : I}
    (a : i ⟶ j) (b : j ⟶ k) (t : i ⟶ k) (h : a ≫ b = t) :
    System.rightTailTransition D F a b t h ≫ P.rightTailLeg F t =
      P.rightTailLeg F a := by
  subst t
  simpa only [System.rightTailTransition, eqToHom_refl, Category.comp_id] using
    P.rightTailLeg_step F a b

/-- The complete cocone on the original fixed-stage right-adjoint tail. -/
def rightTailCocone (hD : D.Coherent) (i : I) : Cocone (System.rightTail D hD F i) where
  pt := (P.right i).obj (colimit (P.coefficientFunctor F))
  ι := {
    app := fun a => P.rightTailLeg F a.hom
    naturality := fun a b f =>
      (P.rightTailLeg_transition F a.hom f.right b.hom (Under.w f)).trans
        (Category.comp_id (P.rightTailLeg F a.hom)).symm }

@[simp]
theorem rightTailCocone_ι_app (hD : D.Coherent) (i : I) (a : Under i) :
    (P.rightTailCocone F hD i).ι.app a =
      (D.right a.hom).map (P.adjointLeg F a.right) ≫
        (P.rightTriangle a.hom).hom.app (colimit (P.coefficientFunctor F)) := rfl

end CategoryTheory.InjectiveSystem.AdjunctionData.Cone
