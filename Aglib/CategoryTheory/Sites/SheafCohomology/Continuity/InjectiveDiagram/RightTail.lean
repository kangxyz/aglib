/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.SystemCoherence
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Actual right-adjoint tails of compatible systems

At a fixed stage, push each later coefficient back by its original right
adjoint. The existing system transitions and comparison isomorphisms give
an ordinary functor on the original under category. Its terms are injective
when the original later coefficients are injective, by the genuine adjunction
and preservation of monomorphisms by its left adjoint.

No colimit or continuity property of this tail is assumed or asserted.
-/

@[expose] public noncomputable section

namespace CategoryTheory.InjectiveSystem

universe uI vI uA vA

variable {I : Type uI} [Category.{vI} I]
  {A : I → Type uA} [∀ i, Category.{vA} (A i)]
  (D : AdjunctionData A) (hD : D.Coherent) (F : System D)

include hD in
/-- Inverse associativity retains the actual equality transport between
parenthesizations in the indexing category. -/
theorem AdjunctionData.Coherent.inv_assoc {i j k l : I}
    (a : i ⟶ j) (b : j ⟶ k) (c : k ⟶ l) (T : A l) :
    (D.compIso a b).inv.app ((D.right c).obj T) ≫
        (D.compIso (a ≫ b) c).inv.app T =
      (D.right a).map ((D.compIso b c).inv.app T) ≫
        (D.compIso a (b ≫ c)).inv.app T ≫
          eqToHom (congrArg (fun d => (D.right d).obj T) (Category.assoc a b c).symm) := by
  have h := IsIso.inv_eq_inv.mpr (hD.assoc a b c T)
  simpa only [IsIso.inv_comp, NatIso.inv_hom_app, ← Functor.map_inv,
    inv_eqToHom, Category.assoc] using h

/-- The original transition followed by the inverse composition comparison. -/
def System.rightStep {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    (D.right a).obj (F.obj j) ⟶ (D.right (a ≫ b)).obj (F.obj k) :=
  (D.right a).map (F.map b) ≫ (D.compIso a b).inv.app (F.obj k)

/-- The system composition law in its actual inverse-comparison direction. -/
theorem System.map_comp_inv {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    F.map a ≫ (D.right a).map (F.map b) ≫ (D.compIso a b).inv.app (F.obj k) =
      F.map (a ≫ b) := by
  rw [← Category.assoc, ← F.map_comp, Category.assoc, Iso.hom_inv_id_app,
    Category.comp_id]

include hD in
/-- Identity of the right-adjoint tail, with its original index transport. -/
theorem System.rightStep_id {i j : I} (a : i ⟶ j) :
    System.rightStep D F a (𝟙 j) ≫
        eqToHom (congrArg (fun b => (D.right b).obj (F.obj j)) (Category.comp_id a)) =
      𝟙 ((D.right a).obj (F.obj j)) := by
  have h : (D.right a).map ((D.idIso j).hom.app (F.obj j)) =
      (D.compIso a (𝟙 j)).inv.app (F.obj j) ≫
        eqToHom (congrArg (fun b => (D.right b).obj (F.obj j)) (Category.comp_id a)) := by
    have h := congrArg (fun f => (D.compIso a (𝟙 j)).inv.app (F.obj j) ≫ f)
      (hD.comp_id a (F.obj j))
    simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using h
  rw [System.rightStep, Category.assoc, ← h, ← Functor.map_comp, F.map_id,
    Functor.map_id]

include hD in
/-- Composition of the actual right-adjoint steps, retaining associativity
transport instead of identifying the comparison functors definitionally. -/
theorem System.rightStep_comp {i j k l : I}
    (a : i ⟶ j) (b : j ⟶ k) (c : k ⟶ l) :
    System.rightStep D F a b ≫ System.rightStep D F (a ≫ b) c =
      System.rightStep D F a (b ≫ c) ≫
        eqToHom (congrArg (fun d => (D.right d).obj (F.obj l))
          (Category.assoc a b c).symm) := by
  have hn : (D.compIso a b).inv.app (F.obj k) ≫
      (D.right (a ≫ b)).map (F.map c) =
      (D.right a).map ((D.right b).map (F.map c)) ≫
        (D.compIso a b).inv.app ((D.right c).obj (F.obj l)) :=
    ((D.compIso a b).inv.naturality (F.map c)).symm
  simp only [System.rightStep, Category.assoc]
  rw [reassoc_of% hn, AdjunctionData.Coherent.inv_assoc D hD a b c (F.obj l)]
  have h := congrArg
    (fun f => (D.right a).map f ≫ (D.compIso a (b ≫ c)).inv.app (F.obj l) ≫
      eqToHom (congrArg (fun d => (D.right d).obj (F.obj l))
        (Category.assoc a b c).symm))
    (System.map_comp_inv D F b c)
  simpa only [Functor.map_comp, Category.assoc] using h

/-- A right-adjoint step with a specified actual target arrow. -/
def System.rightTailTransition {i j k : I} (a : i ⟶ j) (b : j ⟶ k)
    (t : i ⟶ k) (h : a ≫ b = t) :
    (D.right a).obj (F.obj j) ⟶ (D.right t).obj (F.obj k) :=
  System.rightStep D F a b ≫ eqToHom (congrArg (fun d => (D.right d).obj (F.obj k)) h)

include hD in
/-- Original composition for a commutative pair of tail triangles. -/
theorem System.rightTailTransition_comp {i j k l : I}
    (a : i ⟶ j) (b : j ⟶ k) (c : k ⟶ l) (t : i ⟶ k) (s : i ⟶ l)
    (ht : a ≫ b = t) (hs : t ≫ c = s) (hs' : a ≫ (b ≫ c) = s) :
    System.rightTailTransition D F a b t ht ≫ System.rightTailTransition D F t c s hs =
      System.rightTailTransition D F a (b ≫ c) s hs' := by
  subst t
  subst s
  have h := congrArg
    (fun f : (D.right a).obj (F.obj j) ⟶ (D.right ((a ≫ b) ≫ c)).obj (F.obj l) =>
      f ≫ eqToHom (congrArg (fun d => (D.right d).obj (F.obj l))
        (Category.assoc a b c)))
    (System.rightStep_comp D hD F a b c)
  simpa only [System.rightTailTransition, eqToHom_refl, Category.comp_id,
    Category.assoc, eqToHom_trans] using h

/-- The actual fixed-stage diagram of right images of the later coefficients. -/
def System.rightTail (i : I) : Under i ⥤ A i where
  obj a := (D.right a.hom).obj (F.obj a.right)
  map {a b} f := System.rightTailTransition D F a.hom f.right b.hom (Under.w f)
  map_id a := System.rightStep_id D hD F a.hom
  map_comp {a b c} f g :=
    (System.rightTailTransition_comp D hD F a.hom f.right g.right b.hom c.hom
      (Under.w f) (Under.w g) (Under.w (f ≫ g))).symm

@[simp]
theorem System.rightTail_obj (i : I) (a : Under i) :
    (System.rightTail D hD F i).obj a = (D.right a.hom).obj (F.obj a.right) := rfl

/-- Native adjunction injectivity supplies each actual tail coefficient.
No inverse image of an injective is asserted to be injective. -/
instance System.rightTail_obj_injective (i : I) (a : Under i) [Injective (F.obj a.right)] :
    Injective ((System.rightTail D hD F i).obj a) :=
  Injective.injective_of_adjoint (D.adj a.hom) (F.obj a.right)

end CategoryTheory.InjectiveSystem
