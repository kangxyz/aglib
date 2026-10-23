/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.RightTail
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramDirectImageTriangleComp

/-! # The original fixed-stage right-image coefficient cocone

All coefficients in the tail at a fixed stage live on that stage. Its maps
are the actual system transitions followed by the native direct-image
composition comparison. The adjoints of the original coefficient-colimit
injections give a genuine cocone into the direct image of the limit
coefficient. We do not assert that this sheaf cocone is colimiting.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u uI vI

attribute [local instance] hasSheafifyLarge

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X)

/-- The actual later coefficients pushed to one fixed stage. -/
def diagramRightTail (i : I) : Under i ⥤ AbelianSheaf.{u, u + 1} (X.obj i).unop :=
  InjectiveSystem.System.rightTail (diagramAdjunctionData X)
    (diagramAdjunctionData_coherent X) F i

@[simp]
theorem diagramRightTail_obj (i : I) (a : Under i) :
    (diagramRightTail X F i).obj a =
      (directImage (X.map a.hom).unop).obj (F.obj a.right) := rfl

/-- Genuine right adjoints preserve the injectivity of the later coefficient. -/
instance diagramRightTail_obj_injective (i : I) (a : Under i)
    [Injective (F.obj a.right)] : Injective ((diagramRightTail X F i).obj a) :=
  InjectiveSystem.System.rightTail_obj_injective (diagramAdjunctionData X)
    (diagramAdjunctionData_coherent X) F i a

variable (c : Cocone X) [HasColimit (coneCoefficientFunctor X c F)]

/-- The original adjoint coefficient leg, transported through the actual cone triangle. -/
def diagramRightTailLeg {i j : I} (a : i ⟶ j) :
    (directImage (X.map a).unop).obj (F.obj j) ⟶
      (directImage (c.ι.app i).unop).obj (colimit (coneCoefficientFunctor X c F)) :=
  (directImage (X.map a).unop).map (diagramAdjointLeg X c F j) ≫
    (diagramDirectImageTriangle X c a).hom.app (colimit (coneCoefficientFunctor X c F))

/-- The original system transition and both direct-image comparisons give the
fixed-stage cocone equation for a composable pair of arrows. -/
theorem diagramRightTailLeg_step {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    InjectiveSystem.System.rightStep (diagramAdjunctionData X) F a b ≫
        diagramRightTailLeg X F c (a ≫ b) = diagramRightTailLeg X F c a := by
  let L := colimit (coneCoefficientFunctor X c F)
  let α : (directImage (X.map a).unop).obj (F.obj j) ⟶
      (directImage (X.map a).unop).obj ((directImage (X.map b).unop).obj (F.obj k)) :=
    (directImage (X.map a).unop).map (F.map b)
  let β : (directImage (X.map a).unop).obj
      ((directImage (X.map b).unop).obj (F.obj k)) ⟶
        (directImage (X.map (a ≫ b)).unop).obj (F.obj k) :=
    ((diagramAdjunctionData X).compIso a b).inv.app (F.obj k)
  let γ : (directImage (X.map (a ≫ b)).unop).obj (F.obj k) ⟶
      (directImage (X.map (a ≫ b)).unop).obj ((directImage (c.ι.app k).unop).obj L) :=
    (directImage (X.map (a ≫ b)).unop).map (diagramAdjointLeg X c F k)
  let δ : (directImage (X.map (a ≫ b)).unop).obj
      ((directImage (c.ι.app k).unop).obj L) ⟶ (directImage (c.ι.app i).unop).obj L :=
    (diagramDirectImageTriangle X c (a ≫ b)).hom.app L
  let ε : (directImage (X.map a).unop).obj
      ((directImage (X.map b).unop).obj (F.obj k)) ⟶
        (directImage (X.map a).unop).obj
          ((directImage (X.map b).unop).obj ((directImage (c.ι.app k).unop).obj L)) :=
    (directImage (X.map a).unop).map
      ((directImage (X.map b).unop).map (diagramAdjointLeg X c F k))
  let ζ : (directImage (X.map a).unop).obj
      ((directImage (X.map b).unop).obj ((directImage (c.ι.app k).unop).obj L)) ⟶
        (directImage (X.map (a ≫ b)).unop).obj ((directImage (c.ι.app k).unop).obj L) :=
    ((diagramAdjunctionData X).compIso a b).inv.app ((directImage (c.ι.app k).unop).obj L)
  let η : (directImage (X.map a).unop).obj
      ((directImage (X.map b).unop).obj ((directImage (c.ι.app k).unop).obj L)) ⟶
        (directImage (X.map a).unop).obj ((directImage (c.ι.app j).unop).obj L) :=
    (directImage (X.map a).unop).map ((diagramDirectImageTriangle X c b).hom.app L)
  let θ : (directImage (X.map a).unop).obj ((directImage (c.ι.app j).unop).obj L) ⟶
      (directImage (c.ι.app i).unop).obj L :=
    (diagramDirectImageTriangle X c a).hom.app L
  have hn : β ≫ γ = ε ≫ ζ :=
    (((diagramAdjunctionData X).compIso a b).inv.naturality
      (diagramAdjointLeg X c F k)).symm
  have ht : ζ ≫ δ = η ≫ θ := diagramDirectImageTriangle_comp X c a b L
  have hm : (directImage (X.map a).unop).map (diagramAdjointLeg X c F j) =
      α ≫ ε ≫ η := by
    let ρ : F.obj j ⟶ (directImage (X.map b).unop).obj (F.obj k) := F.map b
    let σ : (directImage (X.map b).unop).obj (F.obj k) ⟶
        (directImage (X.map b).unop).obj ((directImage (c.ι.app k).unop).obj L) :=
      (directImage (X.map b).unop).map (diagramAdjointLeg X c F k)
    let τ : (directImage (X.map b).unop).obj ((directImage (c.ι.app k).unop).obj L) ⟶
        (directImage (c.ι.app j).unop).obj L :=
      (diagramDirectImageTriangle X c b).hom.app L
    have hξ : diagramAdjointLeg X c F j = ρ ≫ σ ≫ τ :=
      diagramAdjointLeg_naturality X c F b
    have h := congrArg
      (fun f : F.obj j ⟶ (directImage (c.ι.app j).unop).obj L =>
        (directImage (X.map a).unop).map f) hξ
    exact h.trans (((directImage (X.map a).unop).map_comp ρ (σ ≫ τ)).trans
      (congrArg (fun f => (directImage (X.map a).unop).map ρ ≫ f)
        ((directImage (X.map a).unop).map_comp σ τ)))
  have hcalc : (α ≫ β) ≫ (γ ≫ δ) =
      (directImage (X.map a).unop).map (diagramAdjointLeg X c F j) ≫ θ := by
    calc
      (α ≫ β) ≫ (γ ≫ δ) = α ≫ (β ≫ γ) ≫ δ := by simp only [Category.assoc]
      _ = α ≫ (ε ≫ ζ) ≫ δ := congrArg (fun f => α ≫ f ≫ δ) hn
      _ = (α ≫ ε) ≫ (ζ ≫ δ) := by simp only [Category.assoc]
      _ = (α ≫ ε) ≫ (η ≫ θ) := congrArg (fun f => (α ≫ ε) ≫ f) ht
      _ = (α ≫ ε ≫ η) ≫ θ := by simp only [Category.assoc]
      _ = (directImage (X.map a).unop).map (diagramAdjointLeg X c F j) ≫ θ :=
        congrArg (fun f => f ≫ θ) hm.symm
  exact hcalc

/-- The same cocone equation retains a specified triangle in the original index category. -/
theorem diagramRightTailLeg_transition {i j k : I}
    (a : i ⟶ j) (b : j ⟶ k) (t : i ⟶ k) (h : a ≫ b = t) :
    InjectiveSystem.System.rightTailTransition (diagramAdjunctionData X) F a b t h ≫
        diagramRightTailLeg X F c t = diagramRightTailLeg X F c a := by
  subst t
  simpa only [InjectiveSystem.System.rightTailTransition, eqToHom_refl,
    Category.comp_id] using diagramRightTailLeg_step X F c a b

/-- The canonical cocone on the actual fixed-stage right-image tail. Only
existence of the original limit coefficient colimit is needed here. -/
def diagramRightTailCocone (i : I) : Cocone (diagramRightTail X F i) where
  pt := (directImage (c.ι.app i).unop).obj (colimit (coneCoefficientFunctor X c F))
  ι := {
    app := fun a => diagramRightTailLeg X F c a.hom
    naturality := fun a b f =>
      (diagramRightTailLeg_transition X F c a.hom f.right b.hom (Under.w f)).trans
        (Category.comp_id (diagramRightTailLeg X F c a.hom)).symm }

@[simp]
theorem diagramRightTailCocone_ι_app (i : I) (a : Under i) :
    (diagramRightTailCocone X F c i).ι.app a =
      (directImage (X.map a.hom).unop).map (diagramAdjointLeg X c F a.right) ≫
        (diagramDirectImageTriangle X c a.hom).hom.app
          (colimit (coneCoefficientFunctor X c F)) := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
