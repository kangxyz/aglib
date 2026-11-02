/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramLimitCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSquareCoefficients
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.ConeExtension

/-! # The actual coefficient diagram at an inverse scheme cone -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge

/-- The native direct-image triangle, with its original equality transport. -/
def directImageTriangleIso {X Y T : Scheme.{u}} (f : Y ⟶ X)
    (p : T ⟶ X) (q : T ⟶ Y) (h : q ≫ f = p) :
    directImage q ⋙ directImage f ≅ directImage p :=
  directImageCompIso f q ≪≫ eqToIso (congrArg directImage h)

/-- The selected right triangle is the original whole direct-image comparison. -/
lemma schemeTriangleRightIso_eq_directImageTriangleIso {X Y T : Scheme.{u}ᵒᵖ}
    (f : X ⟶ Y) (p : X ⟶ T) (q : Y ⟶ T) (h : f ≫ q = p) :
    schemeAdjunctionData.triangleRightIso p f q h =
      directImageTriangleIso f.unop p.unop q.unop (congrArg Quiver.Hom.unop h) := by
  cases h
  rfl

/-- The original inverse- and direct-image triangle comparisons are conjugate. -/
lemma pullbackTriangleIso_mate {X Y T : Scheme.{u}} (f : Y ⟶ X)
    (p : T ⟶ X) (q : T ⟶ Y) (h : q ≫ f = p) :
    conjugateEquiv ((inverseImageAdjunction f).comp (inverseImageAdjunction q))
      (inverseImageAdjunction p) (pullbackTriangleIso p f q h).hom =
        (directImageTriangleIso f p q h).hom := by
  have hm := schemeAdjunctionData.conjugate_triangleIso_hom p.op f.op q.op
    (congrArg Quiver.Hom.op h)
  simp only [schemeTriangleIso_eq_pullbackTriangleIso,
    schemeTriangleRightIso_eq_directImageTriangleIso, Quiver.Hom.unop_op] at hm ⊢
  exact hm

/-- Transporting the identity coefficient through the original identity comparison is identity. -/
lemma triangleCoefficientMap_identity {Y T : Scheme.{u}} (f : Y ⟶ Y) (e : f = 𝟙 Y)
    (p : T ⟶ Y) (F : AbelianSheaf.{u, u + 1} Y) :
    triangleCoefficientMap f p p (by rw [e, Category.comp_id])
      (eqToHom (congrArg (fun k : Y ⟶ Y => (inverseImage k).obj F) e) ≫
        (inverseImageId Y).hom.app F) = 𝟙 ((inverseImage p).obj F) := by
  have h := schemeAdjunctionData.triangleCoefficientMap_identity schemeAdjunctionData_coherent
    f.op (congrArg Quiver.Hom.op e) p.op F
  simp only [InjectiveSystem.AdjunctionData.triangleCoefficientMap,
    schemeTriangleIso_eq_pullbackTriangleIso, schemeLeft_eq_inverseImage,
    schemeLeftIdIso_eq_inverseImageId, triangleCoefficientMap,
    Quiver.Hom.unop_op, unop_id] at h ⊢
  exact h

/-- The coefficient composition law retains a supplied equality of scheme maps. -/
lemma triangleCoefficientMap_comp_transport {Y Z W T : Scheme.{u}}
    (f : Z ⟶ Y) (g : W ⟶ Z) (t : W ⟶ Y) (e : t = g ≫ f)
    (p : T ⟶ Y) (q : T ⟶ Z) (r : T ⟶ W)
    (hp : q ≫ f = p) (hq : r ≫ g = q)
    {F : AbelianSheaf.{u, u + 1} Y} {G : AbelianSheaf.{u, u + 1} Z}
    {H : AbelianSheaf.{u, u + 1} W}
    (φ : (inverseImage f).obj F ⟶ G) (ψ : (inverseImage g).obj G ⟶ H) :
    triangleCoefficientMap f p q hp φ ≫ triangleCoefficientMap g q r hq ψ =
      triangleCoefficientMap t p r (by rw [e, ← Category.assoc, hq, hp])
        (eqToHom (congrArg (fun k : W ⟶ Y => (inverseImage k).obj F) e) ≫
          (inverseImageComp f g).hom.app F ≫ (inverseImage g).map φ ≫ ψ) := by
  have h := schemeAdjunctionData.triangleCoefficientMap_comp_transport
    schemeAdjunctionData_coherent f.op g.op t.op (congrArg Quiver.Hom.op e)
    p.op q.op r.op (congrArg Quiver.Hom.op hp) (congrArg Quiver.Hom.op hq) φ ψ
  simp only [InjectiveSystem.AdjunctionData.triangleCoefficientMap,
    schemeTriangleIso_eq_pullbackTriangleIso, schemeLeftCompIso_eq_inverseImageComp,
    schemeLeft_eq_inverseImage, triangleCoefficientMap, unop_comp,
    Quiver.Hom.unop_op] at h ⊢
  exact h

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (c : Cocone X) (F : DiagramCoefficientSystem X)

/-- The existing scheme adjunction data at the specified cone, retaining its
original inverse-image triangle rather than choosing another image functor. -/
def diagramConeAdjunctionData :
    (diagramAdjunctionData X).Cone (AbelianSheaf.{u, u + 1} c.pt.unop) :=
  { InjectiveSystem.AdjunctionData.Cone.ofCocone schemeAdjunctionData
      schemeAdjunctionData_coherent X c with
    leftTriangle := fun {i j} a => pullbackTriangleIso (c.ι.app i).unop
      (X.map a).unop (c.ι.app j).unop
      (congrArg (fun k : X.obj i ⟶ c.pt => k.unop) (c.w a))
    conjugate := fun {i j} a => pullbackTriangleIso_mate (X.map a).unop
      (c.ι.app i).unop (c.ι.app j).unop
      (congrArg (fun k : X.obj i ⟶ c.pt => k.unop) (c.w a)) }

/-- The coefficient at a stage pulled to the specified cone point. -/
abbrev coneCoefficientObj (i : I) : AbelianSheaf.{u, u + 1} c.pt.unop :=
  (inverseImage (c.ι.app i).unop).obj (F.obj i)

/-- The actual compatible transition at the cone point. -/
def coneCoefficientMap {i j : I} (a : i ⟶ j) :
    coneCoefficientObj X c F i ⟶ coneCoefficientObj X c F j :=
  triangleCoefficientMap (X.map a).unop (c.ι.app i).unop (c.ι.app j).unop
    (congrArg (fun k : X.obj i ⟶ c.pt => k.unop) (c.w a))
    (diagramInverseTransition X F a)

/-- The original coefficient system produces an actual diagram on the cone point. -/
def coneCoefficientFunctor : I ⥤ AbelianSheaf.{u, u + 1} c.pt.unop :=
  (diagramConeAdjunctionData X c).coefficientFunctor F

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
