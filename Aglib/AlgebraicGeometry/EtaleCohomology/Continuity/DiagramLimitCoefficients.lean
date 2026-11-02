/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramPullbacks
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackCohomologySystem
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.ConeConstancy

/-! # Pulling compatible coefficients to a specified scheme cone -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge

/-- The original selected left functor is literally the native inverse image. -/
lemma schemeLeft_eq_inverseImage {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    schemeAdjunctionData.left f = inverseImage f.unop := rfl

/-- The existing ambient comparison is the original inverse-image comparison. -/
lemma schemeLeftCompIso_eq_inverseImageComp {X Y Z : Scheme.{u}ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    schemeAdjunctionData.leftCompIso f g = inverseImageComp f.unop g.unop := by
  apply Iso.ext
  apply (conjugateEquiv ((inverseImageAdjunction f.unop).comp
    (inverseImageAdjunction g.unop)) (inverseImageAdjunction (g.unop ≫ f.unop))).injective
  exact (Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _).trans
    (conjugateEquiv_inverseImageComp_hom f.unop g.unop).symm

/-- Generic triangle transport is the whole original pullback triangle. -/
lemma schemeTriangleIso_eq_pullbackTriangleIso {X Y T : Scheme.{u}ᵒᵖ}
    (f : X ⟶ Y) (p : X ⟶ T) (q : Y ⟶ T) (h : f ≫ q = p) :
    schemeAdjunctionData.triangleIso p f q h =
      pullbackTriangleIso p.unop f.unop q.unop (congrArg Quiver.Hom.unop h) := by
  cases h
  simpa only [InjectiveSystem.AdjunctionData.triangleIso, pullbackTriangleIso,
    eqToIso_refl, Iso.refl_trans] using schemeLeftCompIso_eq_inverseImageComp f q

/-- Transport of a coefficient transition to a fixed scheme, with its actual triangle. -/
def triangleCoefficientMap {Y Z T : Scheme.{u}} (f : Z ⟶ Y)
    (p : T ⟶ Y) (q : T ⟶ Z) (h : q ≫ f = p)
    {F : AbelianSheaf.{u, u + 1} Y} {G : AbelianSheaf.{u, u + 1} Z}
    (φ : (inverseImage f).obj F ⟶ G) :
    (inverseImage p).obj F ⟶ (inverseImage q).obj G :=
  (pullbackTriangleIso p f q h).hom.app F ≫ (inverseImage q).map φ

/-- Transporting two coefficient transitions composes by the original inverse-image comparison. -/
lemma triangleCoefficientMap_comp {Y Z W T : Scheme.{u}}
    (f : Z ⟶ Y) (g : W ⟶ Z) (p : T ⟶ Y) (q : T ⟶ Z) (r : T ⟶ W)
    (hp : q ≫ f = p) (hq : r ≫ g = q)
    {F : AbelianSheaf.{u, u + 1} Y} {G : AbelianSheaf.{u, u + 1} Z}
    {H : AbelianSheaf.{u, u + 1} W}
    (φ : (inverseImage f).obj F ⟶ G) (ψ : (inverseImage g).obj G ⟶ H) :
    triangleCoefficientMap f p q hp φ ≫ triangleCoefficientMap g q r hq ψ =
      triangleCoefficientMap (g ≫ f) p r (by rw [← Category.assoc, hq, hp])
        ((inverseImageComp f g).hom.app F ≫ (inverseImage g).map φ ≫ ψ) := by
  simpa only [InjectiveSystem.AdjunctionData.triangleCoefficientMap,
    schemeTriangleIso_eq_pullbackTriangleIso, schemeLeftCompIso_eq_inverseImageComp,
    schemeLeft_eq_inverseImage, triangleCoefficientMap, unop_comp, Quiver.Hom.unop_op] using
    schemeAdjunctionData.triangleCoefficientMap_comp schemeAdjunctionData_coherent
      f.op g.op p.op q.op r.op (congrArg Quiver.Hom.op hp) (congrArg Quiver.Hom.op hq) φ ψ

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
