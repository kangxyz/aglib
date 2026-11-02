/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Representable.SectionComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.TriangleCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SectionPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality

/-! # Original roots coefficient transport along an actual section

The whole formal identity, coefficient contraction and Ext assembly are in
SectionComparison. The native wrapper supplies the original roots isomorphisms,
actual inverse-image composition/identity maps and their existing intrinsic
coherence. Positivity and invertibility of the level remain geometric. No
geometric point, connected parameter family or new roots model is selected.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology.PointedNaturality
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.SectionPullback

universe u w w'
attribute [local instance] hasSheafifyLarge

/-- The original identity roots comparison is the original inverse-image identity. -/
theorem rootsPullbackIso_identity (X : Scheme.{u}) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) :
    (rootsPullbackIso (𝟙 X) n hn hinv).hom = (inverseImageId X).hom.app (mu X n) := by
  let j := (eqToIso (congrArg (fun f => (inverseImage f).obj (mu X n))
    (Category.comp_id (𝟙 X)))).hom
  have hc := TriangleCoherence.rootsPullbackIso_comp_intrinsic (𝟙 X) (𝟙 X) n hn hinv
  have hg := TriangleCoherence.rootsPullbackIso_congr (Category.comp_id (𝟙 X)) n hn hinv
  have hu := congrArg (fun e => e.hom.app (mu X n)) (inverseImageComp_id_comp (𝟙 X))
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, eqToIso.hom, eqToHom_app] at hu
  have hunit : (inverseImageComp (𝟙 X) (𝟙 X)).hom.app (mu X n) ≫
      (inverseImage (𝟙 X)).map ((inverseImageId X).hom.app (mu X n)) = j := by
    change (inverseImageComp (𝟙 X) (𝟙 X)).hom.app (mu X n) ≫
      (inverseImage (𝟙 X)).map ((inverseImageId X).hom.app (mu X n)) ≫
        𝟙 ((inverseImage (𝟙 X)).obj (mu X n)) = j at hu
    simpa only [Category.comp_id] using hu
  exact Functor.coefficientIso_identity (inverseImage (𝟙 X)) (inverseImageId X)
    (inverseImageComp (𝟙 X) (𝟙 X)) (mu X n) j (rootsPullbackIso (𝟙 X) n hn hinv)
    (hc.trans hg.symm) hunit

/-- The original composite roots map is the actual section identity comparison. -/
theorem rootsComposite_identity {X Y : Scheme.{u}} (r : Y ⟶ X) (a : X ⟶ Y)
    (ha : a ≫ r = 𝟙 X) (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    (rootsPullbackIso (a ≫ r) n hn hinv).hom =
      ((eqToIso (congrArg (fun f : X ⟶ X => inverseImage f) ha) ≪≫ inverseImageId X).hom.app
        (mu X n)) := by
  have h := TriangleCoherence.rootsPullbackIso_congr ha n hn hinv
  rw [rootsPullbackIso_identity] at h
  simpa only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app] using h.symm

/-- The literal roots coefficient maps contract along the actual section. -/
theorem roots_section_coefficients {X Y : Scheme.{u}} (r : Y ⟶ X) (a : X ⟶ Y)
    (ha : a ≫ r = 𝟙 X) (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    (inverseImage a).map (rootsPullbackIso r n hn hinv).hom ≫
      (rootsPullbackIso a n hn (levelInvertible r n hinv)).hom =
        (sectionCoefficientIso r a ha (mu X n)).hom := by
  let c := inverseImageComp r a
  let i := eqToIso (congrArg (fun f : X ⟶ X => inverseImage f) ha) ≪≫ inverseImageId X
  have hc := Functor.sectionCoefficient_of_composition c i
    (rootsPullbackIso r n hn hinv) (rootsPullbackIso a n hn (levelInvertible r n hinv))
    (rootsPullbackIso (a ≫ r) n hn hinv)
    (TriangleCoherence.rootsPullbackIso_comp_intrinsic r a n hn hinv)
    (rootsComposite_identity r a ha n hn hinv)
  have hi : (Functor.sourceSectionIso c i).hom.app (mu X n) =
      (sectionCoefficientIso r a ha (mu X n)).hom :=
    congrArg Iso.hom (sectionCoefficientNatIso_app r a ha (mu X n))
  exact hc.trans hi

/-- Whole original roots H1 section formula, preserving the actual two independent Ext worlds. -/
theorem sectionPullback_roots {X Y : Scheme.{u}} (r : Y ⟶ X) (a : X ⟶ Y)
    (ha : a ≫ r = 𝟙 X) (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y)]
    (x : H1Etale.{u, u + 1, w'} Y (mu Y n)) :
    sectionPullback r a ha (mu X n) (coefficientMap (rootsPullbackIso r n hn hinv).inv x) =
      Kummer.rootsCohomologyPullback a n hn (levelInvertible r n hinv) 1 x := by
  let c := inverseImageComp r a
  let i := eqToIso (congrArg (fun f : X ⟶ X => inverseImage f) ha) ≪≫ inverseImageId X
  let Z := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  have hx := Functor.extSectionPullback_coefficientIso
    (inverseImage r) (inverseImage a) (inverseImage (a ≫ r)) c i
    ((inverseImageConstantIso a).inv.app Z)
    (rootsPullbackIso r n hn hinv) (rootsPullbackIso a n hn (levelInvertible r n hinv))
    (rootsPullbackIso (a ≫ r) n hn hinv)
    (TriangleCoherence.rootsPullbackIso_comp_intrinsic r a n hn hinv)
    (rootsComposite_identity r a ha n hn hinv) 1 x
  have hi : (Functor.sourceSectionIso c i).hom.app (mu X n) =
      (sectionCoefficientIso r a ha (mu X n)).hom :=
    congrArg Iso.hom (sectionCoefficientNatIso_app r a ha (mu X n))
  simpa only [Functor.extSectionPullback, Functor.extCoefficientTransfer_apply, hi] using hx

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.SectionPullback
