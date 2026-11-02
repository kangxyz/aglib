/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Representable.SectionComparisonValues
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
  change (inverseImageComp (𝟙 X) (𝟙 X)).hom.app (mu X n) ≫
    (inverseImage (𝟙 X)).map ((inverseImageId X).hom.app (mu X n)) ≫
      𝟙 ((inverseImage (𝟙 X)).obj (mu X n)) = j at hu
  exact Functor.coefficientIso_identity_of_unit_composite
    (inverseImage (𝟙 X)) (inverseImageId X)
    (inverseImageComp (𝟙 X) (𝟙 X)) (mu X n) j (rootsPullbackIso (𝟙 X) n hn hinv)
    (hc.trans hg.symm) hu

/-- The original composite roots map is the actual section identity comparison. -/
theorem rootsComposite_identity {X Y : Scheme.{u}} (r : Y ⟶ X) (a : X ⟶ Y)
    (ha : a ≫ r = 𝟙 X) (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    (rootsPullbackIso (a ≫ r) n hn hinv).hom =
      ((eqToIso (congrArg (fun f : X ⟶ X => inverseImage f) ha) ≪≫ inverseImageId X).hom.app
        (mu X n)) := by
  let hF := congrArg (fun f : X ⟶ X => inverseImage f) ha
  let t := eqToIso hF ≪≫ inverseImageId X
  have ht : t = eqToIso hF ≪≫ inverseImageId X := rfl
  have hg := TriangleCoherence.rootsPullbackIso_congr ha n hn hinv
  have hi := rootsPullbackIso_identity X n hn hinv
  have hfinal := Functor.comparison_transport_hom_app_of_whole
    hF (inverseImageId X) t ht (mu X n) hg hi
  exact hfinal

/-- The literal roots coefficient maps contract along the actual section. -/
theorem roots_section_coefficients {X Y : Scheme.{u}} (r : Y ⟶ X) (a : X ⟶ Y)
    (ha : a ≫ r = 𝟙 X) (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    (inverseImage a).map (rootsPullbackIso r n hn hinv).hom ≫
      (rootsPullbackIso a n hn (levelInvertible r n hinv)).hom =
        (sectionCoefficientIso r a ha (mu X n)).hom := by
  let c := inverseImageComp r a
  let i := eqToIso (congrArg (fun f : X ⟶ X => inverseImage f) ha) ≪≫ inverseImageId X
  let σ := sectionCoefficientNatIso r a ha
  have hσ : σ = Functor.sourceSectionIso c i := rfl
  have hc := Functor.sectionCoefficient_of_original_comparison c i σ hσ
    (rootsPullbackIso r n hn hinv) (rootsPullbackIso a n hn (levelInvertible r n hinv))
    (rootsPullbackIso (a ≫ r) n hn hinv)
    (TriangleCoherence.rootsPullbackIso_comp_intrinsic r a n hn hinv)
    (rootsComposite_identity r a ha n hn hinv)
  have hi := congrArg Iso.hom (sectionCoefficientNatIso_app r a ha (mu X n))
  exact hc.trans hi

/-- Assemble the complete original comparison with arbitrary coefficient
sheaves. In particular, the H1/raw-cohomology value correspondence is proved
here, before roots, their level or their comparison isomorphisms are supplied. -/
private theorem sectionPullback_of_original_coefficients
    {X Y : Scheme.{u}} (r : Y ⟶ X) (a : X ⟶ Y) (ha : a ≫ r = 𝟙 X)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y)]
    {A : AbelianSheaf.{u, u + 1} X} {B : AbelianSheaf.{u, u + 1} Y}
    (q : (inverseImage r).obj A ≅ B) (s : (inverseImage a).obj B ≅ A)
    (k : (inverseImage (a ≫ r)).obj A ≅ A)
    (hcomp : (inverseImageComp r a).hom.app A ≫
      (inverseImage a).map q.hom ≫ s.hom = k.hom)
    (hid : k.hom =
      (eqToIso (congrArg (fun f : X ⟶ X => inverseImage f) ha) ≪≫ inverseImageId X).hom.app A)
    (x : H1Etale.{u, u + 1, w'} Y B) :
    sectionPullback r a ha A (coefficientMap q.inv x) =
      (Sheaf.H.map s.hom 1).comp (cohomologyPullback a B 1) x := by
  let c := inverseImageComp r a
  let i := eqToIso (congrArg (fun f : X ⟶ X => inverseImage f) ha) ≪≫ inverseImageId X
  let σ := sectionCoefficientNatIso r a ha
  have hσ : σ = Functor.sourceSectionIso c i := rfl
  let T := h1Functor.{u, u + 1, w} (X := X)
  have hφ : (sectionCoefficientIso r a ha A).hom =
      (σ.app A).hom :=
    (congrArg Iso.hom (sectionCoefficientNatIso_app r a ha A)).symm
  have hE : (fun b => sectionPullback r a ha A b) =
      fun b => T.map (sectionCoefficientIso r a ha A).hom
        (h1Pullback a ((inverseImage r).obj A) b) := rfl
  have hR : (fun b => (Sheaf.H.map s.hom 1).comp (cohomologyPullback a B 1) b) =
      fun b => T.map s.hom (h1Pullback a B b) := by
    funext b
    change coefficientMap s.hom (cohomologyPullback a B 1 b) = _
    rw [cohomologyPullback_one]
    rfl
  have hp (b : H1Etale.{u, u + 1, w'} Y B) :=
    h1Pullback_coefficientMap.{u, w', w} a q.inv b
  have hfinal := Functor.sectionCoefficient_map_values_of_original_comparison
    c i σ hσ q s k hcomp hid
    (sectionCoefficientIso r a ha A).hom hφ T
    (fun b => sectionPullback r a ha A b)
    (fun b => h1Pullback a ((inverseImage r).obj A) b)
    (fun b => h1Pullback a B b)
    (fun b => coefficientMap q.inv b)
    (fun b => (Sheaf.H.map s.hom 1).comp (cohomologyPullback a B 1) b)
    hE hR hp
  exact congrFun hfinal x

/-- Whole original roots H1 section formula, preserving the actual two independent Ext worlds. -/
theorem sectionPullback_roots {X Y : Scheme.{u}} (r : Y ⟶ X) (a : X ⟶ Y)
    (ha : a ≫ r = 𝟙 X) (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y)]
    (x : H1Etale.{u, u + 1, w'} Y (mu Y n)) :
    sectionPullback r a ha (mu X n) (coefficientMap (rootsPullbackIso r n hn hinv).inv x) =
      Kummer.rootsCohomologyPullback a n hn (levelInvertible r n hinv) 1 x := by
  exact sectionPullback_of_original_coefficients r a ha
    (rootsPullbackIso r n hn hinv)
    (rootsPullbackIso a n hn (levelInvertible r n hinv))
    (rootsPullbackIso (a ≫ r) n hn hinv)
    (TriangleCoherence.rootsPullbackIso_comp_intrinsic r a n hn hinv)
    (rootsComposite_identity r a ha n hn hinv) x

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.SectionPullback
