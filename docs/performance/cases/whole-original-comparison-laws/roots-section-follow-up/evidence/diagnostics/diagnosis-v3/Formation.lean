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

/- Diagnostic only: original propositions occur in theorem binders.
The new arbitrary-coefficient proposition is also tested.
No proof of any original proposition is asserted by this file. -/

theorem rootsComposite_identity_formation {X Y : Scheme.{u}} (r : Y ⟶ X) (a : X ⟶ Y)
    (ha : a ≫ r = 𝟙 X) (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (_original_statement :
    (rootsPullbackIso (a ≫ r) n hn hinv).hom =
      ((eqToIso (congrArg (fun f : X ⟶ X => inverseImage f) ha) ≪≫ inverseImageId X).hom.app
        (mu X n))) : True := True.intro

#check rootsComposite_identity_formation

theorem sectionPullback_of_original_coefficients_formation
    {X Y : Scheme.{u}} (r : Y ⟶ X) (a : X ⟶ Y) (ha : a ≫ r = 𝟙 X)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y)]
    {A : AbelianSheaf.{u, u + 1} X} {B : AbelianSheaf.{u, u + 1} Y}
    (q : (inverseImage r).obj A ≅ B) (s : (inverseImage a).obj B ≅ A)
    (k : (inverseImage (a ≫ r)).obj A ≅ A)
    (_hcomp : (inverseImageComp r a).hom.app A ≫
      (inverseImage a).map q.hom ≫ s.hom = k.hom)
    (_hid : k.hom =
      (eqToIso (congrArg (fun f : X ⟶ X => inverseImage f) ha) ≪≫ inverseImageId X).hom.app A)
    (x : H1Etale.{u, u + 1, w'} Y B)
    (_original_statement :
    sectionPullback r a ha A (coefficientMap q.inv x) =
      (Sheaf.H.map s.hom 1).comp (cohomologyPullback a B 1) x) : True := True.intro

#check sectionPullback_of_original_coefficients_formation

theorem sectionPullback_roots_formation {X Y : Scheme.{u}} (r : Y ⟶ X) (a : X ⟶ Y)
    (ha : a ≫ r = 𝟙 X) (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y)]
    (x : H1Etale.{u, u + 1, w'} Y (mu Y n))
    (_original_statement :
    sectionPullback r a ha (mu X n) (coefficientMap (rootsPullbackIso r n hn hinv).inv x) =
      Kummer.rootsCohomologyPullback a n hn (levelInvertible r n hinv) 1 x) : True := True.intro

#check sectionPullback_roots_formation

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.SectionPullback
