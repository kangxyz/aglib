/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.NoetherianComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.ProjectiveLineTests
public import Mathlib.GroupTheory.OrderOfElement
public import Aglib.CategoryTheory.Abelian.Ext.OriginalComparisonValues
public import Aglib.CategoryTheory.Sites.SheafCohomology.SourceSection

/-! # Literal original inverse-source transport

Equality of the original index transports a source-arrow family and an original
comparison isomorphism. The target morphism is retained as its literal input
value. The native theorem is the same full ordinary source equation as the V28
test; its proof does not reconstruct source functors or source isomorphisms in
the generic transport telescope.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe uI uC vC uD vD

/-- Transport an original pointwise source family, retaining the original
comparison isomorphism and the literal target morphism. -/
theorem sourceInverse_composite_transport_of_arrows
    {I : Type uI} {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D]
    (K : I → C ⥤ D) {U : C} {V : D}
    (s : (i : I) → V ⟶ (K i).obj U)
    {i j : I} (h : i = j) {Q : C ⥤ D} (c : K j ≅ Q)
    (r : V ⟶ Q.obj U) (hc : s j ≫ c.hom.app U = r) :
    s i ≫ (eqToIso (congrArg K h) ≪≫ c).hom.app U = r := by
  cases h
  simpa only [eqToIso_refl, Iso.refl_trans] using hc

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u

attribute [local instance] hasSheafifyLarge

/-- The literal original ordinary source equation follows from the original
composition equation and equality transport of its actual source-arrow family. -/
theorem diag_original_sourceSecond_literal
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (A : AddCommGrpCat.{u + 1}) :
    ((inverseImageConstantIso (f' ≫ g)).app A).inv ≫
        (eqToIso (congrArg (fun k : X' ⟶ S => inverseImage k) h) ≪≫
          inverseImageComp f g').hom.app
            ((constantSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).obj A) =
      ((inverseImageConstantIso g').app A).inv ≫
        (inverseImage g').map ((inverseImageConstantIso f).app A).inv := by
  have hSourceComp := inverseImageComp_constant_inv f g' A
  exact Functor.sourceInverse_composite_transport_of_arrows
    (fun k : X' ⟶ S => inverseImage k)
    (fun k => ((inverseImageConstantIso k).app A).inv) h
    (inverseImageComp f g')
    (((inverseImageConstantIso g').app A).inv ≫
      (inverseImage g').map ((inverseImageConstantIso f).app A).inv)
    hSourceComp

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
