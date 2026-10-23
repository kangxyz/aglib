/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.BaseChangeUnitMatching
/-! # Actual comparison arrows between the two original relative chart objects -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u
open EtaleCohomology EtaleCohomology.Continuity

/-- The identity-underlying map from the factorized chart to the native chart. -/
def relativeToNativeChart {S T X : Scheme.{u}} (τ : T ⟶ S) (r : S ⟶ X)
    (W : Over S) [Etale W.hom] : relativeBaseChangeObject τ r W.hom ⟶
      Over.mk ((baseChangeEtaleChart τ W).hom ≫ (τ ≫ r)) :=
  Over.homMk (𝟙 (pullback τ W.hom)) (by
    change (𝟙 _) ≫ (pullback.fst τ W.hom ≫ (τ ≫ r)) =
      pullback.snd τ W.hom ≫ W.hom ≫ r
    exact (Category.id_comp _).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun q ↦ q ≫ r) pullback.condition).trans (Category.assoc _ _ _))))

/-- The reverse identity-underlying map, without identifying the objects by equality. -/
def nativeToRelativeChart {S T X : Scheme.{u}} (τ : T ⟶ S) (r : S ⟶ X)
    (W : Over S) [Etale W.hom] :
    Over.mk ((baseChangeEtaleChart τ W).hom ≫ (τ ≫ r)) ⟶
      relativeBaseChangeObject τ r W.hom :=
  Over.homMk (𝟙 (pullback τ W.hom)) (by
    change (𝟙 _) ≫ (pullback.snd τ W.hom ≫ W.hom ≫ r) =
      pullback.fst τ W.hom ≫ (τ ≫ r)
    exact (Category.id_comp _).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun q ↦ q ≫ r) pullback.condition.symm).trans (Category.assoc _ _ _))))

theorem relativeToNativeChart_source {S T X : Scheme.{u}} (τ : T ⟶ S) (r : S ⟶ X)
    (W : Over S) [Etale W.hom] :
    relativeToNativeChart τ r W ≫
      Over.homMk (baseChangeEtaleChart τ W).hom
        (U := Over.mk ((baseChangeEtaleChart τ W).hom ≫ (τ ≫ r)))
        (V := Over.mk (τ ≫ r)) = relativeBaseChangeSource τ r W.hom := by
  apply Over.OverMorphism.ext
  exact Category.id_comp _

theorem nativeToRelativeChart_source {S T X : Scheme.{u}} (τ : T ⟶ S) (r : S ⟶ X)
    (W : Over S) [Etale W.hom] :
    nativeToRelativeChart τ r W ≫ relativeBaseChangeSource τ r W.hom =
      Over.homMk (baseChangeEtaleChart τ W).hom
        (U := Over.mk ((baseChangeEtaleChart τ W).hom ≫ (τ ≫ r)))
        (V := Over.mk (τ ≫ r)) := by
  apply Over.OverMorphism.ext
  exact Category.id_comp _

theorem relativeToNativeChart_representative {S T X : Scheme.{u}}
    (τ : T ⟶ S) (r : S ⟶ X) (W : Over S) [Etale W.hom]
    (U : X.Etale) (a : W.left ⟶ U.left) (ha : a ≫ U.hom = W.hom ≫ r) :
    relativeToNativeChart τ r W ≫
      unitRepresentativeArrow (τ ≫ r) (baseChangeChartTest τ r W U a ha) =
      relativeBaseChangeRepresentative τ r W.hom U a ha := by
  apply Over.OverMorphism.ext
  change (𝟙 _) ≫ ((baseChangeChartTest τ r W U a ha).left ≫
    pullback.fst U.hom (τ ≫ r)) = pullback.snd τ W.hom ≫ a
  exact (Category.id_comp _).trans (pullback.lift_fst _ _ _)

end AlgebraicGeometry.Scheme.EtaleAffineBasis
