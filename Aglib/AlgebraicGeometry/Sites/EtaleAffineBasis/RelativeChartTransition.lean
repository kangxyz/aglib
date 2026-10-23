/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.BaseChangeRepresentativeSections
/-! # Native relative chart transition triangles -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u

/-- The original relative map given by a commuting triangle of schemes. -/
def relativeStageTransition {S T L X : Scheme.{u}}
    (τ : T ⟶ S) (σ : L ⟶ S) (q : L ⟶ T) (hq : q ≫ τ = σ) (r : S ⟶ X) :
    Over.mk (σ ≫ r) ⟶ Over.mk (τ ≫ r) :=
  Over.homMk q ((Category.assoc _ _ _).symm.trans (congrArg (fun z ↦ z ≫ r) hq))

/-- The actual transition between the two pullback charts. -/
def relativeChartTransition {S T L X : Scheme.{u}}
    (τ : T ⟶ S) (σ : L ⟶ S) (q : L ⟶ T) (hq : q ≫ τ = σ)
    (r : S ⟶ X) (W : Over S) :
    relativeBaseChangeObject σ r W.hom ⟶ relativeBaseChangeObject τ r W.hom :=
  Over.homMk
    (pullback.lift (pullback.fst σ W.hom ≫ q) (pullback.snd σ W.hom)
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z ↦ pullback.fst σ W.hom ≫ z) hq).trans pullback.condition)))
    (by
      change (pullback.lift _ _ _) ≫ (pullback.snd τ W.hom ≫ W.hom ≫ r) =
        pullback.snd σ W.hom ≫ W.hom ≫ r
      exact pullback.lift_snd_assoc _ _ _ _)

theorem relativeChartTransition_source {S T L X : Scheme.{u}}
    (τ : T ⟶ S) (σ : L ⟶ S) (q : L ⟶ T) (hq : q ≫ τ = σ)
    (r : S ⟶ X) (W : Over S) :
    relativeChartTransition τ σ q hq r W ≫ relativeBaseChangeSource τ r W.hom =
      relativeBaseChangeSource σ r W.hom ≫ relativeStageTransition τ σ q hq r := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

theorem relativeChartTransition_representative {S T L X : Scheme.{u}}
    (τ : T ⟶ S) (σ : L ⟶ S) (q : L ⟶ T) (hq : q ≫ τ = σ)
    (r : S ⟶ X) (W : Over S) (U : X.Etale)
    (a : W.left ⟶ U.left) (ha : a ≫ U.hom = W.hom ≫ r) :
    relativeChartTransition τ σ q hq r W ≫
      relativeBaseChangeRepresentative τ r W.hom U a ha =
      relativeBaseChangeRepresentative σ r W.hom U a ha := by
  apply Over.OverMorphism.ext
  change (pullback.lift _ _ _) ≫ (pullback.snd τ W.hom ≫ a) =
    pullback.snd σ W.hom ≫ a
  exact pullback.lift_snd_assoc _ _ _ _

end AlgebraicGeometry.Scheme.EtaleAffineBasis
