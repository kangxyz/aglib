/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Over.FullPullbackChart
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GenericRadicialChart

/-! # Affine-scheme adapter for entire radicial chart descent

The literal spectrum theorem is transported through the original affine
spectrum isomorphisms. The resulting chart map is defined on the entire
original pullback and retains its original map to the original source chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable

universe u

/-- An entire finite-etale source chart descends on a nonempty affine target
open, in a form directly usable by original coefficient pullback. -/
theorem exists_affine_radicial_chart_factorization
    {Y X : Scheme.{u}} [IsAffine Y] [IsAffine X] [IsIntegral Y] [IsIntegral X]
    [IsNoetherian X] (f : Y ⟶ X) [IsFinite f] [UniversallyInjective f] [Surjective f]
    (W : Scheme.FiniteEtale Y) [Surjective W.obj.hom] :
    ∃ (U : Scheme.{u}) (j : U ⟶ X), IsAffine U ∧ IsOpenImmersion j ∧ Nonempty U ∧
      ∃ T : Scheme.FiniteEtale U, Surjective T.obj.hom ∧
        ∃ a : pullback f (T.obj.hom ≫ j) ⟶ W.obj.left,
          a ≫ W.obj.hom = pullback.fst f (T.obj.hom ≫ j) := by
  let : IsNoetherianRing Γ(X, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  let f₀ : Spec Γ(Y, ⊤) ⟶ Spec Γ(X, ⊤) := Y.isoSpec.inv ≫ f ≫ X.isoSpec.hom
  have : IsFinite f₀ := inferInstanceAs (IsFinite (Y.isoSpec.inv ≫ f ≫ X.isoSpec.hom))
  have : Surjective f₀ := inferInstanceAs (Surjective (Y.isoSpec.inv ≫ f ≫ X.isoSpec.hom))
  have : UniversallyInjective f₀ := by
    exact MorphismProperty.comp_mem @UniversallyInjective _ _ inferInstance
      (MorphismProperty.comp_mem @UniversallyInjective _ _ inferInstance inferInstance)
  let W₀ := (Scheme.FiniteEtale.baseChange Y.isoSpec.inv).obj W
  have : Surjective W₀.obj.hom :=
    inferInstanceAs (Surjective (pullback.snd W.obj.hom Y.isoSpec.inv))
  obtain ⟨U, hUa, hU, T, hT, ⟨e⟩⟩ :=
    Scheme.FiniteEtale.PurelyInseparable.exists_generic_surjective_full_pullback_chart
      Γ(X, ⊤) Γ(Y, ⊤) f₀ W₀
  let j : U.toScheme ⟶ X := U.ι ≫ X.isoSpec.inv
  let q := T.obj.hom
  let H := (isPullback_morphismRestrict f₀ U).flip
  let a₀ := CategoryTheory.Over.fullPullbackChartMap f₀ U.ι (f₀ ⁻¹ᵁ U).ι (f₀ ∣_ U) H q W₀.obj.hom e
  let b : pullback f (q ≫ j) ⟶ pullback f₀ (q ≫ U.ι) :=
    pullback.lift (pullback.fst f (q ≫ j) ≫ Y.isoSpec.hom)
      (pullback.snd f (q ≫ j)) (by
        have hb := congrArg (fun z => z ≫ X.isoSpec.hom)
          (pullback.condition (f := f) (g := q ≫ j))
        simpa [f₀, j, Category.assoc] using hb)
  refine ⟨U, j, hUa, inferInstance, ⟨⟨genericPoint (Spec Γ(X, ⊤)), hU⟩⟩,
    T, hT, b ≫ a₀ ≫ pullback.fst W.obj.hom Y.isoSpec.inv, ?_⟩
  have hW : pullback.fst W.obj.hom Y.isoSpec.inv ≫ W.obj.hom =
      W₀.obj.hom ≫ Y.isoSpec.inv := pullback.condition
  have ha : a₀ ≫ W₀.obj.hom = pullback.fst f₀ (q ≫ U.ι) :=
    CategoryTheory.Over.fullPullbackChartMap_over f₀ U.ι (f₀ ⁻¹ᵁ U).ι (f₀ ∣_ U) H q W₀.obj.hom e
  have hb : b ≫ pullback.fst f₀ (q ≫ U.ι) =
      pullback.fst f (q ≫ j) ≫ Y.isoSpec.hom := pullback.lift_fst _ _ _
  calc
    (b ≫ a₀ ≫ pullback.fst W.obj.hom Y.isoSpec.inv) ≫ W.obj.hom =
        b ≫ a₀ ≫ W₀.obj.hom ≫ Y.isoSpec.inv := by
      exact (Category.assoc b (a₀ ≫ pullback.fst W.obj.hom Y.isoSpec.inv) W.obj.hom).trans
        ((congrArg (fun z => b ≫ z)
          (Category.assoc a₀ (pullback.fst W.obj.hom Y.isoSpec.inv) W.obj.hom)).trans
          (congrArg (fun z => b ≫ a₀ ≫ z) hW))
    _ = (b ≫ pullback.fst f₀ (q ≫ U.ι)) ≫ Y.isoSpec.inv := by
      simpa only [Category.assoc] using congrArg (fun z => b ≫ z ≫ Y.isoSpec.inv) ha
    _ = pullback.fst f (q ≫ j) := by
      rw [hb]
      simp

end AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable
