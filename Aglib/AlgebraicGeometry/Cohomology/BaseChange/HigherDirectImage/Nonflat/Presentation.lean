/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.LocalRefinement
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ChartCongruence
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.RestrictionIdentity

/-! # Independence of the cartesian chart presentation

Identity affine refinements compare the actual local arrow on any supplied
cartesian chart squares with the arrow on the chosen fibre products. The
comparison keeps the original restriction isomorphisms and coefficient maps.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

/-- The actual local comparison on any cartesian chart presentation equals the comparison
on the chosen fibre products. This is identity affine refinement, with the original
restriction and coefficient isomorphisms retained. -/
theorem localMap_eq_chartMap
    {W U V X U₁ W₁ : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
    (h : IsPullback a b f g) [QuasiCompact f] [QuasiSeparated f]
    {R S : CommRingCat.{u}}
    (j : Spec R ⟶ X) (v : Spec S ⟶ V) (σ : R ⟶ S)
    [IsOpenImmersion j] [IsOpenImmersion v] (hv : Spec.map σ ≫ j = v ≫ g)
    (n : ℕ) (M : U.Modules) [M.IsQuasicoherent]
    (p₁ : U₁ ⟶ U) (d₁ : U₁ ⟶ Spec R) [IsOpenImmersion p₁]
    (hU₁ : IsPullback p₁ d₁ f j)
    (c₁ : W₁ ⟶ W) (e₁ : W₁ ⟶ Spec S) [IsOpenImmersion c₁]
    (hW₁ : IsPullback c₁ e₁ b v)
    (q₁ : W₁ ⟶ U₁) (hq₁ : q₁ ≫ p₁ = c₁ ≫ a)
    (hb₁ : q₁ ≫ d₁ = e₁ ≫ Spec.map σ) :
    localMap a b f g h j v σ hv n M p₁ d₁ hU₁ c₁ e₁ hW₁ q₁ hq₁ hb₁ =
      chartMap a b f g h j v σ hv n M := by
  let p := Limits.pullback.fst f j
  let d := Limits.pullback.snd f j
  let c := Limits.pullback.fst b v
  let e := Limits.pullback.snd b v
  let q := chartUpper a b f g h j v σ hv
  have hρ : Spec.map (𝟙 R) ≫ j = j := by simp only [Spec.map_id, Category.id_comp]
  have hτ : Spec.map (𝟙 S) ≫ v = v := by simp only [Spec.map_id, Category.id_comp]
  have hσ : Spec.map (𝟙 S) ≫ Spec.map σ = Spec.map σ ≫ Spec.map (𝟙 R) := by
    simp only [Spec.map_id, Category.id_comp, Category.comp_id]
  have hU : IsPullback p d f (Spec.map (𝟙 R) ≫ j) := by
    rw [hρ]
    exact IsPullback.of_hasPullback f j
  have hW : IsPullback c e b (Spec.map (𝟙 S) ≫ v) := by
    rw [hτ]
    exact IsPullback.of_hasPullback b v
  let p₀ := hU₁.lift p (d ≫ Spec.map (𝟙 R)) (by rw [hU.w, Category.assoc])
  let c₀ := hW₁.lift c (e ≫ Spec.map (𝟙 S)) (by rw [hW.w, Category.assoc])
  have hp₀ : p₀ ≫ p₁ = p := hU₁.lift_fst _ _ _
  have hd₀ : p₀ ≫ d₁ = d ≫ Spec.map (𝟙 R) := hU₁.lift_snd _ _ _
  have hc₀ : c₀ ≫ c₁ = c := hW₁.lift_fst _ _ _
  have he₀ : c₀ ≫ e₁ = e ≫ Spec.map (𝟙 S) := hW₁.lift_snd _ _ _
  have hU₀ : IsPullback p₀ d d₁ (Spec.map (𝟙 R)) := hU.of_right' hU₁
  have hW₀ : IsPullback c₀ e e₁ (Spec.map (𝟙 S)) := hW.of_right' hW₁
  let : IsOpenImmersion p₀ := MorphismProperty.of_isPullback hU₀.flip inferInstance
  let : IsOpenImmersion c₀ := MorphismProperty.of_isPullback hW₀.flip inferInstance
  have hq₀ : q ≫ p₀ = c₀ ≫ q₁ := by
    apply hU₁.hom_ext
    · simp only [Category.assoc, hp₀, hq₁]
      rw [← Category.assoc, hc₀]
      exact chartUpper_fst a b f g h j v σ hv
    · calc
        (q ≫ p₀) ≫ d₁ = (q ≫ d) ≫ Spec.map (𝟙 R) := by
          rw [Category.assoc, hd₀, Category.assoc]
        _ = (e ≫ Spec.map σ) ≫ Spec.map (𝟙 R) := by rw [chartUpper_snd]
        _ = (e ≫ Spec.map (𝟙 S)) ≫ Spec.map σ := by
          simpa only [Category.assoc] using congrArg (fun k => e ≫ k) hσ.symm
        _ = (c₀ ≫ e₁) ≫ Spec.map σ := congrArg (fun k => k ≫ Spec.map σ) he₀.symm
        _ = (c₀ ≫ q₁) ≫ d₁ := by simp only [Category.assoc, hb₁]
  have ht : Spec.map σ ≫ (Spec.map (𝟙 R) ≫ j) =
      (Spec.map (𝟙 S) ≫ v) ≫ g := by rw [hρ, hτ]; exact hv
  have hqT : q ≫ (p₀ ≫ p₁) = (c₀ ≫ c₁) ≫ a := by
    rw [hp₀, hc₀]
    exact chartUpper_fst a b f g h j v σ hv
  let E := (pullback g).obj (((pushforward f).rightDerived n).obj M)
  let F := ((pushforward b).rightDerived n).obj ((pullback a).obj M)
  let β := localMap a b f g h j v σ hv n M p₁ d₁ hU₁ c₁ e₁ hW₁ q₁ hq₁ hb₁
  let γ := chartMap a b f g h j v σ hv n M
  let βT := localMap a b f g h (Spec.map (𝟙 R) ≫ j) (Spec.map (𝟙 S) ≫ v)
    σ ht n M (p₀ ≫ p₁) d (hU₀.paste_horiz hU₁)
    (c₀ ≫ c₁) e (hW₀.paste_horiz hW₁) q hqT
    (chartUpper_snd a b f g h j v σ hv)
  have hr := localMap_refinement a b f g h j v σ hv
    p₁ d₁ hU₁ c₁ e₁ hW₁ q₁ hq₁ hb₁ (𝟙 R) (𝟙 S) σ hσ ht
    p₀ d hU₀ c₀ e hW₀ q hq₀ (chartUpper_snd a b f g h j v σ hv) hqT n M
  have hg := localMap_congr_charts a b f g h
    (Spec.map (𝟙 R) ≫ j) j (Spec.map (𝟙 S) ≫ v) v σ σ ht hv n M
    (p₀ ≫ p₁) p d (hU₀.paste_horiz hU₁) (IsPullback.of_hasPullback f j)
    (c₀ ≫ c₁) c e (hW₀.paste_horiz hW₁) (IsPullback.of_hasPullback b v)
    q q hqT (chartUpper_snd a b f g h j v σ hv)
    (chartUpper_fst a b f g h j v σ hv) (chartUpper_snd a b f g h j v σ hv)
    hρ hτ rfl hp₀ hc₀ rfl
  change (restrictFunctorComp (Spec.map (𝟙 S)) v).hom.app E ≫
      (restrictFunctor (Spec.map (𝟙 S))).map β =
    βT ≫ (restrictFunctorComp (Spec.map (𝟙 S)) v).hom.app F at hr
  change (restrictFunctorCongr hτ).hom.app E ≫ γ =
    βT ≫ (restrictFunctorCongr hτ).hom.app F at hg
  have he : (restrictFunctorCongr hτ.symm).hom = (restrictFunctorCongr hτ).inv := by
    apply NatTrans.ext
    funext L
    apply Scheme.Modules.hom_ext
    intro O
    rw [restrictFunctorCongr_hom_app_app, restrictFunctorCongr_inv_app_app]
  have hβT : (restrictFunctorCongr hτ).inv.app E ≫ βT =
      γ ≫ (restrictFunctorCongr hτ).inv.app F := by
    rw [← cancel_mono ((restrictFunctorCongr hτ).hom.app F)]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← hg, Iso.inv_hom_id_app_assoc]
    exact (Category.comp_id γ).symm
  let I := (restrictFunctorCongr (Spec.map_id S)) ≪≫ (restrictFunctorId (X := Spec S))
  have hi (L : V.Modules) : (restrictFunctorCongr hτ).inv.app L ≫
      (restrictFunctorComp (Spec.map (𝟙 S)) v).hom.app L =
      I.inv.app (L.restrict v) := by
    rw [← he]
    exact restrictFunctor_identity_refinement_hom v (Spec.map (𝟙 S)) (Spec.map_id S) hτ L
  have H : I.inv.app (E.restrict v) ≫ (restrictFunctor (Spec.map (𝟙 S))).map β =
      γ ≫ I.inv.app (F.restrict v) := by
    rw [← hi, ← hi]
    simp only [Category.assoc]
    rw [hr, ← Category.assoc, hβT, Category.assoc]
  change β = γ
  rw [← cancel_mono (I.inv.app (F.restrict v))]
  exact (I.inv.naturality β).trans H

end AlgebraicGeometry.Scheme.Modules.Nonflat
