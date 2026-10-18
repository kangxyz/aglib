/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.LocalRefinement
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ChartCongruence
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ChartCover

/-! # Refinement of the chosen affine chart arrows

The actual fibre products for the smaller chart serve as common source
objects. Their native universal lifts compare both presentations of the
local map, retaining every original open-restriction isomorphism.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

/-- An affine refinement identifies the actual chart arrows through the native restriction
equality and composition isomorphisms. -/
theorem chartMap_refinement
    {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
    (h : IsPullback a b f g) [QuasiCompact f] [QuasiSeparated f]
    (C D : AffineBaseChangeChart g)
    (ρ : C.sourceRing ⟶ D.sourceRing) (τ : C.targetRing ⟶ D.targetRing)
    [IsOpenImmersion (Spec.map ρ)] [IsOpenImmersion (Spec.map τ)]
    (hρ : Spec.map ρ ≫ C.source = D.source) (hτ : Spec.map τ ≫ C.target = D.target)
    (hσ : Spec.map τ ≫ Spec.map C.scalar = Spec.map D.scalar ≫ Spec.map ρ)
    (n : ℕ) (M : U.Modules) [M.IsQuasicoherent] :
    ((restrictFunctorCongr hτ.symm).app
          ((pullback g).obj (((pushforward f).rightDerived n).obj M)) ≪≫
        (restrictFunctorComp (Spec.map τ) C.target).app
          ((pullback g).obj (((pushforward f).rightDerived n).obj M))).hom ≫
      (restrictFunctor (Spec.map τ)).map
        (chartMap a b f g h C.source C.target C.scalar C.comm n M) =
    chartMap a b f g h D.source D.target D.scalar D.comm n M ≫
      ((restrictFunctorCongr hτ.symm).app
          (((pushforward b).rightDerived n).obj ((pullback a).obj M)) ≪≫
        (restrictFunctorComp (Spec.map τ) C.target).app
          (((pushforward b).rightDerived n).obj ((pullback a).obj M))).hom := by
  let p₁ := Limits.pullback.fst f C.source
  let d₁ := Limits.pullback.snd f C.source
  let c₁ := Limits.pullback.fst b C.target
  let e₁ := Limits.pullback.snd b C.target
  let p := Limits.pullback.fst f D.source
  let d := Limits.pullback.snd f D.source
  let c := Limits.pullback.fst b D.target
  let e := Limits.pullback.snd b D.target
  let q₁ := chartUpper a b f g h C.source C.target C.scalar C.comm
  let q := chartUpper a b f g h D.source D.target D.scalar D.comm
  let hU₁ := IsPullback.of_hasPullback f C.source
  let hW₁ := IsPullback.of_hasPullback b C.target
  have hU : IsPullback p d f (Spec.map ρ ≫ C.source) := by
    rw [hρ]
    exact IsPullback.of_hasPullback f D.source
  have hW : IsPullback c e b (Spec.map τ ≫ C.target) := by
    rw [hτ]
    exact IsPullback.of_hasPullback b D.target
  let p₀ := hU₁.lift p (d ≫ Spec.map ρ) (by rw [hU.w, Category.assoc])
  let c₀ := hW₁.lift c (e ≫ Spec.map τ) (by rw [hW.w, Category.assoc])
  have hp₀ : p₀ ≫ p₁ = p := hU₁.lift_fst _ _ _
  have hd₀ : p₀ ≫ d₁ = d ≫ Spec.map ρ := hU₁.lift_snd _ _ _
  have hc₀ : c₀ ≫ c₁ = c := hW₁.lift_fst _ _ _
  have he₀ : c₀ ≫ e₁ = e ≫ Spec.map τ := hW₁.lift_snd _ _ _
  have hU₀ : IsPullback p₀ d d₁ (Spec.map ρ) := hU.of_right' hU₁
  have hW₀ : IsPullback c₀ e e₁ (Spec.map τ) := hW.of_right' hW₁
  let : IsOpenImmersion p₀ := MorphismProperty.of_isPullback hU₀.flip inferInstance
  let : IsOpenImmersion c₀ := MorphismProperty.of_isPullback hW₀.flip inferInstance
  have hq₀ : q ≫ p₀ = c₀ ≫ q₁ := by
    apply hU₁.hom_ext
    · calc
        (q ≫ p₀) ≫ p₁ = q ≫ p := by rw [Category.assoc, hp₀]
        _ = c ≫ a := chartUpper_fst a b f g h D.source D.target D.scalar D.comm
        _ = (c₀ ≫ q₁) ≫ p₁ := by
          rw [Category.assoc, chartUpper_fst, ← Category.assoc, hc₀]
    · calc
        (q ≫ p₀) ≫ d₁ = (q ≫ d) ≫ Spec.map ρ := by
          rw [Category.assoc, hd₀, Category.assoc]
        _ = (e ≫ Spec.map D.scalar) ≫ Spec.map ρ := by rw [chartUpper_snd]
        _ = (e ≫ Spec.map τ) ≫ Spec.map C.scalar := by
          simpa only [Category.assoc] using congrArg (fun k => e ≫ k) hσ.symm
        _ = (c₀ ≫ e₁) ≫ Spec.map C.scalar :=
          congrArg (fun k => k ≫ Spec.map C.scalar) he₀.symm
        _ = (c₀ ≫ q₁) ≫ d₁ := by
          simp only [Category.assoc]
          exact congrArg (fun k => c₀ ≫ k)
            (chartUpper_snd a b f g h C.source C.target C.scalar C.comm).symm
  have ht : Spec.map D.scalar ≫ (Spec.map ρ ≫ C.source) =
      (Spec.map τ ≫ C.target) ≫ g := by rw [hρ, hτ]; exact D.comm
  have hqT : q ≫ (p₀ ≫ p₁) = (c₀ ≫ c₁) ≫ a := by
    rw [hp₀, hc₀]
    exact chartUpper_fst a b f g h D.source D.target D.scalar D.comm
  let βT := localMap a b f g h (Spec.map ρ ≫ C.source) (Spec.map τ ≫ C.target)
    D.scalar ht n M (p₀ ≫ p₁) d (hU₀.paste_horiz hU₁)
    (c₀ ≫ c₁) e (hW₀.paste_horiz hW₁) q hqT
    (chartUpper_snd a b f g h D.source D.target D.scalar D.comm)
  have hr := localMap_refinement a b f g h C.source C.target C.scalar C.comm
    p₁ d₁ hU₁ c₁ e₁ hW₁ q₁
    (chartUpper_fst a b f g h C.source C.target C.scalar C.comm)
    (chartUpper_snd a b f g h C.source C.target C.scalar C.comm)
    ρ τ D.scalar hσ ht p₀ d hU₀ c₀ e hW₀ q hq₀
    (chartUpper_snd a b f g h D.source D.target D.scalar D.comm) hqT n M
  have hg := localMap_congr_charts a b f g h
    (Spec.map ρ ≫ C.source) D.source (Spec.map τ ≫ C.target) D.target
    D.scalar D.scalar ht D.comm n M (p₀ ≫ p₁) p d
    (hU₀.paste_horiz hU₁) (IsPullback.of_hasPullback f D.source)
    (c₀ ≫ c₁) c e (hW₀.paste_horiz hW₁) (IsPullback.of_hasPullback b D.target)
    q q hqT (chartUpper_snd a b f g h D.source D.target D.scalar D.comm)
    (chartUpper_fst a b f g h D.source D.target D.scalar D.comm)
    (chartUpper_snd a b f g h D.source D.target D.scalar D.comm)
    hρ hτ rfl hp₀ hc₀ rfl
  let E := (pullback g).obj (((pushforward f).rightDerived n).obj M)
  let F := ((pushforward b).rightDerived n).obj ((pullback a).obj M)
  change (restrictFunctorComp (Spec.map τ) C.target).hom.app E ≫
      (restrictFunctor (Spec.map τ)).map
        (chartMap a b f g h C.source C.target C.scalar C.comm n M) =
    βT ≫ (restrictFunctorComp (Spec.map τ) C.target).hom.app F at hr
  change (restrictFunctorCongr hτ).hom.app E ≫
      chartMap a b f g h D.source D.target D.scalar D.comm n M =
    βT ≫ (restrictFunctorCongr hτ).hom.app F at hg
  have he : (restrictFunctorCongr hτ.symm).hom = (restrictFunctorCongr hτ).inv := by
    apply NatTrans.ext
    funext L
    apply Scheme.Modules.hom_ext
    intro O
    rw [restrictFunctorCongr_hom_app_app, restrictFunctorCongr_inv_app_app]
  have hβT : (restrictFunctorCongr hτ).inv.app E ≫ βT =
      chartMap a b f g h D.source D.target D.scalar D.comm n M ≫
        (restrictFunctorCongr hτ).inv.app F := by
    rw [← cancel_mono ((restrictFunctorCongr hτ).hom.app F)]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← hg, Iso.inv_hom_id_app_assoc, Category.comp_id]
  simp only [Iso.trans_hom, Iso.app_hom, he, Category.assoc]
  rw [hr, ← Category.assoc, hβT, Category.assoc]

end AlgebraicGeometry.Scheme.Modules.Nonflat
