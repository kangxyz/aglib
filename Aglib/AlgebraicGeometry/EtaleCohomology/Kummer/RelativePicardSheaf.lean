/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativeNormalizedPicard
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Pushforward
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootsComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootCover
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackComposition
public import Aglib.AlgebraicGeometry.Picard.Fppf

/-!
# The base part of relative Kummer cohomology

For proper flat geometrically integral families over a locally Noetherian base, universal
O-connectedness identifies actual global units after every base change. With a section, the
kernel of the normalized Kummer Picard map is precisely original roots cohomology pulled
back from the test scheme. This exactness is the input to the small étale sheaf comparison;
no pointwise injectivity, representer, or finite étale torsion kernel is assumed here.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u w w' e

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open RelativePicard

section Effacement

variable {B Y Z : Scheme.{u}}
    [HasExt.{w} (AbelianSheaf.{u, u + 1} B)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Z)]

/-- Original roots cohomology composes without a connectedness or geometric-point input. -/
theorem rootsPullback_comp_unrestricted (f : Y ⟶ B) (g : Z ⟶ Y)
    (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(B, ⊤)))
    (a : Sheaf.H.{w} (mu B n) 1) :
    rootsCohomologyPullback (g ≫ f) n hn hi 1 a =
      rootsCohomologyPullback g n hn (levelInvertible f n hi) 1
        (rootsCohomologyPullback f n hn hi 1 a) := by
  have ht := GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso_comp f g n hn hi
  have hc := cohomologyPullback_comp f g (mu B n) 1 a
  have hm := cohomologyPullback_coefficientMap g (rootsPullbackIso f n hn hi).hom 1
    (cohomologyPullback f (mu B n) 1 a)
  change Sheaf.H.map (rootsPullbackIso (g ≫ f) n hn hi).hom 1
    (cohomologyPullback (g ≫ f) (mu B n) 1 a) = _
  rw [← ht, Sheaf.H.map_comp_apply, Sheaf.H.map_comp_apply, hc, ← hm]
  rfl

end Effacement

/-- A unit boundary vanishes on its original finite étale root cover. -/
theorem rootsPullback_unitsBoundary_rootCover (B : Scheme.{u})
    [hB : HasExt.{w} (AbelianSheaf.{u, u + 1} B)]
    (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(B, ⊤))) (a : Additive Γ(B, ⊤)ˣ)
    [hV : HasExt.{w'} (AbelianSheaf.{u, u + 1}
      (Group.RootCover.cover B n hn hi a.toMul).obj.left)] :
    rootsCohomologyPullback (Group.RootCover.cover B n hn hi a.toMul).obj.hom n hn hi 1
      (unitsBoundary B n hn hi a) = 0 := by
  let V := (Group.RootCover.cover B n hn hi a.toMul).obj.left
  let f : V ⟶ B := (Group.RootCover.cover B n hn hi a.toMul).obj.hom
  let : HasExt.{w'} (AbelianSheaf.{u, u + 1} V) := hV
  have hnat := DFunLike.congr_fun (@unitsBoundary_pullback B V hB hV f n hn hi) a
  have hz : unitsBoundary V n hn (levelInvertible f n hi) (unitsPullback f a) = 0 := by
    apply (unitsBoundary_eq_zero_iff V n hn (levelInvertible f n hi) _).mpr
    obtain ⟨b, hb⟩ := Group.RootCover.cover_hasRoot B n hn hi a.toMul
    exact ⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩
  exact hnat.trans hz

/-- Every original roots `H¹` class is killed by a pointed étale refinement: first trivialize
its actual Picard class Zariski locally, then take the actual finite étale unit-root cover. -/
theorem exists_etale_rootsPullback_eq_zero (B : Scheme.{u})
    [hB : HasExt.{w} (AbelianSheaf.{u, u + 1} B)]
    [hAll : ∀ Y : Scheme.{u}, HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(B, ⊤)))
    (a : Sheaf.H.{w} (mu B n) 1) (x : B) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ B) (_ : Etale f) (y : Y),
      f y = x ∧ @rootsCohomologyPullback B Y hB (hAll Y) f n hn hi 1 a = 0 := by
  obtain ⟨𝒰, h𝒰⟩ := (Scheme.mem_grothendieckTopology_iff).mp
    (RelativePicard.vanishingSieve_mem_zariskiTopology (@rootsPicardMap B hB n a))
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
  let f := 𝒰.f i
  let b := @rootsCohomologyPullback B (𝒰.X i) hB (hAll (𝒰.X i)) f n hn hi 1 a
  let hi' := levelInvertible f n hi
  have hb : rootsPicardMap (𝒰.X i) n b = 0 := by
    have hnat := DFunLike.congr_fun
      (@rootsPicardMap_pullback B (𝒰.X i) hB (hAll (𝒰.X i)) f n hn hi) a
    exact hnat.trans (h𝒰 _ _ ⟨i⟩)
  obtain ⟨z, hz⟩ := (exact_unitsQuotientBoundary_rootsPicardMap
    (𝒰.X i) n hn hi' b).mp hb
  obtain ⟨c, hc⟩ : ∃ c, unitsBoundary (𝒰.X i) n hn hi' c = b := by
    induction z using QuotientAddGroup.induction_on with
    | H c => exact ⟨c, hz⟩
  let V := Group.RootCover.cover (𝒰.X i) n hn hi' c.toMul
  let g := V.obj.hom
  have : Surjective g := Group.RootCover.cover_surjective _ n hn hi' c.toMul
  obtain ⟨v, hv⟩ := (surjective_iff g).mp inferInstance y
  refine ⟨V.obj.left, g ≫ f, inferInstance, v, ?_, ?_⟩
  · exact (congrArg f hv).trans hy
  · rw [@rootsPullback_comp_unrestricted B (𝒰.X i) V.obj.left
      hB (hAll (𝒰.X i)) (hAll V.obj.left) f g n hn hi a]
    change rootsCohomologyPullback g n hn hi' 1 b = 0
    rw [← hc]
    exact rootsPullback_unitsBoundary_rootCover (𝒰.X i) n hn hi' c

variable {S X : Scheme.{u}} (p : X ⟶ S)
    [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]

/-- Universal O-connectedness supplies actual global-unit preimages, including on
nonreduced and non-Noetherian test schemes. -/
theorem unitsPullback_pullback_snd_surjective (T : Over S) :
    Function.Surjective (unitsPullback (pullback.snd p T.hom)) := by
  let e := RingEquiv.ofBijective (pullback.snd p T.hom).appTop.hom
    (bijective_app_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral p T.hom ⊤)
  intro a
  obtain ⟨b, hb⟩ := (Units.mapEquiv e.toMulEquiv).surjective a.toMul
  exact ⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩

variable (o : S ⟶ X) (ho : o ≫ p = 𝟙 S) (T : Over S)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} T.left)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} (pullback p T.hom))]
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(T.left, ⊤)))

/-- Exactness at the original family `H¹(μ_n)`: the normalized Picard kernel is precisely
original cohomology pulled back from the base, not an extra geometric or finite-kernel input. -/
theorem exact_rootsPullback_rootsNormalizedPicardMap :
    Function.Exact (rootsCohomologyPullback (pullback.snd p T.hom) n hn hinv 1)
      (rootsNormalizedPicardMap p o ho T n hn
        (levelInvertible (pullback.snd p T.hom) n hinv)) := by
  let q := pullback.snd p T.hom
  let s := originSection p o ho T
  let hi := levelInvertible q n hinv
  let P := rootsCohomologyPullback q n hn hinv 1
  intro a
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := (rootsNormalizedPicardMap_eq_zero_iff p o ho T n hn hi a).mp ha
    let c := rootsCohomologyPullback s n hn hi 1 a
    have hc : rootsPicardMap T.left n c = b := by
      have hnat := DFunLike.congr_fun (rootsPicardMap_pullback s n hn hi) a
      change rootsPicardMap T.left n c =
        ((originRestriction p o ho).app (op T)).hom
          (rootsPicardMap (pullback p T.hom) n a) at hnat
      rw [← hb] at hnat
      exact hnat.trans (DFunLike.congr_fun
        (originRestriction_comp_basePullback p o ho (op T)) b)
    have hd : rootsPicardMap (pullback p T.hom) n (a - P c) = 0 := by
      rw [map_sub]
      have hnat := DFunLike.congr_fun (rootsPicardMap_pullback q n hn hinv) c
      change rootsPicardMap (pullback p T.hom) n (P c) =
        ((basePullback p).app (op T)).hom (rootsPicardMap T.left n c) at hnat
      rw [hnat, hc, hb, sub_self]
    have hex : ∃ u, unitsBoundary (pullback p T.hom) n hn hi u = a - P c := by
      obtain ⟨z, hz⟩ := (exact_unitsQuotientBoundary_rootsPicardMap
        (pullback p T.hom) n hn hi (a - P c)).mp hd
      induction z using QuotientAddGroup.induction_on with
      | H u => exact ⟨u, hz⟩
    obtain ⟨u, hu⟩ := hex
    obtain ⟨v, hv⟩ := unitsPullback_pullback_snd_surjective p T u
    have hv' : P (unitsBoundary T.left n hn hinv v) = a - P c := by
      have hnat := DFunLike.congr_fun (unitsBoundary_pullback q n hn hinv) v
      change P (unitsBoundary T.left n hn hinv v) =
        unitsBoundary (pullback p T.hom) n hn hi (unitsPullback q v) at hnat
      exact hnat.trans ((congrArg (unitsBoundary (pullback p T.hom) n hn hi) hv).trans hu)
    refine ⟨c + unitsBoundary T.left n hn hinv v, ?_⟩
    change P (c + unitsBoundary T.left n hn hinv v) = a
    rw [map_add, hv']
    abel
  · rintro ⟨c, rfl⟩
    apply (rootsNormalizedPicardMap_eq_zero_iff p o ho T n hn hi _).mpr
    refine ⟨rootsPicardMap T.left n c, ?_⟩
    exact (DFunLike.congr_fun (rootsPicardMap_pullback q n hn hinv) c).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
