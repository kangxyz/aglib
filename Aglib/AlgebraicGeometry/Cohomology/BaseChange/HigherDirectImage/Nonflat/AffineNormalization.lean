/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat

/-! # Original affine normalization of the canonical nonflat comparison

The original chart source and target isomorphisms carry the canonical global
map to the original affine geometric cohomology mate. The normalization
retains the actual coefficient arrow and original scalar actions.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

open Cohomology

private theorem cancel_original_chart_isos
    {C : Type*} [Category C] {E A B F : C}
    (s : E ≅ A) (t : F ≅ B) (k : A ⟶ B) :
    s.inv ≫ (s.hom ≫ k ≫ t.inv) ≫ t.hom = k := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

variable {W U V X : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
  (h : IsPullback a b f g) [QuasiCompact f] [QuasiSeparated f]
  {R S : CommRingCat.{u}} (j : Spec R ⟶ X) (v : Spec S ⟶ V) (σ : R ⟶ S)
  [IsOpenImmersion j] [IsOpenImmersion v] (hv : Spec.map σ ≫ j = v ≫ g)
  (n : ℕ) (M : U.Modules) [M.IsQuasicoherent]

/-- The original chart source identification for the higher-image comparison. -/
def chartSourceIso :
    ((pullback g).obj (((pushforward f).rightDerived n).obj M)).restrict v ≅
      (pullback (Spec.map σ)).obj
        (((pushforward (Limits.pullback.snd f j)).rightDerived n).obj
          (M.restrict (Limits.pullback.fst f j))) :=
  (pullbackOpenSquare v (Spec.map σ) g j hv.symm).app _ ≪≫
    (pullback (Spec.map σ)).mapIso
      ((higherDirectImageOpenRestrictionIso (Limits.pullback.fst f j)
        (Limits.pullback.snd f j) f j (IsPullback.of_hasPullback f j) n).app M)

/-- The original chart target identification for the higher-image comparison. -/
def chartTargetIso :
    (((pushforward b).rightDerived n).obj ((pullback a).obj M)).restrict v ≅
      ((pushforward (Limits.pullback.snd b v)).rightDerived n).obj
        (((pullback a).obj M).restrict (Limits.pullback.fst b v)) :=
  (higherDirectImageOpenRestrictionIso (Limits.pullback.fst b v)
    (Limits.pullback.snd b v) b v (IsPullback.of_hasPullback b v) n).app ((pullback a).obj M)

/-- Through the original source and target chart isomorphisms, the actual global arrow is
exactly the actual affine map with the original restricted pullback-unit coefficient. -/
theorem higherDirectImageBaseChangeMap_affine :
    letI : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
    letI : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
    (chartSourceIso f g j v σ hv n M).inv ≫
      (restrictFunctor v).map (higherDirectImageBaseChangeMap a b f g h n M) ≫
      (chartTargetIso a b v n M).hom =
    higherDirectImageAffineMap
      (M := M.restrict (Limits.pullback.fst f j))
      (N := ((pullback a).obj M).restrict (Limits.pullback.fst b v))
      (chartUpper a b f g h j v σ hv) (Limits.pullback.snd b v)
      (Limits.pullback.snd f j) σ (chartUpper_snd a b f g h j v σ hv)
      (chartCoefficient a (Limits.pullback.fst f j) (Limits.pullback.fst b v)
        (chartUpper a b f g h j v σ hv) (chartUpper_fst a b f g h j v σ hv)
        ((pullbackPushforwardAdjunction a).unit.app M)) n := by
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  let C : AffineBaseChangeChart g :=
    { sourceRing := R
      targetRing := S
      source := j
      target := v
      scalar := σ
      source_open := inferInstance
      target_open := inferInstance
      comm := hv }
  rw [higherDirectImageBaseChangeMap_chart a b f g h n M C]
  let s := chartSourceIso f g j v σ hv n M
  let t := chartTargetIso a b v n M
  let k := higherDirectImageAffineMap
    (M := M.restrict (Limits.pullback.fst f j))
    (N := ((pullback a).obj M).restrict (Limits.pullback.fst b v))
    (chartUpper a b f g h j v σ hv) (Limits.pullback.snd b v)
    (Limits.pullback.snd f j) σ (chartUpper_snd a b f g h j v σ hv)
    (chartCoefficient a (Limits.pullback.fst f j) (Limits.pullback.fst b v)
      (chartUpper a b f g h j v σ hv) (chartUpper_fst a b f g h j v σ hv)
      ((pullbackPushforwardAdjunction a).unit.app M)) n
  have hk : chartMap a b f g h j v σ hv n M = s.hom ≫ k ≫ t.inv := by
    simp only [s, t, k, chartSourceIso, chartTargetIso, chartMap, localMap,
      Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
  change s.inv ≫ chartMap a b f g h j v σ hv n M ≫ t.hom = k
  rw [hk]
  exact cancel_original_chart_isos s t k

/-- On every affine chart, the actual global comparison sends the geometric unit pure
tensor to the original geometric cohomology map. The formula uses the original affine
higher-image section equivalences and the actual restricted pullback unit. -/
theorem higherDirectImageBaseChangeMap_affine_one_tmul
    (x : moduleSpecΓFunctor.obj
      (((pushforward (Limits.pullback.snd f j)).rightDerived n).obj
        (M.restrict (Limits.pullback.fst f j)))) :
    let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
    let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
    let P := M.restrict (Limits.pullback.fst f j)
    let Q := ((pullback a).obj M).restrict (Limits.pullback.fst b v)
    let E := ((pushforward (Limits.pullback.snd f j)).rightDerived n).obj P
    let := moduleHigherDirectImageAffine_isQuasicoherent (Limits.pullback.snd f j) P n
    let q := chartUpper a b f g h j v σ hv
    let ψ : P ⟶ (pushforward q).obj Q :=
      chartCoefficient a (Limits.pullback.fst f j) (Limits.pullback.fst b v)
        q (chartUpper_fst a b f g h j v σ hv)
        ((pullbackPushforwardAdjunction a).unit.app M)
    moduleHigherDirectImageAffineSectionsLinearEquiv (Limits.pullback.snd b v) Q
        (injectiveResolution Q) n
        (moduleSpecΓFunctor.map
          ((chartSourceIso f g j v σ hv n M).inv ≫
            (restrictFunctor v).map (higherDirectImageBaseChangeMap a b f g h n M) ≫
              (chartTargetIso a b v n M).hom)
          ((affinePullbackGlobalSectionsIso σ E).hom ((1 : S) ⊗ₜ[R,σ.hom] x))) =
      moduleCohomologyMapAlong q ψ n
        (moduleHigherDirectImageAffineSectionsLinearEquiv (Limits.pullback.snd f j) P
          (injectiveResolution P) n x) := by
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  dsimp only
  rw [higherDirectImageBaseChangeMap_affine a b f g h j v σ hv n M]
  exact higherDirectImageAffineMap_one_tmul
    (M := M.restrict (Limits.pullback.fst f j))
    (N := ((pullback a).obj M).restrict (Limits.pullback.fst b v))
    (chartUpper a b f g h j v σ hv) (Limits.pullback.snd b v)
    (Limits.pullback.snd f j) σ (chartUpper_snd a b f g h j v σ hv)
    (chartCoefficient a (Limits.pullback.fst f j) (Limits.pullback.fst b v)
      (chartUpper a b f g h j v σ hv) (chartUpper_fst a b f g h j v σ hv)
      ((pullbackPushforwardAdjunction a).unit.app M)) n x

end AlgebraicGeometry.Scheme.Modules.Nonflat
