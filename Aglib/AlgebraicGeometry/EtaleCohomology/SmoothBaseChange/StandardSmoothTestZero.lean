/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.StandardSmoothPositive
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PointedPullbackLocalZero
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.StandardAffinePointedTest

/-! # Original pointed étale-test class refinement on a standard-smooth curve

The affine chart supplier and the arithmetic class supplier are separate
proved inputs. This lemma returns the actual original test restriction and
its original mark, without a change of coefficient base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients FiniteTypeArrowLimit.TargetBaseChange
universe u
attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- Every original étale-test class is locally zero at its original geometric mark. -/
theorem exists_standardSmooth_test_positive_zero
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A C] [Algebra.IsStandardSmoothOfRelativeDimension 1 A C]
    (f : A →+* B) {Y : Scheme.{u}}
    (a : Y ⟶ Spec (.of C)) (b : Y ⟶ Spec (.of B))
    (H : IsPullback a b (Spec.algebraMap A C) (Spec.map (CommRingCat.ofHom f)))
    (q : ℕ) (hq : 0 < q) (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : A))
    (I : ModuleSheaf (Spec (.of B)) (ULift.{u + 1} (ZMod n))) [hI : Injective I]
    (U : (Spec (.of C)).Etale)
    (c : Sheaf.H.{u + 2} ((inverseImage (pullback.snd U.hom a)).obj
      ((inverseImage b).obj ((SheafOfModules.toSheaf
        (constantRing (Spec (.of B)) (ULift.{u + 1} (ZMod n)))).obj I))) q)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ U.left) :
    ∃ (V : (Spec (.of C)).Etale) (g : V ⟶ U) (z : Spec (.of Ω) ⟶ V.left),
      z ≫ g.left = ξ ∧ fibreProductCohomologyRestriction a g
        ((inverseImage b).obj ((SheafOfModules.toSheaf
          (constantRing (Spec (.of B)) (ULift.{u + 1} (ZMod n)))).obj I)) q c = 0 := by
  let M := (SheafOfModules.toSheaf (constantRing (Spec (.of B))
    (ULift.{u + 1} (ZMod n)))).obj I
  let F := (inverseImage b).obj M
  obtain ⟨D, hD, hAD, hsm, j, ξD, hj, hξ, hvA⟩ :=
    exists_standardSmooth_affine_pointed_test (A := A) U Ω ξ
  let := hD
  let := hAD
  let := hsm
  let := hj
  let v := j ≫ U.hom
  let V : (Spec (.of C)).Etale := Scheme.Etale.mk v
  let g : V ⟶ U := MorphismProperty.Over.homMk j rfl
  let d := fibreProductCohomologyRestriction a g F q c
  let r := pullback.snd V.hom a
  let aV := pullback.fst V.hom a
  let bV := r ≫ b
  have HV : IsPullback aV bV (Spec.algebraMap A D) (Spec.map (CommRingCat.ofHom f)) := by
    have h := (IsPullback.of_hasPullback V.hom a).paste_vert H
    change IsPullback aV bV (v ≫ Spec.algebraMap A C)
      (Spec.map (CommRingCat.ofHom f)) at h
    exact Eq.mp (congrArg
      (fun t : Spec (.of D) ⟶ Spec (.of A) =>
        IsPullback aV bV t (Spec.map (CommRingCat.ofHom f))) hvA) h
  let E : (inverseImage r).obj F ≅ (inverseImage bV).obj M :=
    ((inverseImageComp b r).app M).symm
  obtain ⟨W, z, hz, hc⟩ := exists_standardSmooth_pointed_positive_refinement
    f aV bV HV q hq n hn hunit I (Sheaf.H.map E.hom q d) Ω
    ξD
  have hc' : cohomologyPullback.{u, u + 2, u + 2}
      (pullback.snd W.hom aV) ((inverseImage r).obj F) q d = 0 := by
    apply Sheaf.H.map_injective_of_isIso
      ((inverseImage (pullback.snd W.hom aV)).map E.hom) q
    exact (cohomologyPullback_coefficientMap (pullback.snd W.hom aV) E.hom q d).symm.trans
      (hc.trans (map_zero _).symm)
  let t : W.left ⟶ V.left := W.hom
  let : Etale t := W.prop
  let : Etale V.hom := V.prop
  let Z : (Spec (.of C)).Etale := Scheme.Etale.mk (t ≫ V.hom)
  let k : Z ⟶ V := MorphismProperty.Over.homMk t rfl
  refine ⟨Z, k ≫ g, z, ?_, ?_⟩
  · change z ≫ (t ≫ j) = ξ
    exact (Category.assoc z t j).symm.trans
      ((congrArg (fun s => s ≫ j) hz).trans hξ)
  · exact (fibreProductCohomologyRestriction_comp a F q g k c).trans
      (fibreProductCohomologyRestriction_eq_zero_of_target_pullback a k F q d hc')

end AlgebraicGeometry.Scheme.EtaleCohomology
