/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.ArithmeticCurvePointedProducer
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.HigherImageLocalZero
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PointedPullbackLocalZero
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.ModuleInjectiveTests

/-! # Actual first higher-image vanishing on arithmetic smooth curves

Every original etale test is again a smooth arithmetic curve. The genuine
injective remains on the unchanged coefficient base. Its class is transported
only through the original inverse-image composition isomorphism, killed at
the original geometric point, and returned to the native restriction map.
This proves degree one, not all-degree smooth exchange.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u
attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- The original first higher image of a pulled-back genuine injective is zero. -/
theorem higherDirectImage_arithmetic_curve_injective_one_isZero
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 p]
    (a : Y ⟶ X) (b : Y ⟶ Spec (.of S))
    (H : IsPullback a b p (Spec.algebraMap R S))
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (I : ModuleSheaf (Spec (.of S)) (ULift.{u + 1} (ZMod n))) [Injective I] :
    IsZero ((higherDirectImage a 1).obj ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (.of S))
        (ULift.{u + 1} (ZMod n)))).obj I))) := by
  let M := (SheafOfModules.toSheaf (constantRing (Spec (.of S))
    (ULift.{u + 1} (ZMod n)))).obj I
  let F := (inverseImage b).obj M
  apply higherDirectImage_isZero_of_pointed_local_class_zero a F 1
  intro U c x
  let v := pullback.snd U.hom a
  let aU := pullback.fst U.hom a
  let bU := v ≫ b
  let pU := U.hom ≫ p
  let : SmoothOfRelativeDimension 1 pU := by
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 1 U.hom p
  have HU : IsPullback aU bU pU (Spec.algebraMap R S) :=
    (IsPullback.of_hasPullback U.hom a).paste_vert H
  let E : (inverseImage v).obj F ≅ (inverseImage bU).obj M :=
    ((inverseImageComp b v).app M).symm
  let cU := Sheaf.H.map E.hom 1 c
  let L := U.left.residueField x
  let Ω := AlgebraicClosure L
  let ξ : Spec (.of Ω) ⟶ U.left :=
    Spec.algebraMap L Ω ≫ U.left.fromSpecResidueField x
  obtain ⟨W, z, hz, hc⟩ := exists_arithmetic_curve_pointed_H1_refinement
    R S pU aU bU HU n hn hunit I cU Ω ξ
  have hc' : cohomologyPullback.{u, u + 2, u + 2}
      (pullback.snd W.hom aU) ((inverseImage v).obj F) 1 c = 0 := by
    apply Sheaf.H.map_injective_of_isIso ((inverseImage (pullback.snd W.hom aU)).map E.hom) 1
    rw [← cohomologyPullback_coefficientMap]
    exact hc.trans (map_zero _).symm
  let t : W.left ⟶ U.left := W.hom
  let : Etale t := W.prop
  let V : X.Etale := Scheme.Etale.mk (t ≫ U.hom)
  let g : V ⟶ U := MorphismProperty.Over.homMk t rfl
  refine ⟨V, g, z default, ?_, ?_⟩
  · have hpoint := congrArg (fun k : Spec (.of Ω) ⟶ U.left => k default) hz
    exact hpoint.trans (Scheme.fromSpecResidueField_apply (X := U.left) x
      ((Spec.algebraMap L Ω) default))
  · exact fibreProductCohomologyRestriction_eq_zero_of_target_pullback a g F 1 c hc'

/-- The canonical first exchange is invertible on genuine Z/n injectives. -/
theorem higherBaseChangeMap_arithmetic_curve_zmodInjective_one_isIso
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 p]
    (a : Y ⟶ X) (b : Y ⟶ Spec (.of S))
    (H : IsPullback a b p (Spec.algebraMap R S))
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (I : Proper.Reduction.ZModSheaf (Spec (.of S)) n) [Injective I] :
    IsIso ((higherBaseChangeMap (Spec.algebraMap R S) a p b H.w 1).app
      ((Proper.Reduction.zmodUnderlying (Spec (.of S)) n).obj I)) := by
  exact higherBaseChangeMap_zmodInjective_isIso_of_ringed_target_vanishing
    (Spec.algebraMap R S) a p b H.w n 0
    (fun J => higherDirectImage_arithmetic_curve_injective_one_isZero
      R S p a b H n hn hunit J) I

end AlgebraicGeometry.Scheme.EtaleCohomology
