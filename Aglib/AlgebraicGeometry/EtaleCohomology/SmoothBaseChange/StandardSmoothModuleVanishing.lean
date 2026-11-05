/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.StandardSmoothTestZero
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.HigherImageLocalZero

/-! # Genuine injective vanishing on every original standard-smooth curve test

Every original étale test is refined at its original geometric point by an
affine chart. This chart is standard smooth of relative dimension one over
the original base. Arithmetic continuity therefore kills its original class
without changing the coefficient base or asserting that inverse image
preserves injectives. Native restriction composition returns the result to
the original test, proving vanishing of the actual higher-image sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients FiniteTypeArrowLimit.TargetBaseChange
universe u
attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- Full étale-test vanishing, not merely vanishing on the identity test. -/
theorem higherDirectImage_standardSmooth_injective_positive_isZero
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A C] [Algebra.IsStandardSmoothOfRelativeDimension 1 A C]
    (f : A →+* B) {Y : Scheme.{u}}
    (a : Y ⟶ Spec (.of C)) (b : Y ⟶ Spec (.of B))
    (H : IsPullback a b (Spec.algebraMap A C) (Spec.map (CommRingCat.ofHom f)))
    (q : ℕ) (hq : 0 < q) (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : A))
    (I : ModuleSheaf (Spec (.of B)) (ULift.{u + 1} (ZMod n))) [hI : Injective I] :
    IsZero ((higherDirectImage a q).obj ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (.of B))
        (ULift.{u + 1} (ZMod n)))).obj I))) := by
  let M := (SheafOfModules.toSheaf (constantRing (Spec (.of B))
    (ULift.{u + 1} (ZMod n)))).obj I
  let F := (inverseImage b).obj M
  apply higherDirectImage_isZero_of_pointed_local_class_zero a F q
  intro U c x
  let L := U.left.residueField x
  let Ω := AlgebraicClosure L
  let ξ : Spec (.of Ω) ⟶ U.left :=
    Spec.algebraMap L Ω ≫ U.left.fromSpecResidueField x
  obtain ⟨V, g, z, hz, hc⟩ := exists_standardSmooth_test_positive_zero
    f a b H q hq n hn hunit I U c Ω ξ
  refine ⟨V, g, z default, ?_, hc⟩
  have hp := congrArg (fun t : Spec (.of Ω) ⟶ U.left => t default) hz
  exact hp.trans (Scheme.fromSpecResidueField_apply (X := U.left) x
    ((Spec.algebraMap L Ω) default))

end AlgebraicGeometry.Scheme.EtaleCohomology
