/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.SmoothStagePointedZero
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ArrowSmoothStageSystem
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ArithmeticDirectImageEffacement
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.FiniteTypeArrowBaseChangeFamilies
public import Aglib.RingTheory.FiniteType.ArithmeticArrowStages
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.ZMod

/-! # Original arbitrary-arrow curve positive-degree effacement by arithmetic continuity

Only the auxiliary model ring is arithmetic finite type. The original arrow
and its source and target rings are arbitrary. Every stage uses the actual
genuine module direct image and its proved injectivity. The original bounded
class representative, geometric point, ordinary mate and counit are retained.
This proves pointed positive-degree effacement for these actual smooth curve base
changes; no all-degree smooth exchange is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.FiniteTypeArrowLimit.TargetBaseChange
open Algebra.FiniteTypeArrowLimit EtaleCohomology EtaleCohomology.Continuity
open EtaleCohomology.Coefficients
universe u
attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (α : A →ₐ[R] B)

/-- The quiver of the opposite finite-stage category. -/
local instance positiveArrowIndexQuiver : Quiver (Index A B)ᵒᵖ :=
  (inferInstance : Category (Index A B)ᵒᵖ).toQuiver
/-- The quiver of the double-opposite finite-stage category. -/
local instance positiveArrowDoubleOppositeQuiver : Quiver ((Index A B)ᵒᵖ)ᵒᵖ :=
  (inferInstance : Category ((Index A B)ᵒᵖ)ᵒᵖ).toQuiver

/-- The original arbitrary-arrow class admits an etale zero chart retaining
its original geometric point. Arithmetic hypotheses concern only the model R. -/
theorem exists_arbitrary_arrow_pointed_positive_refinement
    (q : ℕ) (hq : 0 < q)
    [Algebra.FiniteType ℤ R]
    {X : Scheme.{u}} [IsAffine X] (p : X ⟶ Spec (.of R))
    [SmoothOfRelativeDimension 1 p]
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (I : ModuleSheaf (Spec (.of B)) (ULift.{u + 1} (ZMod n))) [hI : Injective I]
    (c : Sheaf.H.{u + 2} ((inverseImage
      (pullback.fst (Spec.algebraMap R B) p)).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (.of B))
        (ULift.{u + 1} (ZMod n)))).obj I)) q)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ pullback (Spec.algebraMap R A) p) :
    ∃ (U : (pullback (Spec.algebraMap R A) p).Etale) (xU : Spec (.of Ω) ⟶ U.left),
      xU ≫ U.hom = x ∧
      cohomologyPullback.{u, u + 2, u + 2}
        (pullback.snd U.hom (familyArrow α p)) _ q c = 0 := by
  let : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  let M := (SheafOfModules.toSheaf (constantRing (Spec (.of B))
    (ULift.{u + 1} (ZMod n)))).obj I
  have hM : n • 𝟙 M = 0 := Functor.map_nsmul_id_eq_zero
    (SheafOfModules.toSheaf (constantRing (Spec (.of B))
      (ULift.{u + 1} (ZMod n)))) I n
    (ModuleCat.Sheaf.ConstantRing.uLiftZMod_nsmul_id_eq_zero
      (Scheme.smallEtaleTopology (Spec (.of B))) n I)
  let F : (boundedCoefficientProperty (Spec (.of B)) n).FullSubcategory := ⟨M, hM⟩
  apply (smoothStageSystem α p).exists_pointed_zero_of_stage_zero
    (familyArrow α p)
    (fun i => sourceStageFamily α p i.unop)
    (fun i => sourceFamilyLeg α p i.unop)
    (fun i => stageFamilyArrow α p i.unop)
    (fun i => familyArrow_cone α p i.unop) n hn F q x ?_ c
  intro i ci
  let s := i.unop.unop
  let : Algebra (sourceStage α s) (targetStage α s) :=
    (stageMap α s).toRingHom.toAlgebra
  let : Algebra.FiniteType ℤ (sourceStage α s) := sourceStage_finiteType_int α s
  let : Algebra.FiniteType ℤ (targetStage α s) := targetStage_finiteType_int α s
  have hn' : IsUnit (n : sourceStage α s) := by
    simpa only [map_natCast] using hunit.map (algebraMap R (sourceStage α s))
  have H : IsPullback (stageFamilyArrow α p i.unop)
      (pullback.fst (Spec.algebraMap R (targetStage α s)) p)
      (pullback.fst (Spec.algebraMap R (sourceStage α s)) p)
      (Spec.algebraMap (sourceStage α s) (targetStage α s)) :=
    stageFamily_isPullback α p i.unop
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{u} 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have hsmooth : SmoothOfRelativeDimension 1
      (pullback.fst (Spec.algebraMap R (sourceStage α s)) p) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension.{u} 1)
      (IsPullback.of_hasPullback (Spec.algebraMap R (sourceStage α s)) p).flip
      (inferInstance : SmoothOfRelativeDimension 1 p)
  exact @exists_arithmetic_directImage_pointed_positive_refinement.{u}
    q hq
    (sourceStage α s) (targetStage α s) _ _ _ _ _
    (sourceStageFamily α p i.unop) ((schemeDiagram α p).obj i.unop) (Spec (.of B))
    (pullback.fst (Spec.algebraMap R (sourceStage α s)) p) hsmooth
    (stageFamilyArrow α p i.unop)
    (pullback.fst (Spec.algebraMap R (targetStage α s)) p)
    H n hn hn' ((targetSpecCone α).π.app i.unop) I hI ci Ω _ _
    (x ≫ sourceFamilyLeg α p i.unop)

end AlgebraicGeometry.Scheme.FiniteTypeArrowLimit.TargetBaseChange
