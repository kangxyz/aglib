/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.PointedCurveDegreeTwo
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.EtaleCyclicTrivialization
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Etale
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Descent.SurjectiveAffine

/-! # Cyclic degree two for a pointed smooth proper curve

The original finite étale splitting cover supplies cyclic coordinates only on
that cover. The original section and curve are pulled back along its actual
map. Existing étale exchange and affine constructibility descent transport the
positive-section roots theorem to the original constant coefficient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- The original cyclic second image is constructible. No projective embedding,
Picard representative, or roots coordinate on the original base is required. -/
theorem isConstructible_cyclicHigherDirectImage_two_pointedCurve
    {X S : Scheme.{u}} [IsAffine S] [IsIntegral S]
    (f : X ⟶ S) [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyConnected f] (o : S ⟶ X) (ho : o ≫ f = 𝟙 S)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(S, ⊤))) :
    Constructible.IsConstructible ((higherDirectImage f 2).obj
      (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X)) := by
  classical
  obtain ⟨T, hTsurj, ⟨eT₀⟩⟩ :=
    GroupCohomology.Kummer.exists_finiteEtale_cyclic_trivialization S n hn hinv
  let b := T.obj.hom
  let : Surjective b := hTsurj
  let : IsAffine T.obj.left := isAffine_of_isAffineHom b
  let Y := pullback b f
  let p : Y ⟶ T.obj.left := pullback.fst b f
  let a : Y ⟶ X := pullback.snd b f
  let : SmoothOfRelativeDimension 1 p :=
    (@MorphismProperty.IsStableUnderBaseChange.of_isPullback
      Scheme.{u} _ (@SmoothOfRelativeDimension 1)
      (smoothOfRelativeDimension_isStableUnderBaseChange 1))
      (IsPullback.of_hasPullback b f).flip
      (inferInstanceAs (SmoothOfRelativeDimension 1 f))
  let : IsProper p := inferInstanceAs (IsProper (pullback.fst b f))
  let : GeometricallyConnected p :=
    inferInstanceAs (GeometricallyConnected (pullback.fst b f))
  let oT : T.obj.left ⟶ Y := pullback.lift (𝟙 _) (b ≫ o) (by
    rw [Category.id_comp, Category.assoc, ho, Category.comp_id])
  have hoT : oT ≫ p = 𝟙 _ := pullback.lift_fst _ _ _
  let value := ConstantFinite.value (ULift.{u} (ZMod n))
  let F := ConstantFinite.coefficient (ULift.{u} (ZMod n)) X
  have hT := levelInvertible b n hinv
  have hY := levelInvertible p n hT
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Y) := HasExt.standard _
  have hroots : Constructible.IsConstructible
      ((higherDirectImage p 2).obj (mu Y n)) :=
    isConstructible_rootsHigherDirectImage_two_pointedCurve.{u, u + 2}
      p oT hoT n hn hY hT
  let eT : mu T.obj.left n ≅
      ConstantFinite.coefficient (ULift.{u} (ZMod n)) T.obj.left :=
    (rootsPullbackIso b n hn hinv).symm ≪≫ eT₀
  let eY : mu Y n ≅ ConstantFinite.coefficient (ULift.{u} (ZMod n)) Y :=
    (rootsPullbackIso p n hn hT).symm ≪≫ (inverseImage p).mapIso eT ≪≫
      (inverseImageConstantIso p).app value
  let eF : (inverseImage a).obj F ≅ mu Y n :=
    (inverseImageConstantIso a).app value ≪≫ eY.symm
  let : IsIso (higherBaseChangeMap f p b a pullback.condition 2) :=
    higherBaseChangeMap_etale_isIso f b 2
  let E : (inverseImage b).obj ((higherDirectImage f 2).obj F) ≅
      (higherDirectImage p 2).obj (mu Y n) :=
    asIso ((higherBaseChangeMap f p b a pullback.condition 2).app F) ≪≫
      (higherDirectImage p 2).mapIso eF
  exact Constructible.isConstructible_of_surjective_pullback_of_isAffine b
    ((higherDirectImage f 2).obj F)
    ((Constructible.isConstructible_iff_of_iso E).mpr hroots)

end AlgebraicGeometry.Scheme.EtaleCohomology
