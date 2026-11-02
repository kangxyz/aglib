/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.SplitThickeningImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.OrdinaryBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Descent.SurjectiveAffine

/-! # Constructibility descent through an actual finite Cartesian square

The original finite base-change mate transports the split-thickening image
result to the inverse image of the original direct image. Surjective descent
then applies to that same coefficient on the affine base. The geometric
square and closed immersion are actual morphisms, not constructibility or
finite-presentation certificates. Producing them over a generic open and
assembling strata are separate geometric steps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

attribute [local instance] hasSheafifyLarge

/-- A finite direct image is constructible when an actual surjective affine
base change admits a surjective closed immersion with finite etale composite.
No flatness, target-coefficient constructibility or FP premise is required. -/
theorem isConstructible_directImage_of_surjective_splitThickening
    {X S X' S' Z : Scheme.{u}} [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    [IsFinite f] [Surjective g] (h : IsPullback g' f' f g)
    (i : Z ⟶ X') [IsClosedImmersion i] [Surjective i]
    [IsFinite (i ≫ f')] [Etale (i ≫ f')]
    {F : AbelianSheaf.{u, u + 1} X} (hF : Constructible.IsConstructible F) :
    Constructible.IsConstructible ((directImage f).obj F) := by
  have : IsFinite f' := MorphismProperty.of_isPullback h (inferInstance : IsFinite f)
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsAffine X' := isAffine_of_isAffineHom f'
  have hF' : Constructible.IsConstructible ((inverseImage g').obj F) :=
    Constructible.isConstructible_pullback_of_isAffine g' hF
  have hImage : Constructible.IsConstructible
      ((directImage f').obj ((inverseImage g').obj F)) :=
    isConstructible_directImage_of_surjectiveClosedImmersion f' i hF'
  have : IsIso ((baseChangeMap f f' g g' h.w.symm).app F) :=
    finiteBaseChange_app_isIso f f' g g' h F
  have hPullback : Constructible.IsConstructible
      ((inverseImage g).obj ((directImage f).obj F)) :=
    (Constructible.isConstructible_iff_of_iso
      (asIso ((baseChangeMap f f' g g' h.w.symm).app F))).mpr hImage
  exact Constructible.isConstructible_of_surjective_pullback_of_isAffine
    g ((directImage f).obj F) hPullback

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
