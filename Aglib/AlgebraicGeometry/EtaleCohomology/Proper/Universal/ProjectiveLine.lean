/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Universal.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Universal.ProjectiveLineCharts
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GeometricStalkExchange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ProjectiveLineGeometricTransfer
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricAffineChart
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.StalkUniverse

/-! # Universal bounded exchange for the original projective line

Actual affine chart models and the original strict-local/geometric transfer
prove invertibility of the defined higher exchange on every original
geometric stalk. The same argument applies to each base-changed P1 and
every bounded coefficient on that actual source.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard HasDerivedCategory.standard

private theorem killed_functor_obj {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (L : C ⥤ D) [L.Additive]
    (n : ℕ) (F : C) (hF : n • 𝟙 F = 0) : n • 𝟙 (L.obj F) = 0 := by
  simpa using congrArg L.map hF

/-- Every actual base change of native P1 satisfies bounded original exchange
for all coefficients on its original source and every further Cartesian square. -/
theorem boundedExchange_of_baseChangedProjectiveLine
    (n : ℕ) (hn : n ≠ 0) (R₀ : Type u) [CommRing R₀]
    {X S : Scheme.{u}} (f : X ⟶ S) (b : S ⟶ Spec (.of R₀))
    (a : X ⟶ ProjectiveLine.projectiveP1 R₀)
    (H₀ : IsPullback a f (ProjectiveLine.structureMap R₀) b)
    {X' S' : Scheme.{u}} (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (H : IsPullback g' f' f g) : boundedExchange n f f' g g' H.w.symm := by
  intro F hF q
  have : IsProper f := MorphismProperty.of_isPullback H₀
    (inferInstance : IsProper (ProjectiveLine.structureMap R₀))
  have : IsProper f' := MorphismProperty.of_isPullback H (inferInstance : IsProper f)
  apply StalkUniverse.isIso_of_all_original_fibrewiseClosed_geometricStalks (𝟙 S')
  intro Ω _ _ ζ _
  obtain ⟨i, φ, hη⟩ := Finite.exists_affineOpenCover_point_factorization (ζ ≫ g)
  obtain ⟨i', φ', hζ⟩ := Finite.exists_affineOpenCover_point_factorization ζ
  let R := S.affineOpenCover.X i
  let R' := S'.affineOpenCover.X i'
  let j : Spec (.of R) ⟶ S := S.affineOpenCover.f i
  let j' : Spec (.of R') ⟶ S' := S'.affineOpenCover.f i'
  let : Algebra R Ω := φ.toAlgebra
  let : Algebra R' Ω := φ'.toAlgebra
  have hη' : Spec.algebraMap R Ω ≫ j = ζ ≫ g := hη
  have hζ' : Spec.algebraMap R' Ω ≫ j' = ζ := hζ
  let E := projectiveLineAffineChartIso R₀ R f b a H₀ j
  let E' := projectiveLineAffineChartIso R₀ R' f' (g ≫ b) (g' ≫ a)
    (H.paste_horiz H₀) j'
  have hG : n • 𝟙 ((inverseImage g').obj F) = 0 :=
    killed_functor_obj (inverseImage g') n F hF
  have hκ := Stalk.chartGeometricPointMap_projectiveLine_transfer_bijective
    R Ω (ζ ≫ g) f j hη' E n hn F hF q
  have hκ' := Stalk.chartGeometricPointMap_projectiveLine_transfer_bijective
    R' Ω ζ f' j' hζ' E' n hn ((inverseImage g').obj F) hG q
  exact Stalk.higherBaseChangeMap_geometricStalk_isIso_of_localTransfers
    (f := f) (f' := f') (g := g) (g' := g') (h := H.w.symm) (ζ := ζ)
    (F := F) (q := q) (R := R) (R' := R') (j := j) (j' := j')
    (hη := hη') (hζ := hζ') H hκ hκ'

/-- Native P1 over every commutative ring has the original universal bounded
base-change property, including all coefficients on each pulled-back source. -/
theorem universallyBoundedBaseChange_projectiveLine
    (n : ℕ) (hn : n ≠ 0) (R : Type u) [CommRing R] :
    universallyBoundedBaseChange n (ProjectiveLine.structureMap R) := by
  intro X S a b f H₀ X' S' f' g g' H
  exact boundedExchange_of_baseChangedProjectiveLine n hn R f b a H₀.flip f' g g' H

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
