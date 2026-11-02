/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Projectivity.FiniteMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.SeparableExtension.FiniteConstants.FieldComparison

/-! # Original finite-constant field comparison for normal proper curves

The native finite pencil is constructed from normality, integrality,
properness and dimension one. Its actual structural equation identifies the
original field-pullback map with the existing finite-over-projective-line
comparison. Smooth proper geometrically connected curves are a specialization.
The original comparison's single standard Ext realization is retained in every
degree. No affine-curve comparison or boundary-extension statement is inferred.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge HasExt.standard

variable (k K : Type u) [Field k] [Field K] [IsSepClosed k] [Algebra k K]
  (X : FScheme k) (A : Type u) [AddCommGroup A] [Finite A]

/-- The original finite-constant restriction on a normal integral proper
curve is injective after any extension of its separably closed base field.
The target field need not be separably closed for this assertion. -/
theorem normalProperCurve_fieldExtension_constantRestriction_injective
    [IsIntegral X.left] [IsProper X.hom]
    (hN : Scheme.NormalStalks X.left) (hdim : topologicalKrullDim X.left = 1) (q : ℕ) :
    Function.Injective (constantRestriction.{u, u + 2, u + 2} A
      (pullback.fst X.hom (Spec.algebraMap k K)) q) := by
  obtain ⟨f, hf, _⟩ :=
    Projectivity.exists_finite_dominant_map_to_projectiveP1_of_normal X hN hdim
  let : IsFinite f.left := hf
  have h := finite_projectiveLine_fieldExtension_constantRestriction_injective k K f.left A q
  have he : f.left ≫ ProjectiveLine.structureMap k = X.hom := f.w
  exact (congrArg (fun p : X.left ⟶ Spec (.of k) =>
    Function.Injective (constantRestriction.{u, u + 2, u + 2} A
      (pullback.fst p (Spec.algebraMap k K)) q)) he).mp h

/-- The same actual restriction is bijective when the target field is also
separably closed. There is no coefficient-order or characteristic condition. -/
theorem normalProperCurve_fieldExtension_constantRestriction_bijective
    [IsSepClosed K] [IsIntegral X.left] [IsProper X.hom]
    (hN : Scheme.NormalStalks X.left) (hdim : topologicalKrullDim X.left = 1) (q : ℕ) :
    Function.Bijective (constantRestriction.{u, u + 2, u + 2} A
      (pullback.fst X.hom (Spec.algebraMap k K)) q) := by
  obtain ⟨f, hf, _⟩ :=
    Projectivity.exists_finite_dominant_map_to_projectiveP1_of_normal X hN hdim
  let : IsFinite f.left := hf
  have h := finite_projectiveLine_fieldExtension_constantRestriction_bijective k K f.left A q
  have he : f.left ≫ ProjectiveLine.structureMap k = X.hom := f.w
  exact (congrArg (fun p : X.left ⟶ Spec (.of k) =>
    Function.Bijective (constantRestriction.{u, u + 2, u + 2} A
      (pullback.fst p (Spec.algebraMap k K)) q)) he).mp h

/-- The existing smooth proper geometrically connected curve interface supplies
all the normality, integrality and dimension hypotheses of the original map. -/
theorem curveProperties_fieldExtension_constantRestriction_injective
    (hX : Properties X) (q : ℕ) :
    Function.Injective (constantRestriction.{u, u + 2, u + 2} A
      (pullback.fst X.hom (Spec.algebraMap k K)) q) := by
  let : IsIntegral X.left :=
    curveProperties_isIntegral Scheme.smoothFieldNormality Scheme.normalComponentsOpen hX
  let : IsProper X.hom := hX.proper
  exact normalProperCurve_fieldExtension_constantRestriction_injective k K X A
    (Scheme.smoothFieldNormality k X.left X.hom (curveProperties_smooth hX))
    (curveProperties_dimension Scheme.smoothFieldDimension hX) q

/-- Every original finite-constant cohomology group of a smooth proper
geometrically connected curve is invariant under extension of separably closed
fields, with the unchanged standard Ext realization and original restriction. -/
theorem curveProperties_fieldExtension_constantRestriction_bijective
    [IsSepClosed K] (hX : Properties X) (q : ℕ) :
    Function.Bijective (constantRestriction.{u, u + 2, u + 2} A
      (pullback.fst X.hom (Spec.algebraMap k K)) q) := by
  let : IsIntegral X.left :=
    curveProperties_isIntegral Scheme.smoothFieldNormality Scheme.normalComponentsOpen hX
  let : IsProper X.hom := hX.proper
  exact normalProperCurve_fieldExtension_constantRestriction_bijective k K X A
    (Scheme.smoothFieldNormality k X.left X.hom (curveProperties_smooth hX))
    (curveProperties_dimension Scheme.smoothFieldDimension hX) q

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
