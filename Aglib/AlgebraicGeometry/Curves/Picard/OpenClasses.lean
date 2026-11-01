/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.DivisorOpenRestriction
public import Aglib.AlgebraicGeometry.Curves.Picard.DivisorInverse
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback

/-! # Original Picard classes under open restriction

The constructed original module pullback isomorphism identifies pullback of
actual divisor line bundles with restriction of the original divisor. Every
line bundle on the open subscheme is represented by an actual divisor;
extension by zero constructs a preimage for the original Picard pullback.
No replacement Picard quotient or cohomological localization premise is used.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass

variable {U X : Scheme.{u}} [IsIntegral U] [IsIntegral X]
  [IsNoetherian U] [IsNoetherian X] [JacobsonSpace X]
  [∀ x : ClosedPoint U, IsDiscreteValuationRing (U.presheaf.stalk x.val)]
  [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
  (j : U ⟶ X) [IsOpenImmersion j]
  (hdim : topologicalKrullDim X ≤ 1)

omit [IsIntegral U] [IsIntegral X] [IsNoetherian U] [IsNoetherian X] [JacobsonSpace X]
  [∀ x : ClosedPoint U, IsDiscreteValuationRing (U.presheaf.stalk x.val)]
  [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)] in
include j hdim in
/-- The open source inherits the dimension bound from the original open embedding. -/
theorem openSource_dimension_le_one : topologicalKrullDim U ≤ 1 :=
  j.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le.trans hdim

/-- Original Picard pullback of a divisor line bundle is the class of the
original restricted divisor, by the constructed original module isomorphism. -/
theorem pullbackClass_divisor (D : Divisor X) :
    pullbackClass j (classOf X (divisorLineBundle X hdim D)) =
      classOf U (divisorLineBundle U (openSource_dimension_le_one j hdim)
        (openRestriction j D)) := by
  exact Quotient.sound ⟨divisorSheafOpenPullbackIso j D⟩

include hdim in
/-- Every actual Picard class on the open subscheme extends: represent its
line bundle by a divisor and extend that divisor by zero. -/
theorem pullbackClass_openImmersion_surjective : Function.Surjective (pullbackClass j) := by
  intro a
  induction a using Quotient.inductionOn with
  | h L =>
    obtain ⟨D, ⟨e⟩⟩ := DivisorInverse.exists_divisor_iso U L.val L.property
      (openSource_dimension_le_one j hdim)
    refine ⟨classOf X (divisorLineBundle X hdim (openExtension j D)), ?_⟩
    rw [pullbackClass_divisor, openRestriction_openExtension]
    exact Quotient.sound ⟨e.symm⟩

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass
