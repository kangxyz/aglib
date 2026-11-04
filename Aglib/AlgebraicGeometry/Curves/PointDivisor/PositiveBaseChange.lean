/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.PointDivisor.Basic
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.LineBundleBaseChange
public import Aglib.AlgebraicGeometry.RationalPoint.BaseChange

/-! The positive bundle of the actual rational section under scalar extension. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor

variable {k : Type u} [Field k] {X : FScheme k}

/-- The original positive point class pulls back to the class of the actual
lifted rational section, with the same original Cartier ideals. -/
theorem pullbackClass_positiveLineBundle_fieldBaseChange (hX : Properties X)
    (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
    (K : Type u) [Field K] [Algebra k K] :
    let b := Spec.algebraMap k K
    let XK : FScheme K := Over.mk (pullback.snd X.hom b)
    let r := (rationalPoint X o ho).baseChange b
    let hXK := curveProperties_baseChange hX K b
    pullbackClass (pullback.fst X.hom b) (classOf X.left (positiveLineBundle X hX o ho)) =
      classOf XK.left (positiveLineBundle XK hXK r.sectionMap r.section_comp) := by
  let b := Spec.algebraMap k K
  let XK : FScheme K := Over.mk (pullback.snd X.hom b)
  let r := rationalPoint X o ho
  let rK := r.baseChange b
  let hXK := curveProperties_baseChange hX K b
  let i := idealLineBundle X hX o ho
  let j := idealLineBundle XK hXK rK.sectionMap rK.section_comp
  have hb : Flat (pullback.fst X.hom b) := MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback X.hom b).flip (inferInstanceAs (Flat (Spec.algebraMap k K)))
  let hi : Scheme.Hom.IsEffectiveCartier o := ⟨r.section_isClosedImmersion, i.property⟩
  let hj : Scheme.Hom.IsEffectiveCartier rK.sectionMap :=
    ⟨rK.section_isClosedImmersion, j.property⟩
  exact @Scheme.Hom.pullbackClass_positiveCartier_of_isPullback_of_flat _ _ _ _
    o rK.sectionMap b (pullback.fst X.hom b) (r.baseChange_isPullback b) hb hi hj

end AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor
