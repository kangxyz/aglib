/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily

/-!
# The positive ordered divisor family without a base point

Use the same existing ordered parameter scheme and its original coordinate
graphs. The finite tensor product of their existing positive Cartier bundles
is the family O(sum graph(s_i)); no origin section is chosen. Its class and
arbitrary test-base pullback formulas precede specialization to the Picard
representative. When an origin is supplied, the original based family is
this positive family tensored with n copies of the original origin ideal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {S X : Scheme.{u}} (p : X ⟶ S)
  [SmoothOfRelativeDimension 1 p] [IsSeparated p]

/-- The positive graph-divisor family on the same original ordered product.
It has no chosen origin or rational point. -/
def positiveFamilyLineBundle (n : ℕ) : LineBundle (pullback p (parameter p n).hom) :=
  finiteTensorLineBundle _ (fun i : Fin n =>
    Hom.positiveGraphLineBundle Hom.smoothRelativeDivisorIdeal p (parameter p n).hom
      (coordinate p n i) (coordinate_over p n i))

/-- The original class of the positive family is the sum of the original
positive graph classes. -/
theorem positiveFamilyLineBundle_class (n : ℕ) :
    classOf _ (positiveFamilyLineBundle p n) = ∑ i : Fin n,
      classOf _ (Hom.positiveGraphLineBundle Hom.smoothRelativeDivisorIdeal p
        (parameter p n).hom (coordinate p n i) (coordinate_over p n i)) :=
  classOf_finiteTensor _ _

/-- The positive family is relatively flat over its original parameter
scheme, since it is invertible and the projection is flat. -/
theorem positiveFamilyLineBundle_relativeFlat (n : ℕ) :
    Modules.relativeFlat (pullback.snd p (parameter p n).hom)
      (positiveFamilyLineBundle p n).val := by
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  exact relativeFlat_of_flat (pullback.snd p (parameter p n).hom)
    (positiveFamilyLineBundle p n)

-- Compare the actual finite-tensor pullback with the original graph class maps.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The positive family specializes along every tuple of sections over
every test scheme, including nonreduced tests. -/
theorem positiveFamilyLineBundle_class_at_tuple {T : Scheme.{u}} (t : T ⟶ S) {n : ℕ}
    (s : Fin n → (T ⟶ X)) (hs : ∀ i, s i ≫ p = t) :
    pullbackClass (Hom.familyMap p (parameter p n).hom t (parameterPoint p t s hs)
      (parameterPoint_over p t s hs)) (classOf _ (positiveFamilyLineBundle p n)) =
      ∑ i : Fin n, classOf _
        (Hom.positiveGraphLineBundle Hom.smoothRelativeDivisorIdeal p t (s i) (hs i)) := by
  rw [positiveFamilyLineBundle_class]
  change (PullbackTensor.Local.pullbackHom _) (∑ i : Fin n, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := positiveGraphClass_baseChange Hom.smoothRelativeDivisorIdeal
    Hom.relativeCartierIdealBaseChange moduleTensorPullback p
    (parameter p n).hom t (coordinate p n i) (coordinate_over p n i)
    (parameterPoint p t s hs) (parameterPoint_over p t s hs)
  simpa only [parameterPoint_coordinate, PullbackTensor.Local.pullbackHom_apply] using h

/-- The original based family differs from the positive family by the
specified origin ideal, as a whole family class. -/
theorem lineBundle_class_eq_positive_add_origin (o : S ⟶ X) (ho : o ≫ p = 𝟙 _)
    (n : ℕ) :
    classOf _ (lineBundle p o ho n) = classOf _ (positiveFamilyLineBundle p n) +
      n • classOf _ (Hom.originIdealLineBundle Hom.smoothRelativeDivisorIdeal p o ho
        (parameter p n).hom) := by
  rw [lineBundle_class, positiveFamilyLineBundle_class]
  simp only [Hom.abelClass, Hom.abelLineBundle, classOf_tensor, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- Positive-degree class before any origin normalization. -/
theorem positiveFamilyLineBundle_class_eq_based_sub_origin
    (o : S ⟶ X) (ho : o ≫ p = 𝟙 _) (n : ℕ) :
    classOf _ (positiveFamilyLineBundle p n) = classOf _ (lineBundle p o ho n) -
      n • classOf _ (Hom.originIdealLineBundle Hom.smoothRelativeDivisorIdeal p o ho
        (parameter p n).hom) :=
  (eq_sub_iff_add_eq).mpr (lineBundle_class_eq_positive_add_origin p o ho n).symm

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
