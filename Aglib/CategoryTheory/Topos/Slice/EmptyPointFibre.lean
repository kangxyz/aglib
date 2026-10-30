/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Adjunction
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! # Empty point fibres and actual slice extension by zero

An empty fibre over the slice object makes the original restricted skyscraper
zero. The two actual adjunctions then identify every endomorphism of the original
extension fibre, so its identity is zero. No neighborhood or enough-points
assumption enters this argument.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

universe u v p a b d e

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : Point.{p} J) {A : Type a} [Category.{b} A]
  [HasProducts.{p} A] [HasZeroMorphisms A]

/-- The original skyscraper restricts to zero over an empty point fibre. -/
theorem isZero_overPullback_skyscraper (U : C) (hU : IsEmpty (Φ.fiber.obj U)) (M : A) :
    IsZero ((J.overPullback A U).obj (Φ.skyscraperSheaf M)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply Pi.hom_ext
  intro q
  exact (hU.false (Φ.fiber.map V.unop.hom q)).elim

variable [HasColimitsOfSize.{p, p} A]

/-- The actual lower-shriek and point adjunctions force the original fibre to be zero. -/
theorem isZero_sheafFiber_of_skyscraper_restriction
    {D : Type d} [Category.{e} D]
    (L : D ⥤ Sheaf J A) (R : Sheaf J A ⥤ D) (adj : L ⊣ R)
    (hR : ∀ M : A, IsZero (R.obj (Φ.skyscraperSheaf M))) (F : D) :
    IsZero (Φ.sheafFiber.obj (L.obj F)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  let M := Φ.sheafFiber.obj (L.obj F)
  let e := (Φ.skyscraperSheafAdjunction.homEquiv _ M).trans (adj.homEquiv F _)
  exact e.injective ((hR M).eq_of_tgt _ _)

/-- In particular the actual hom-indexed coproduct slice lower shriek has zero fibre. -/
theorem isZero_sheafFiber_lowerShriek [HasCoproducts.{v} A] [HasWeakSheafify J A]
    (U : C) (hU : IsEmpty (Φ.fiber.obj U)) (F : Sheaf (J.over U) A) :
    IsZero (Φ.sheafFiber.obj ((Sheaf.SliceCohomology.lowerShriek J A U).obj F)) :=
  Φ.isZero_sheafFiber_of_skyscraper_restriction
    (Sheaf.SliceCohomology.lowerShriek J A U) (J.overPullback A U)
    (Sheaf.SliceCohomology.lowerShriekAdjunction J A U)
    (fun M => Φ.isZero_overPullback_skyscraper U hU M) F

end CategoryTheory.GrothendieckTopology.Point
