/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov

/-! # Upper bounds from the finite original homology layers

A triangulated functor sends a cohomologically bounded object into an upper
truncation range if it sends each of its finitely many original homology
singles into that range. A degree-zero bound `N` on those coefficients gives
upper bound `N + b` when the input has upper bound `b`.

This is a finite homological reduction. It supplies neither geometric
cohomological-dimension bounds nor an unbounded or all-coefficient amplitude
assertion. In particular, coefficient conditions must be proved on the actual
homology objects, not on arbitrary terms of a chosen resolution.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ZeroObject

namespace DerivedCategory.Plus

universe u v w u' v'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (F : Plus C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
  (t : CategoryTheory.Triangulated.TStructure D)

/-- An upper bound on the images of the finite original homology layers is an
upper bound on the image of the original bounded object. -/
theorem isLE_obj_of_homology_bounds (K : Plus C) (a b N : ℤ)
    [K.IsGE a] [K.IsLE b]
    (hs : ∀ i : ℤ, a ≤ i → i ≤ b →
      t.IsLE (F.obj ((singleFunctor C i).obj ((homologyFunctor C i).obj K))) N) :
    t.IsLE (F.obj K) N := by
  let P : ObjectProperty (Plus C) := fun L => t.IsLE (F.obj L) N
  let : P.IsClosedUnderIsomorphisms := {
    of_iso := by
      intro L M e hL
      let : t.IsLE (F.obj L) N := hL
      exact t.isLE_of_iso (F.mapIso e) N }
  let : P.ContainsZero := {
    exists_zero := ⟨0, isZero_zero _,
      t.isLE_of_isZero (F.map_isZero (isZero_zero _)) N⟩ }
  let : P.IsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk'
    (P := P) (fun T hT h₁ h₃ =>
      t.isLE₂ (F.mapTriangle.obj T) (F.map_distinguished T hT) N h₁ h₃)
  exact property_of_homology_bounds P K a b hs

omit [F.IsTriangulated] in
/-- The actual single-functor and functor-shift isomorphisms transport a bound
on a degree-zero single to the corresponding bound in any degree. -/
theorem isLE_obj_single_of_zero (M : C) (i N : ℤ)
    [t.IsLE (F.obj ((singleFunctor C 0).obj M)) N] :
    t.IsLE (F.obj ((singleFunctor C i).obj M)) (N + i) := by
  let K := (singleFunctor C 0).obj M
  let : t.IsLE ((F.obj K)⟦-i⟧) (N + i) :=
    t.isLE_shift (F.obj K) N (-i) (N + i) (by omega)
  let e : (F.obj K)⟦-i⟧ ≅ F.obj ((singleFunctor C i).obj M) :=
    ((F.commShiftIso (-i)).app K).symm ≪≫
      F.mapIso (((singleFunctors C).shiftIso (-i) i 0 (by omega)).app M)
  exact t.isLE_of_iso e (N + i)

/-- A uniform degree-zero bound on the finitely many actual homology
coefficients adds to the input's upper amplitude. The lower bound is used
only to make the Postnikov reduction finite, and empty ranges are allowed. -/
theorem isLE_obj_of_homology_single_zero_bounds (K : Plus C) (a b N : ℤ)
    [K.IsGE a] [K.IsLE b]
    (hs : ∀ i : ℤ, a ≤ i → i ≤ b →
      t.IsLE (F.obj ((singleFunctor C 0).obj ((homologyFunctor C i).obj K))) N) :
    t.IsLE (F.obj K) (N + b) := by
  apply isLE_obj_of_homology_bounds F t K a b (N + b)
  intro i hai hib
  let : t.IsLE (F.obj ((singleFunctor C 0).obj ((homologyFunctor C i).obj K))) N :=
    hs i hai hib
  let : t.IsLE (F.obj ((singleFunctor C i).obj ((homologyFunctor C i).obj K))) (N + i) :=
    isLE_obj_single_of_zero F t ((homologyFunctor C i).obj K) i N
  exact t.isLE_of_le _ (N + i) (N + b) (by omega)

end DerivedCategory.Plus
