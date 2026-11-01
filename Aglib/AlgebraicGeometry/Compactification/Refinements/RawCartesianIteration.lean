/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.CartesianBaseChange

/-! # Original Cartesian squares for successive raw base change -/

@[expose] public section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u
variable {X S T U : Scheme.{u}} {f : X ⟶ S}
  (C : Hom.Compactification f) (b : T ⟶ S) (c : U ⟶ T)

/-- The two actual raw open squares paste to the original composite square. -/
theorem isPullback_rawIterationOpen :
    IsPullback ((pullback.snd c (pullback.fst b f)) ≫ (pullback.snd b f)) (((C.baseChange
      b).baseChange c)).j C.j ((pullback.snd c (C.baseChange b).p) ≫ (pullback.snd b C.p)) :=
  (isPullback_rawCompactificationOpen (C.baseChange b) c).paste_horiz
    (isPullback_rawCompactificationOpen C b)

/-- The two actual raw proper squares paste to the original composite square. -/
theorem isPullback_rawIterationProper :
    IsPullback ((pullback.snd c (C.baseChange b).p) ≫ (pullback.snd b C.p)) (((C.baseChange
      b).baseChange c)).p C.p (c ≫ b) :=
  (IsPullback.of_hasPullback c ((C.baseChange b)).p).flip.paste_horiz
    (IsPullback.of_hasPullback b C.p).flip

end AlgebraicGeometry.Scheme.EtaleCohomology
