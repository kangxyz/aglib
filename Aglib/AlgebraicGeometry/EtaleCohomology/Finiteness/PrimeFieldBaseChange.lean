/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.ArtinSchreier.Constants
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionColimit.ConstructibleTorsion

/-! # Original prime-field higher images under proper base change

The isomorphism is the original proper exchange followed by the canonical
constant-coefficient pullback isomorphism. No characteristic assumption on the
base is needed for this transport.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

/-- Proper base change with the same literal prime-field coefficient on the
actual pullback source. -/
def primeFieldHigherDirectImageBaseChangeIso
    {X S T : Scheme.{u}} (f : X ⟶ S) [IsProper f] (g : T ⟶ S)
    (p : ℕ) (hp : p.Prime) (q : ℕ) :
    (inverseImage g).obj ((higherDirectImage f q).obj (primeFieldSheaf X p)) ≅
      (higherDirectImage (pullback.snd f g) q).obj
        (primeFieldSheaf (pullback f g) p) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have : Finite (primeFieldCoefficient p) := by
    change Finite (ULift.{u + 1} (ZMod p))
    infer_instance
  have ht : IsTorsion X (primeFieldSheaf X p) :=
    Constructible.isTorsion_of_isConstructible _
      (Constructible.isConstructible_constant X (primeFieldCoefficient p))
  let e := higherBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
    (IsPullback.of_hasPullback f g).w.symm q
  let : IsIso (e.app (primeFieldSheaf X p)) :=
    Proper.properHigherBaseChange_isIso f (pullback.snd f g) g (pullback.fst f g)
      (IsPullback.of_hasPullback f g) _ ht q
  exact asIso (e.app (primeFieldSheaf X p)) ≪≫
    (higherDirectImage (pullback.snd f g) q).mapIso
      ((inverseImageConstantIso (pullback.fst f g)).app (primeFieldCoefficient p))

end AlgebraicGeometry.Scheme.EtaleCohomology
