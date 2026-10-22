/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.LiftAlongSquare
public import Aglib.AlgebraicGeometry.Spec.LocalHenselizationTarget

/-!
# Transporting a selected local-henselization lift to its original target

Given essential surjectivity for the literal closed-fibre restriction on
the selected henselization base change, every prescribed cover of the
original selected prime fibre lifts after base change to the target ring.
The conclusion retains its isomorphism with pullback along the actual
prime-fibre map. The essential-surjectivity premise is explicitly an
intermediate input, not a proper-henselian comparison theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

open LocalRing LocalRing.AtLocalTarget

universe u

variable {S B R : Type u} [CommRing S] [CommRing B] [CommRing R] [HenselianLocalRing R]
  (a : B →+* R) (b : S →+* B) {X : Scheme.{u}} (f : X ⟶ Spec (.of S))

/-- A prescribed prime-fibre cover lifts on the original target once it
lifts on the selected local henselization. Both base changes are directly
from the original coefficient model. -/
theorem exists_cover_of_selected_henselization
    [(baseChange (pullback.fst (pullback.snd f (henselizationSpecMap a b))
      (residueSpecMap (Henselization.AtLocalTarget.Ring a)))).EssSurj]
    (C : FiniteEtale (primeFiber a b f)) :
    ∃ W : FiniteEtale (targetBaseChange a b f),
      Nonempty ((baseChange (pullback.fst (pullback.snd f (targetSpecMap a b))
        (residueSpecMap R))).obj W ≅ (baseChange (targetPrimeFiberMap a b f)).obj C) := by
  obtain ⟨W, ⟨e⟩⟩ := exists_cover_pullback_of_square
    (targetBaseChangeMap a b f)
    (pullback.fst (pullback.snd f (targetSpecMap a b)) (residueSpecMap R))
    (pullback.fst (pullback.snd f (henselizationSpecMap a b))
      (residueSpecMap (Henselization.AtLocalTarget.Ring a)))
    (targetClosedFiberMap a b f) (targetClosedFiberMap_fst a b f).symm
    ((baseChange (henselizationFiberIso a b f).hom).obj C)
  refine ⟨W, ⟨e ≪≫ ?_⟩⟩
  exact (baseChangeComp (henselizationFiberIso a b f).hom
    (targetClosedFiberMap a b f)).symm.app C

end AlgebraicGeometry.Scheme.FiniteEtale
