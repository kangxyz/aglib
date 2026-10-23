/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Descent.Square
public import Aglib.AlgebraicGeometry.Spec.LocalHenselizationTarget

/-!
# Transport from a selected local henselization

A line-bundle lift on the selected local henselization pulls back to the
original henselian target. The comparison retains the actual prime-fibre map
and its original residue-field marking.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Invertible

open LocalRing LocalRing.AtLocalTarget

universe u

/-- Lift the original selected-prime bundle on the original target, given
actual lifts on the selected local henselization's literal closed fibre. -/
theorem exists_lineBundle_of_selected_henselization
    {S B R : Type u} [CommRing S] [CommRing B] [CommRing R] [HenselianLocalRing R]
    (a : B →+* R) (b : S →+* B) {X : Scheme.{u}} (f : X ⟶ Spec (.of S))
    (hlift : ∀ C : LineBundle
        (Limits.pullback (Limits.pullback.snd f (henselizationSpecMap a b))
          (residueSpecMap (Henselization.AtLocalTarget.Ring a))),
      ∃ V : LineBundle (henselizationBaseChange a b f),
        Nonempty ((pullback (Limits.pullback.fst
          (Limits.pullback.snd f (henselizationSpecMap a b))
          (residueSpecMap (Henselization.AtLocalTarget.Ring a)))).obj V.val ≅ C.val))
    (C : LineBundle (primeFiber a b f)) :
    ∃ W : LineBundle (targetBaseChange a b f),
      Nonempty ((pullback (Limits.pullback.fst
        (Limits.pullback.snd f (targetSpecMap a b)) (residueSpecMap R))).obj W.val ≅
          (pullback (targetPrimeFiberMap a b f)).obj C.val) := by
  obtain ⟨W, ⟨e⟩⟩ := exists_lineBundle_pullback_of_square
    (targetBaseChangeMap a b f)
    (Limits.pullback.fst (Limits.pullback.snd f (targetSpecMap a b)) (residueSpecMap R))
    (Limits.pullback.fst (Limits.pullback.snd f (henselizationSpecMap a b))
      (residueSpecMap (Henselization.AtLocalTarget.Ring a)))
    (targetClosedFiberMap a b f) (targetClosedFiberMap_fst a b f).symm hlift
    (pullbackLineBundle (henselizationFiberIso a b f).hom C)
  refine ⟨W, ⟨e ≪≫ ?_⟩⟩
  exact (pullbackComp (targetClosedFiberMap a b f)
    (henselizationFiberIso a b f).hom).app C.val

end AlgebraicGeometry.Scheme.Modules.Invertible
