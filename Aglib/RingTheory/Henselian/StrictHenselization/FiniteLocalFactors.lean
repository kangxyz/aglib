/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.FiniteAlgebraHenselian
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Strictly local factors of finite algebras

A finite local algebra over a strictly Henselian local ring has separably closed
residue field. In particular, the native localization of a finite algebra at a
specified maximal ideal is finite and strictly local. No equality of the residue
fields is asserted: the extension can be nontrivially purely inseparable.

These are the selected-component producers for finite étale-cohomology stalk
calculations. The finite product decomposition of the whole algebra is separate.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace HenselianLocalRing

/-- The residue field of a finite local algebra over a strictly local ring is
separably closed. Independent base and algebra universes are retained. -/
theorem residueField_isSepClosed_of_finite_local_algebra
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (ResidueField R)]
    (B : Type v) [CommRing B] [IsLocalRing B] [Algebra R B] [Module.Finite R B] :
    IsSepClosed (ResidueField B) := by
  let : IsLocalHom (algebraMap R B) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap R B)).out 5 1).mp
    have h : ((maximalIdeal B).under R).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (maximalIdeal B)
    exact IsLocalRing.eq_maximalIdeal h
  exact Algebra.IsAlgebraic.isSepClosed (F := ResidueField R)

/-- The actual residue extension of a finite local algebra over a separably
closed residue field is purely inseparable, not necessarily trivial. -/
theorem residueField_isPurelyInseparable_of_finite_local_algebra
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (ResidueField R)]
    (B : Type v) [CommRing B] [IsLocalRing B] [Algebra R B] [Module.Finite R B]
    [IsLocalHom (algebraMap R B)] :
    IsPurelyInseparable (ResidueField R) (ResidueField B) := inferInstance

/-- The native selected maximal localization is Henselian. -/
theorem henselian_localizationAtPrime
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A]
    (q : Ideal A) [q.IsMaximal] : HenselianLocalRing (Localization.AtPrime q) := by
  let := finite_localizationAtPrime R A q
  exact of_finite_local_algebra R (Localization.AtPrime q)

/-- The native selected maximal localization of a finite algebra over a strictly
local base has separably closed residue field. -/
theorem residueField_isSepClosed_localizationAtPrime
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (ResidueField R)]
    (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A]
    (q : Ideal A) [q.IsMaximal] :
    IsSepClosed (ResidueField (Localization.AtPrime q)) := by
  let := finite_localizationAtPrime R A q
  exact residueField_isSepClosed_of_finite_local_algebra R (Localization.AtPrime q)

end HenselianLocalRing
