/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Reflexive.Hom
public import Aglib.RingTheory.Reflexive.DualPi

/-! The endomorphisms of an actual finite bidual and its finite-product evaluation. -/

@[expose] public section

noncomputable section

example {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.IsReflexive R (Module.End R (Module.Dual R (Module.Dual R M))) := by
  let := Module.IsReflexive.dual_of_finite (R := R) (M := Module.Dual R M)
  exact Module.IsReflexive.linearMap

example {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Finite ι]
    (x : ι → M) :
    Module.Dual.piDoubleDualEquiv R M ι (Module.Dual.eval R (ι → M) x) =
      fun i ↦ Module.Dual.eval R M (x i) :=
  Module.Dual.piDoubleDualEquiv_eval R M ι x
