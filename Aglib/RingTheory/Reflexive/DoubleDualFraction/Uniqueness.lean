/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Reflexive.DoubleDualFraction
public import Mathlib.Algebra.Module.Torsion.Free

/-!
# Generic bidual maps are fixed by original evaluation

A finite-presentation generic comparison makes every bidual element a
denominator multiple of an original evaluation.
Consequently the actual generic bidual map is uniquely fixed by its values
on original raw elements. This is the uniqueness needed to glue the affine
generic embeddings through actual restriction maps.
-/

@[expose] public noncomputable section

namespace Module.Dual

variable {R K M V : Type*} [CommRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup M] [Module R M] [FinitePresentation R M]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  [IsReflexive K V]
  (f : M →ₗ[R] V) [IsLocalizedModule (nonZeroDivisors R) f]

include K f in
/-- Every original bidual element has a regular denominator multiple in the
image of the original evaluation. -/
theorem exists_nonZeroDivisor_smul_eq_eval (z : Dual R (Dual R M)) :
    ∃ (s : nonZeroDivisors R) (m : M), (s : R) • z = eval R M m := by
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors R) f
    (doubleDualToFraction (K := K) f z)
  refine ⟨s, m, ?_⟩
  apply doubleDualToFraction_injective (K := K) f
  simpa only [Submonoid.smul_def, map_smul, doubleDualToFraction_eval (K := K)] using hs

include K f in
/-- Original evaluation determines maps from the actual bidual into any
torsion-free target. The raw module need not be reflexive or torsion-free. -/
theorem doubleDual_linearMap_ext_on_eval_of_torsionFree
    {P : Type*} [AddCommGroup P] [Module R P] [Module.IsTorsionFree R P]
    (g h : Dual R (Dual R M) →ₗ[R] P)
    (heval : ∀ m : M, g (eval R M m) = h (eval R M m)) : g = h := by
  apply LinearMap.ext
  intro z
  obtain ⟨s, m, hz⟩ := exists_nonZeroDivisor_smul_eq_eval (K := K) f z
  apply (isRegular_iff_mem_nonZeroDivisors.mpr s.property).smul_right_injective P
  change (s : R) • g z = (s : R) • h z
  rw [← map_smul, ← map_smul, hz]
  exact heval m

include K f in
/-- Original evaluations determine a map from the actual bidual to the same
generic fibre, without assuming reflexivity of the raw source. -/
theorem doubleDual_linearMap_ext_on_eval
    (g h : Dual R (Dual R M) →ₗ[R] V)
    (heval : ∀ m : M, g (eval R M m) = h (eval R M m)) : g = h := by
  let : Module.IsTorsionFree R V := by
    constructor
    intro r hr
    exact ((Module.End.isUnit_iff _).mp
      (IsLocalizedModule.map_units f ⟨r, isRegular_iff_mem_nonZeroDivisors.mp hr⟩)).1
  exact doubleDual_linearMap_ext_on_eval_of_torsionFree (K := K) f g h heval

/-- Agreement on original raw forms fixes the actual generic bidual embedding. -/
theorem doubleDualToFraction_unique (g : Dual R (Dual R M) →ₗ[R] V)
    (hg : ∀ m : M, g (eval R M m) = f m) :
    g = doubleDualToFraction (K := K) f :=
  doubleDual_linearMap_ext_on_eval (K := K) f g (doubleDualToFraction (K := K) f)
    (fun m => (hg m).trans (doubleDualToFraction_eval (K := K) f m).symm)

end Module.Dual
