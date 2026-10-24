/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Pulling back a quotient subobject

A monomorphism into the cokernel of a monomorphism gives a genuine extension
of the original source inside its target. The resulting quotient is
canonically isomorphic to the prescribed quotient subobject.
-/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory

open Limits

namespace ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {A M R : C} (a : A ⟶ M) [Mono a] (j : R ⟶ cokernel a) [Mono j]

/-- The original subobject maps into the inverse image of the quotient subobject. -/
def quotientPullbackInclusion : A ⟶ pullback (cokernel.π a) j :=
  pullback.lift a 0 (by simp)

omit [Mono a] [Mono j] in
@[reassoc (attr := simp)]
lemma quotientPullbackInclusion_fst :
    quotientPullbackInclusion a j ≫ pullback.fst _ _ = a :=
  pullback.lift_fst _ _ _

omit [Mono a] [Mono j] in
@[reassoc (attr := simp)]
lemma quotientPullbackInclusion_snd :
    quotientPullbackInclusion a j ≫ pullback.snd _ _ = 0 :=
  pullback.lift_snd _ _ _

instance : Mono (quotientPullbackInclusion a j) :=
  mono_of_mono_fac (quotientPullbackInclusion_fst a j)

/-- The original subobject is the kernel of the projection to the quotient subobject. -/
def quotientPullbackInclusionIsKernel :
    IsLimit (KernelFork.ofι (quotientPullbackInclusion a j)
      (quotientPullbackInclusion_snd a j)) := by
  apply KernelFork.IsLimit.ofι'
  intro Z k hk
  have hz : (k ≫ pullback.fst (cokernel.π a) j) ≫ cokernel.π a = 0 := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hk, zero_comp]
  refine ⟨Abelian.monoLift a (k ≫ pullback.fst _ _) hz, ?_⟩
  apply pullback.hom_ext
  · simp only [Category.assoc, quotientPullbackInclusion_fst, Abelian.monoLift_comp]
  · simp only [Category.assoc, quotientPullbackInclusion_snd, comp_zero, hk]

/-- The actual short exact sequence of the inverse-image construction. -/
def quotientPullbackSequence : ShortComplex C :=
  ShortComplex.mk (quotientPullbackInclusion a j) (pullback.snd _ _)
    (quotientPullbackInclusion_snd a j)

omit [Mono j] in
lemma quotientPullbackSequence_shortExact : (quotientPullbackSequence a j).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (quotientPullbackInclusionIsKernel a j)
  mono_f := inferInstanceAs (Mono (quotientPullbackInclusion a j))
  epi_g := inferInstanceAs (Epi (pullback.snd (cokernel.π a) j))

/-- The quotient of the enlarged subobject by the old one is the original
quotient subobject, through the native cokernel comparison isomorphism. -/
def quotientPullbackCokernelIso : cokernel (quotientPullbackInclusion a j) ≅ R :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
    (Abelian.epiIsCokernelOfKernel _ (quotientPullbackInclusionIsKernel a j))

end ShortComplex

end CategoryTheory
