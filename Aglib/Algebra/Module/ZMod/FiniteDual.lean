/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.Algebra.Module.ZMod

/-!
# Cardinality and native biduality for finite ZMod modules

For every positive modulus and every finite module, the original linear dual
has the same cardinality and separates points. Consequently the original
`Module.Dual.eval` is bijective and supplies `Module.IsReflexive` and
`Module.evalEquiv`, with their original evaluation and naturality maps.

The finite counting and separation proof uses Mathlib's finite-abelian duality
(`GroupTheory/FiniteAbelian/Duality.lean`) only through additive/multiplicative
type tags of the same underlying module and `ZMod n` groups. The cyclic target
has a generator of order `n`, and the source exponent divides `n`. Every
additive map is the same ZMod-linear map. This local proof boundary introduces
no public character carrier and changes neither the dual nor its scalar action.
All composite moduli and modulus one are retained.
-/

@[expose] public noncomputable section

namespace ZMod

variable (n : ℕ) [NeZero n]

omit [NeZero n] in
private theorem enoughRoots : HasEnoughRootsOfUnity (Multiplicative (ZMod n)) n where
  prim := ⟨Multiplicative.ofAdd 1, IsPrimitiveRoot.iff_orderOf.mpr (ZMod.addOrderOf_one n)⟩
  cyc := isCyclic_of_injective
    ((Units.coeHom _).comp (rootsOfUnity n (Multiplicative (ZMod n))).subtype)
    (Units.val_injective.comp Subtype.val_injective)

variable (M : Type*) [AddCommGroup M] [Module (ZMod n) M]

/-- The native dual of a finite positive-modulus ZMod module is finite. -/
instance finiteDual [Finite M] : Finite (Module.Dual (ZMod n) M) :=
  Finite.of_injective (fun f : Module.Dual (ZMod n) M => (f : M → ZMod n))
    DFunLike.coe_injective

omit [NeZero n] in
private theorem exponent_dvd_modulus : Monoid.exponent (Multiplicative M) ∣ n := by
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  change n • x.toAdd = 0
  rw [← Nat.cast_smul_eq_nsmul (ZMod n), CharP.cast_eq_zero, zero_smul]

private theorem enoughRootsExponent :
    HasEnoughRootsOfUnity (Multiplicative (ZMod n)) (Monoid.exponent (Multiplicative M)) := by
  let := enoughRoots n
  exact HasEnoughRootsOfUnity.of_dvd _ (exponent_dvd_modulus n M)

/-- A finite positive-modulus ZMod module and its original dual have equal cardinality. -/
theorem natCard_dual [Finite M] : Nat.card (Module.Dual (ZMod n) M) = Nat.card M := by
  let := enoughRootsExponent n M
  let e : Module.Dual (ZMod n) M ≃
      (Multiplicative M →* (Multiplicative (ZMod n))ˣ) :=
    (AddMonoidHom.toZModLinearMapEquiv n).symm.toEquiv.trans
      (AddMonoidHom.toMultiplicative.trans MonoidHom.toHomUnitsMulEquiv.toEquiv)
  exact (Nat.card_congr e).trans
    (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Multiplicative M)
      (Multiplicative (ZMod n)))

/-- The original ZMod-linear dual separates points of every finite module. -/
theorem exists_dual_apply_ne_zero [Finite M] {x : M} (hx : x ≠ 0) :
    ∃ f : Module.Dual (ZMod n) M, f x ≠ 0 := by
  let := enoughRootsExponent n M
  obtain ⟨f, hf⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    (Multiplicative M) (Multiplicative (ZMod n)) (a := Multiplicative.ofAdd x) hx
  let g : M →+ ZMod n := AddMonoidHom.toMultiplicative.symm ((Units.coeHom _).comp f)
  refine ⟨g.toZModLinearMap n, fun h => hf ?_⟩
  apply Units.val_injective
  exact congrArg Multiplicative.ofAdd h

/-- The original evaluation into the double dual is injective for a finite ZMod module. -/
theorem dual_eval_injective [Finite M] : Function.Injective (Module.Dual.eval (ZMod n) M) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  by_contra h
  obtain ⟨f, hf⟩ := exists_dual_apply_ne_zero n M h
  exact hf (DFunLike.congr_fun hx f)

/-- The original evaluation into the double dual is bijective for a finite ZMod module. -/
theorem dual_eval_bijective [Finite M] : Function.Bijective (Module.Dual.eval (ZMod n) M) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  exact ⟨dual_eval_injective n M,
    ((natCard_dual n (Module.Dual (ZMod n) M)).trans (natCard_dual n M)).symm⟩

/-- Finite modules over a positive ZMod ring are reflexive through native evaluation. -/
theorem isReflexive_of_finite [Finite M] : Module.IsReflexive (ZMod n) M :=
  ⟨dual_eval_bijective n M⟩

end ZMod
