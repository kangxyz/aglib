/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedMonomorphism
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverFiber
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Original cyclic coefficient monomorphisms detected at a generator

The actual constant coefficient is represented by the literal trivial cover.
Its geometric point group has prime cardinality. A generator section with
nonzero geometric image therefore makes the original coefficient map monic.
No chosen additive coordinate on the geometric fibre is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
open Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge

/-- A nonzero geometric value of the actual constant-unit generator detects
monicity of a map from the original prime-cyclic coefficient. -/
theorem cyclic_mono_of_generator_value_ne_zero
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ X)
    [GaloisCategory (Scheme.FiniteEtale X)]
    [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
    (H : Grp (Over X)) [IsCommMonObj H.X] [IsFinite H.X.hom] [Etale H.X.hom]
    {p : ℕ} [Fact p.Prime]
    (q : ConstantFinite.coefficient (ULift.{u} (ZMod p)) X ⟶ representedSheaf H)
    (hq : (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 X)) ≫
      (q.hom.app (op (etaleTerminal X))
        (((constantAdjunction X).unit.app (ConstantFinite.value (ULift.{u} (ZMod p))))
          (ULift.up (ULift.up (1 : ZMod p))))).down.toMul ≠ 1) : Mono q := by
  let A := ULift.{u} (ZMod p)
  let R := ConstantFinite.representation A X
  let g : R.group ⟶ H := representedSheafGroupPreimage (R.iso.hom ≫ q)
  have hg : representedSheafMap g = R.iso.hom ≫ q := representedSheafMap_preimage _
  let T := op (etaleTerminal X)
  let z : (ConstantFinite.coefficient A X).obj.obj T :=
    ((constantAdjunction X).unit.app (ConstantFinite.value A))
      (ULift.up (ULift.up (1 : ZMod p)))
  let z' : ULift.{u+1} (Additive (Over.mk (𝟙 X) ⟶ R.group.X)) :=
    R.iso.inv.hom.app T z
  let w : ULift.{u+1} (Additive (Over.mk (𝟙 X) ⟶ H.X)) := q.hom.app T z
  let i : Over.mk s ⟶ Over.mk (𝟙 X) := Over.homMk s (by simp)
  let f : (Over.mk s ⟶ R.group.X) →* (Over.mk s ⟶ H.X) := {
    toFun a := a ≫ g.hom.hom
    map_one' := MonObj.one_comp _
    map_mul' a b := MonObj.mul_comp a b _ }
  have hsection : (representedSheafMap g).hom.app T z' = q.hom.app T z := by
    rw [hg]
    change q.hom.app T (R.iso.hom.hom.app T (R.iso.inv.hom.app T z)) = _
    have hz := congrArg (fun t => t.hom.app T z) R.iso.inv_hom_id
    exact congrArg (q.hom.app T) hz
  have hn : f (i ≫ z'.down.toMul) ≠ 1 := by
    change (i ≫ z'.down.toMul) ≫ g.hom.hom ≠ 1
    rw [Category.assoc]
    have hs := congrArg (fun t => t.down.toMul) hsection
    change z'.down.toMul ≫ g.hom.hom = w.down.toMul at hs
    rw [hs]
    exact hq
  have hcard : Nat.card (Over.mk s ⟶ R.group.X) = p := by
    change Nat.card (Fiber s (trivialCover X A)) = p
    rw [← Nat.card_congr (trivialCoverFiberEquiv A s)]
    simp [A, Nat.card_eq_fintype_card]
  let : IsSimpleGroup (Over.mk s ⟶ R.group.X) :=
    CommGroup.is_simple_iff_prime_card.mpr (hcard.symm ▸ Fact.out)
  have hf : Function.Injective f := by
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
    · exact f.ker_eq_bot_iff.mp h
    · have he : f = 1 := MonoidHom.ker_eq_top_iff.mp h
      exact False.elim (hn (by rw [he]; rfl))
  have : Mono (representedSheafMap g) :=
    representedSheafMap_mono_of_fiber_injective s g hf
  have hqeq : q = R.iso.inv ≫ representedSheafMap g := by
    rw [hg, R.iso.inv_hom_id_assoc]
  rw [hqeq]
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology
