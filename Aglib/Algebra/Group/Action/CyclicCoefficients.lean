/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Data.ZMod.CoefficientMaps
public import Aglib.GroupTheory.Cyclic.Characters
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.Algebra.MulAction

/-!
# Actions from unit characters on cyclic additive coefficients

The unit-valued characters are supplied. Continuity transfers only under
the displayed compatibility and continuity hypotheses.

Source: `R5Lab.Aglib.Algebra.Group.Action.CyclicCoefficients`.
Packet SHA-256:
`d3894c9f7698f5c300a715d4f493d28a16cc9b86f47bf4b90aea38c62387cfc4`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

open _root_.AddMonoidHom.CyclicCharacters


namespace ZMod
variable {n : ℕ} {G : Type*} [Group G]

/-- One-twist action on the additive root-of-unity coordinate model `ZMod n`,
the auxiliary dual-coefficient calculation for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis.
Identifying this model with actual `mu_n` requires a separately supplied marking. -/
@[instance_reducible]
def unitCharacterAction (chi : G →* (ZMod n)ˣ) : DistribMulAction G (ZMod n) where
  smul g a := (chi g : ZMod n) * a
  one_smul a := by
    change (chi (1 : G) : ZMod n) * a = a
    simp
  mul_smul g h a := by
    change (chi (g * h) : ZMod n) * a = (chi g : ZMod n) * ((chi h : ZMod n) * a)
    simp [mul_assoc]
  smul_zero g := mul_zero _
  smul_add g a b := mul_add _ a b

/-- Inverse cyclotomic action on the concrete cyclic coordinate group,
the target action of the auxiliary dual-character calculation for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis.
This definition does not identify any geometric dual kernel. -/
@[instance_reducible]
def inverseUnitCharacterAction (chi : G →* (ZMod n)ˣ) :
    DistribMulAction G (ZMod n) where
  smul g a := (chi g⁻¹ : ZMod n) * a
  one_smul a := by
    change (chi (1 : G)⁻¹ : ZMod n) * a = a
    simp
  mul_smul g h a := by
    change (chi (g * h)⁻¹ : ZMod n) * a =
      (chi g⁻¹ : ZMod n) * ((chi h⁻¹ : ZMod n) * a)
    simp [mul_inv_rev, mul_left_comm, mul_comm]
  smul_zero g := mul_zero _
  smul_add g a b := mul_add _ a b

/-- Evaluation at `1` marks the cyclic-coordinate Hom group by `ZMod n`,
the auxiliary dual-coefficient algebra for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis.
It is a coefficient-group equivalence, with no geometric pairing input. -/
def addHomEvalOneEquiv : (ZMod n →+ ZMod n) ≃+ ZMod n where
  toFun f := f 1
  invFun a :=
    { toFun := fun b => a * b
      map_zero' := mul_zero a
      map_add' := mul_add a }
  left_inv f := AddMonoidHom.ext fun a => (addHom_apply_eq_mul f a).symm
  right_inv a := mul_one a
  map_add' _ _ := rfl

end ZMod

namespace ZMod
variable {d m : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
open ZMod

/-- Compatible reduction derives continuity of the level-d supplied cyclotomic-character values from
continuity at level m.
Source: the coefficient convention of
`K2-018#eq:k2018-coefficient-compatibility`, lines 292–306,
at the documented source snapshot. -/
theorem reduced_character_continuous (hd : d ∣ m)
    (chiD : G →* (ZMod d)ˣ) (chiM : G →* (ZMod m)ˣ)
    (hchi : ∀ g, (ZMod.castHom hd (ZMod d)) (chiM g : ZMod m) = (chiD g : ZMod d))
    (hchiM : Continuous (fun g : G => (chiM g : ZMod m))) :
    Continuous (fun g : G => (chiD g : ZMod d)) := by
  have hred : Continuous ((ZMod.castHom hd (ZMod d)) : ZMod m → ZMod d) :=
    continuous_of_discreteTopology
  have hcomp := hred.comp hchiM
  simpa only [Function.comp_def, hchi] using hcomp

end ZMod
