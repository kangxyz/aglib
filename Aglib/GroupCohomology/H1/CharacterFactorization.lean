/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.GroupCohomology.H1.SplitCoefficients
public import Aglib.GroupTheory.Cyclic.CharacterFactorization
public import Mathlib.Topology.Instances.ZMod

/-!
# Factoring pointed characters through their actual cyclic image

For arbitrary topological groups G and N with the stated action, a continuous equivariant
character into ZMod m factors uniquely through ZMod d when d is its actual additive order. The
level m is nonzero, d divides m, and the literal divisor insertion must be equivariant. N can
be infinite and noncommutative. The construction preserves the kernel, proves surjectivity of
the factor, and extends through the existing pointed-H1 equivalence. The zero character has
order one. Continuous coefficient actions are used only in the pointed-cohomology section.

Extraction source: `R5Lab.Aglib.GroupCohomology.H1.CharacterFactorization`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`c7ee112c42c14905a91e4a5fff8f6eaee99b95991981beb98aec53632133256d`.
The source conditions, actual objects and canonical maps are retained under native names.
-/

@[expose] public section

open _root_.AddMonoidHom.CyclicCharacters ZMod

namespace GroupCohomology.PointedCohomology.CharacterFactorization

open _root_.GroupCohomology.PointedCohomology _root_.GroupCohomology.CoefficientFunctoriality

variable {d m : ℕ} [NeZero m]
variable {G N : Type*} [Group G] [Group N] [MulDistribMulAction G N]
  [TopologicalSpace G] [TopologicalSpace N]
  [DistribMulAction G (ZMod m)] [DistribMulAction G (ZMod d)]

variable (hd : d ∣ m)
  (he : ∀ g : G, ∀ a : ZMod d, divisorInsertion hd (g • a) = g • divisorInsertion hd a)

/-- The constructed insertion preimage is a continuous equivariant geometric character.
Continuity follows by composing with a total inverse on discrete coefficients.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
noncomputable def liftCharacter (f : EquivariantCharacter G N (ZMod m))
    (ho : addOrderOf (characterToAddHom f) = d) : EquivariantCharacter G N (ZMod d) where
  toFun u := liftAddHom (characterToAddHom f) hd ho (Additive.ofMul u)
  continuous_toFun := by
    let i := divisorInsertion hd
    have hi : Function.Injective i := divisorInsertion_injective hd
    have hfun : (fun u : N => liftAddHom (characterToAddHom f) hd ho (Additive.ofMul u)) =
        (Function.invFun i) ∘ f.toFun := by
      funext u
      change liftAddHom (characterToAddHom f) hd ho (Additive.ofMul u) =
        Function.invFun i (characterToAddHom f (Additive.ofMul u))
      rw [← divisorInsertion_liftAddHom (characterToAddHom f) hd ho (Additive.ofMul u)]
      exact ((Function.leftInverse_invFun hi) _).symm
    rw [hfun]
    exact continuous_of_discreteTopology.comp f.continuous_toFun
  map_mul u v := by
    exact (liftAddHom (characterToAddHom f) hd ho).map_add (Additive.ofMul u) (Additive.ofMul v)
  map_action g u := by
    apply divisorInsertion_injective hd
    rw [divisorInsertion_liftAddHom, he, divisorInsertion_liftAddHom]
    exact f.map_action g u

set_option linter.unusedSectionVars false in
-- Preserve this original interface's topology hypothesis and binder order.
/-- Insertion of the constructed continuous character recovers the original character pointwise.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
@[simp, nolint unusedArguments]
theorem divisorInsertion_liftCharacter (f : EquivariantCharacter G N (ZMod m))
    (ho : addOrderOf (characterToAddHom f) = d) (u : N) :
    divisorInsertion hd ((liftCharacter hd he f ho).toFun u) = f.toFun u :=
  divisorInsertion_liftAddHom (characterToAddHom f) hd ho (Additive.ofMul u)

set_option linter.unusedSectionVars false in
-- Preserve this original interface's topology hypothesis and binder order.
/-- The constructed continuous actual-image character is primitive, expressed as surjectivity.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
@[nolint unusedArguments]
theorem liftCharacter_surjective (f : EquivariantCharacter G N (ZMod m))
    (ho : addOrderOf (characterToAddHom f) = d) :
    Function.Surjective (liftCharacter hd he f ho).toFun := by
  intro a
  obtain ⟨u, hu⟩ := liftAddHom_surjective (characterToAddHom f) hd ho a
  exact ⟨u.toMul, hu⟩

/-- The actual coefficient character map sends the constructed lift back to the original character.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
theorem characterMap_liftCharacter (f : EquivariantCharacter G N (ZMod m))
    (ho : addOrderOf (characterToAddHom f) = d) :
    characterMap (divisorInsertion hd) continuous_of_discreteTopology he (liftCharacter hd he f
      ho) = f := by
  apply _root_.GroupCohomology.PointedCohomology.EquivariantCharacter.ext
  intro u
  exact divisorInsertion_liftCharacter hd he f ho u


set_option linter.unusedSectionVars false in
-- Preserve this original interface's topology hypothesis and binder order.
/-- The lifted continuous character has the previously constructed underlying additive homomorphism.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
@[nolint unusedArguments]
theorem characterToAddHom_liftCharacter (f : EquivariantCharacter G N (ZMod m))
    (ho : addOrderOf (characterToAddHom f) = d) :
    characterToAddHom (liftCharacter hd he f ho) = liftAddHom (characterToAddHom f) hd ho := by
  ext u
  rfl

/-- The lifted continuous character and original character have identical geometric kernels.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
theorem liftCharacter_ker (f : EquivariantCharacter G N (ZMod m))
    (ho : addOrderOf (characterToAddHom f) = d) :
    (characterToAddHom (liftCharacter hd he f ho)).ker = (characterToAddHom f).ker := by
  rw [characterToAddHom_liftCharacter]
  exact liftAddHom_ker (characterToAddHom f) hd ho

variable [ContinuousSMul G (ZMod m)] [ContinuousSMul G (ZMod d)]

omit [NeZero m] in
/-- The actual order of a pointed continuous H¹ class is the order of its underlying geometric
additive character.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
theorem pointed_character_order (q : PointedH1 (G := G) (N := N) (A := ZMod m)) :
    addOrderOf (characterToAddHom (pointedH1AddEquiv q)) = addOrderOf q :=
  (addOrderOf_injective characterToAddHom characterToAddHom_injective (pointedH1AddEquiv q)).trans
    ((pointedH1AddEquiv (G := G) (N := N) (A := ZMod m)).addOrderOf_eq q)

/-- Every pointed class at a positive finite coefficient level has positive finite actual
order, including order one for zero.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
theorem pointed_order_pos (q : PointedH1 (G := G) (N := N) (A := ZMod m)) :
    0 < addOrderOf q := by
  rw [← pointed_character_order, character_order_eq_image_card]
  exact Nat.card_pos

/-- The actual order of a pointed class divides its finite coefficient level; no
order-divisibility input is assumed.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
theorem pointed_order_dvd_level (q : PointedH1 (G := G) (N := N) (A := ZMod m)) :
    addOrderOf q ∣ m := by
  rw [← pointed_character_order, character_order_eq_image_card]
  simpa only [Nat.card_zmod] using
    (characterToAddHom (pointedH1AddEquiv q)).range.card_addSubgroup_dvd_card

/-- Construct the pointed class at its actual order from the continuous insertion-preimage
character and the proved pointed-character equivalence.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
noncomputable def factorPointed (q : PointedH1 (G := G) (N := N) (A := ZMod m))
    (ho : addOrderOf q = d) : PointedH1 (G := G) (N := N) (A := ZMod d) :=
  (pointedH1AddEquiv (G := G) (N := N) (A := ZMod d)).symm
    (liftCharacter hd he (pointedH1AddEquiv q) ((pointed_character_order q).trans ho))

/-- The constructed pointed level-d class inserts to the original pointed class at level m.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
theorem divisorInsertion_factorPointed (q : PointedH1 (G := G) (N := N) (A := ZMod m))
    (ho : addOrderOf q = d) :
    pointedH1Map (divisorInsertion hd) continuous_of_discreteTopology he (factorPointed hd he q
      ho) = q := by
  apply (pointedH1AddEquiv (G := G) (N := N) (A := ZMod m)).injective
  rw [pointedH1Map_geometric]
  change characterMap (divisorInsertion hd) continuous_of_discreteTopology he
    (pointedH1AddEquiv ((pointedH1AddEquiv (G := G) (N := N) (A := ZMod d)).symm _)) = _
  rw [AddEquiv.apply_symm_apply]
  exact characterMap_liftCharacter hd he (pointedH1AddEquiv q) ((pointed_character_order
    q).trans ho)

/-- The constructed class equality holds in actual continuous H¹, not only in its pointed subtype.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
theorem h1_divisorInsertion_factorPointed
    (q : PointedH1 (G := G) (N := N) (A := ZMod m)) (ho : addOrderOf q = d) :
    h1Map (divisorInsertion hd) continuous_of_discreteTopology he (factorPointed hd he q ho).1
      = q.1 :=
  congrArg Subtype.val (divisorInsertion_factorPointed hd he q ho)

/-- The pointed factorization is unique by geometric-character insertion injectivity, without
global H¹ injectivity.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
theorem factorPointed_unique (q : PointedH1 (G := G) (N := N) (A := ZMod m))
    (ho : addOrderOf q = d) (k : PointedH1 (G := G) (N := N) (A := ZMod d))
    (hk : pointedH1Map (divisorInsertion hd) continuous_of_discreteTopology he k = q) :
    k = factorPointed hd he q ho := by
  apply pointedH1Map_injective (divisorInsertion hd) continuous_of_discreteTopology he
    (divisorInsertion_injective hd)
  rw [hk, divisorInsertion_factorPointed]

/-- There exists exactly one pointed class at the actual order whose insertion is the original
class.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
theorem existsUnique_factorPointed (q : PointedH1 (G := G) (N := N) (A := ZMod m))
    (ho : addOrderOf q = d) :
    ∃! k : PointedH1 (G := G) (N := N) (A := ZMod d),
      pointedH1Map (divisorInsertion hd) continuous_of_discreteTopology he k = q := by
  exact ⟨factorPointed hd he q ho, divisorInsertion_factorPointed hd he q ho,
    fun k hk => factorPointed_unique hd he q ho k hk⟩

/-- The constructed level-d class has exact additive order d.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
theorem factorPointed_exact_order (q : PointedH1 (G := G) (N := N) (A := ZMod m))
    (ho : addOrderOf q = d) : addOrderOf (factorPointed hd he q ho) = d := by
  calc
    addOrderOf (factorPointed hd he q ho) =
        addOrderOf (pointedH1Map (divisorInsertion hd) continuous_of_discreteTopology he
          (factorPointed hd he q ho)) :=
      (addOrderOf_injective (pointedH1Map (divisorInsertion hd) continuous_of_discreteTopology he)
        (pointedH1Map_injective (divisorInsertion hd) continuous_of_discreteTopology he
          (divisorInsertion_injective hd))
        (factorPointed hd he q ho)).symm
    _ = addOrderOf q := by rw [divisorInsertion_factorPointed]
    _ = d := ho

/-- The constructed pointed class has a surjective, hence primitive, geometric coefficient
character.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
theorem factorPointed_surjective (q : PointedH1 (G := G) (N := N) (A := ZMod m))
    (ho : addOrderOf q = d) :
    Function.Surjective (pointedH1AddEquiv (factorPointed hd he q ho)).toFun := by
  change Function.Surjective
    (pointedH1AddEquiv ((pointedH1AddEquiv (G := G) (N := N) (A := ZMod d)).symm _)).toFun
  rw [AddEquiv.apply_symm_apply]
  exact liftCharacter_surjective hd he (pointedH1AddEquiv q) ((pointed_character_order q).trans ho)

/-- The constructed pointed class preserves the original geometric kernel, the group-theoretic
statement underlying its same actual cover.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
theorem factorPointed_ker (q : PointedH1 (G := G) (N := N) (A := ZMod m))
    (ho : addOrderOf q = d) :
    (characterToAddHom (pointedH1AddEquiv (factorPointed hd he q ho))).ker =
      (characterToAddHom (pointedH1AddEquiv q)).ker := by
  change (characterToAddHom
    (pointedH1AddEquiv ((pointedH1AddEquiv (G := G) (N := N) (A := ZMod d)).symm _))).ker = _
  rw [AddEquiv.apply_symm_apply]
  exact liftCharacter_ker hd he (pointedH1AddEquiv q) ((pointed_character_order q).trans ho)

/-- The constructed class is zero exactly when the original class is zero; the order-one case
is preserved.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
theorem factorPointed_eq_zero_iff (q : PointedH1 (G := G) (N := N) (A := ZMod m))
    (ho : addOrderOf q = d) : factorPointed hd he q ho = 0 ↔ q = 0 := by
  have hi := pointedH1Map_injective (N := N) (divisorInsertion hd)
    continuous_of_discreteTopology he (divisorInsertion_injective hd)
  rw [← hi.eq_iff, divisorInsertion_factorPointed, map_zero]
/-- Construct the level indexed by the original pointed class’s own additive order, using the
proved order-divisibility theorem.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
noncomputable def factorActualPointed
    (q : PointedH1 (G := G) (N := N) (A := ZMod m))
    [DistribMulAction G (ZMod (addOrderOf q))]
    [ContinuousSMul G (ZMod (addOrderOf q))]
    (heActual : ∀ g : G, ∀ a : ZMod (addOrderOf q),
      divisorInsertion (pointed_order_dvd_level q) (g • a) =
        g • divisorInsertion (pointed_order_dvd_level q) a) :
    PointedH1 (G := G) (N := N) (A := ZMod (addOrderOf q)) :=
  factorPointed (pointed_order_dvd_level q) heActual q rfl

/-- The unique actual-image pointed factorization can be indexed directly by the class’s order;
d is not an independent order input.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
theorem existsUnique_actual_order_factorization
    (q : PointedH1 (G := G) (N := N) (A := ZMod m))
    [DistribMulAction G (ZMod (addOrderOf q))]
    [ContinuousSMul G (ZMod (addOrderOf q))]
    (heActual : ∀ g : G, ∀ a : ZMod (addOrderOf q),
      divisorInsertion (pointed_order_dvd_level q) (g • a) =
        g • divisorInsertion (pointed_order_dvd_level q) a) :
    ∃! k : PointedH1 (G := G) (N := N) (A := ZMod (addOrderOf q)),
      pointedH1Map (divisorInsertion (pointed_order_dvd_level q))
        continuous_of_discreteTopology heActual k = q :=
  existsUnique_factorPointed (pointed_order_dvd_level q) heActual q rfl

end GroupCohomology.PointedCohomology.CharacterFactorization
