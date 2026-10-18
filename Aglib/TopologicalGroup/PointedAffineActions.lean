/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.TopologicalGroup.SplitExtension
public import Aglib.GroupCohomology.H1.PrimitiveCharacters
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.Topology.Category.FinTopCat

/-!
# Pointed affine actions of an actual split topological extension

Source: `K2-018#eq:k2018-pointed-character` and
`K2-018#prop:k2018-arithmetic-characters`,
`research/exposes/K2/018/expose.tex` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.

This module proves the action-side algebra and topology behind pointed
monodromy. Its input action is an actual permutation homomorphism, with
continuous evaluation, the affine law for the coefficient action through `p`,
and zero fixed by the chosen section. Evaluation at zero on the actual kernel
then constructs a continuous equivariant character. Conversely, a character
constructs a permutation action through the derived split coordinates. These
constructions are inverse, and the actual kernel action is transitive exactly
when its derived character is surjective.

The coefficient object is an additive commutative group with a continuous
distributive `G`-action; no scalar ring or finiteness is needed for the general
calculation. The hypotheses for constructing the inverse are actual groups,
a topological-group structure on `E`, actual projection and section
homomorphisms, the splitting identity, and continuity of those maps. A topology
on `G` and continuity of its coefficient action are explicit. The kernel action
is the conjugation action proved in `SplitExtension`.

This proves neither the fundamental-group realization of `p` and `s` nor the
finite-etale classification and torsor transport required to turn this action
into a pointed scheme cover. Each declaration's source pointer uses the module
source basis above, and covers only this action-side subset.
-/

@[expose] public section

namespace TopologicalGroup.PointedAffineActions

open TopologicalGroup.SplitExtension
open GroupCohomology.PointedCohomology
open GroupCohomology.PrimitiveCharacters

variable {E G : Type*} [Group E] [Group G] [TopologicalSpace E]

/-- Actual pointed affine permutation actions for the action-side subset of
`K2-018#eq:k2018-pointed-character`, on the module source basis. The fields are
action axioms and continuity, rather than an input geometric character. -/
structure PointedAffineAction (p : E →* G) (s : G →* E) (R : Type*)
    [AddCommGroup R] [DistribMulAction G R] [TopologicalSpace R] where
  /-- The actual permutation representation in the module source subset. -/
  rho : E →* Equiv.Perm R
  /-- Jointly continuous evaluation in the module source subset. -/
  continuous_eval : Continuous (fun x : E × R => rho x.1 x.2)
  /-- Compatibility with coefficient translations in the module source subset. -/
  affine : ∀ e : E, ∀ a b : R, rho e (a + b) = rho e a + (p e) • b
  /-- The chosen zero lies over the marked section in the module source subset. -/
  section_zero : ∀ g : G, rho (s g) 0 = 0

variable {R : Type*} [AddCommGroup R] [DistribMulAction G R]
  [TopologicalSpace R]
variable {p : E →* G} {s : G →* E}

/-- The character target uses the constructed conjugation action for
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
abbrev KernelCharacter (p : E →* G) (s : G →* E) (R : Type*)
    [AddCommGroup R] [DistribMulAction G R] [TopologicalSpace R] :=
  letI := kernelAction p s
  EquivariantCharacter G p.ker R

namespace PointedAffineAction

/-- Extensionality for the actual pointed actions in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
@[ext] theorem ext (rho tau : PointedAffineAction p s R)
    (h : ∀ e a, rho.rho e a = tau.rho e a) : rho = tau := by
  cases rho with
  | mk rf rc ra rs =>
    cases tau with
    | mk tf tc ta ts =>
      have hfun : rf = tf := by
        apply MonoidHom.ext
        intro e
        apply Equiv.ext
        intro a
        exact h e a
      subst tf
      rfl

/-- Identity evaluation for the actual action in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
-- Keep this original specific simp shortcut alongside the lower generic normalization rules.
@[simp, nolint simpNF] theorem apply_one (rho : PointedAffineAction p s R) (a : R) :
    rho.rho 1 a = a := by
  rw [map_one]
  rfl

/-- Multiplication evaluation for the actual action in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem apply_mul (rho : PointedAffineAction p s R) (e d : E) (a : R) :
    rho.rho (e * d) a = rho.rho e (rho.rho d a) := by
  rw [map_mul]
  rfl

/-- The section acts by the coefficient action, derived from affinity and
pointedness in `K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem section_apply (rho : PointedAffineAction p s R)
    (hps : ∀ g, p (s g) = g) (g : G) (a : R) : rho.rho (s g) a = g • a := by
  simpa [rho.section_zero g, hps g] using rho.affine (s g) 0 a

/-- The actual kernel acts by translations, derived from affinity in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem kernel_apply (rho : PointedAffineAction p s R) (n : p.ker) (a : R) :
    rho.rho (n : E) a = rho.rho (n : E) 0 + a := by
  simpa using rho.affine (n : E) 0 a

/-- Kernel evaluation at zero constructs the continuous equivariant character
in `K2-018#eq:k2018-pointed-character`, on the module source basis. -/
def toCharacter (rho : PointedAffineAction p s R) (hps : ∀ g, p (s g) = g) :
    KernelCharacter p s R := by
  letI := kernelAction p s
  exact {
    toFun n := rho.rho (n : E) 0
    continuous_toFun := rho.continuous_eval.comp
      (continuous_subtype_val.prodMk continuous_const)
    map_mul := by
      intro n m
      change rho.rho ((n : E) * (m : E)) 0 = _
      rw [rho.apply_mul, rho.kernel_apply]
    map_action := by
      intro g n
      change rho.rho (s g * (n : E) * (s g)⁻¹) 0 = g • rho.rho (n : E) 0
      rw [rho.apply_mul, rho.apply_mul, ← map_inv s,
        rho.section_zero (g⁻¹), rho.section_apply hps] }

/-- Kernel-character evaluation formula for
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
@[simp] theorem toCharacter_apply (rho : PointedAffineAction p s R)
    (hps : ∀ g, p (s g) = g) (n : p.ker) :
    letI := kernelAction p s
    (rho.toCharacter hps).toFun n = rho.rho (n : E) 0 := by
  let := kernelAction p s
  rfl

/-- Every actual pointed affine action has the derived split-coordinate
formula in `K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem coordinate_formula (rho : PointedAffineAction p s R)
    (hps : ∀ g, p (s g) = g) (e : E) (a : R) :
    letI := kernelAction p s
    rho.rho e a = (rho.toCharacter hps).toFun (toCoordinates p s hps e).1 +
      (p e) • a := by
  let := kernelAction p s
  calc
    rho.rho e a = rho.rho (fromCoordinates p s (toCoordinates p s hps e)) a := by
      rw [fromCoordinates_toCoordinates]
    _ = rho.rho ((toCoordinates p s hps e).1 : E) (rho.rho (s (p e)) a) :=
      rho.apply_mul _ _ _
    _ = (rho.toCharacter hps).toFun (toCoordinates p s hps e).1 + (p e) • a := by
      rw [rho.section_apply hps, rho.kernel_apply]
      rfl

/-- The ordinary action underlying the actual permutation representation in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
@[instance_reducible] def action (rho : PointedAffineAction p s R) : MulAction E R where
  smul e a := rho.rho e a
  one_smul := rho.apply_one
  mul_smul := rho.apply_mul

/-- The underlying action is jointly continuous in the action-side subset of
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem continuousSMul (rho : PointedAffineAction p s R) :
    letI := rho.action
    ContinuousSMul E R := by
  let := rho.action
  exact ⟨rho.continuous_eval⟩

/-- The actual kernel action obtained by restricting the permutation
representation in `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
@[instance_reducible] def geometricAction (rho : PointedAffineAction p s R) :
    MulAction p.ker R where
  smul n a := rho.rho (n : E) a
  one_smul := rho.apply_one
  mul_smul n m a := rho.apply_mul n m a

/-- Continuity of the actual kernel action in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem geometricContinuousSMul (rho : PointedAffineAction p s R) :
    letI := rho.geometricAction
    ContinuousSMul p.ker R := by
  let := rho.geometricAction
  exact ⟨rho.continuous_eval.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)⟩

variable [TopologicalSpace G] [IsTopologicalAddGroup R]

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- The restricted action equals the previously constructed character
translation action in `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem geometricAction_eq_translation (rho : PointedAffineAction p s R)
    (hps : ∀ g, p (s g) = g) :
    letI := kernelAction p s
    rho.geometricAction = translationAction (forgetCharacter (rho.toCharacter hps)) := by
  let := kernelAction p s
  apply MulAction.ext
  exact funext fun n => funext fun a => rho.kernel_apply n a

/-- The actual kernel action is transitive exactly when its derived character
is surjective, the action-side primitive-cover criterion of
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem geometric_transitive_iff_surjective (rho : PointedAffineAction p s R)
    (hps : ∀ g, p (s g) = g) :
    letI := kernelAction p s
    (letI := rho.geometricAction; MulAction.IsPretransitive p.ker R) ↔
      Function.Surjective (rho.toCharacter hps).toFun := by
  let := kernelAction p s
  rw [rho.geometricAction_eq_translation hps]
  exact (translation_transitive_iff_surjective _).trans
    (forgetCharacter_surjective_iff _)

end PointedAffineAction

namespace PointedAffineAction

open CategoryTheory
open scoped FintypeCatDiscrete

variable [Finite R]

/-- The actual finite-set representation of a pointed affine action in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def finiteAction (rho : PointedAffineAction p s R) : Action FintypeCat E where
  V := FintypeCat.of R
  ρ := {
    toFun e := FintypeCat.homMk (rho.rho e)
    map_one' := by
      apply ConcreteCategory.hom_ext
      intro a
      exact rho.apply_one a
    map_mul' := by
      intro e d
      apply ConcreteCategory.hom_ext
      intro a
      exact rho.apply_mul e d a }

/-- The finite action has the original permutation evaluations in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
@[simp] theorem finiteAction_apply (rho : PointedAffineAction p s R) (e : E) (a : R) :
    ConcreteCategory.hom (rho.finiteAction.ρ e) a = rho.rho e a := rfl

variable [DiscreteTopology R]

/-- The genuine finite continuous action object supplied to a later
finite-etale classification in `K2-018#prop:k2018-arithmetic-characters`, on the
module source basis. Discreteness is assumed only for this categorical interface. -/
def finiteContAction (rho : PointedAffineAction p s R) : ContAction FintypeCat E := by
  refine ⟨rho.finiteAction, ?_⟩
  constructor
  let eval : E × R → R := fun x => rho.rho x.1 x.2
  have heval : Continuous eval := rho.continuous_eval
  have hR : (inferInstance : TopologicalSpace R) = ⊥ := DiscreteTopology.eq_bot
  change @Continuous (E × R) R (@instTopologicalSpaceProd E R _ ⊥) ⊥ eval
  exact hR ▸ heval

end PointedAffineAction

/-- Evaluation of the inverse action construction in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
def affineValue (p : E →* G) (s : G →* E) (hps : ∀ g, p (s g) = g)
    (f : KernelCharacter p s R) (e : E) (a : R) : R := by
  letI := kernelAction p s
  exact f.toFun (toCoordinates p s hps e).1 + (p e) • a

/-- Identity law for the derived action in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem affineValue_one (p : E →* G) (s : G →* E) (hps : ∀ g, p (s g) = g)
    (f : KernelCharacter p s R) (a : R) : affineValue p s hps f 1 a = a := by
  let := kernelAction p s
  have hc : toCoordinates p s hps 1 = (1, 1) := by
    simpa using toCoordinates_section p s hps 1
  have hf : f.toFun 1 = 0 := by
    apply add_left_cancel (a := f.toFun 1)
    simpa using (f.map_mul 1 1).symm
  simp [affineValue, hc, hf]

/-- Composition law for the derived action in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem affineValue_mul (p : E →* G) (s : G →* E) (hps : ∀ g, p (s g) = g)
    (f : KernelCharacter p s R) (e d : E) (a : R) :
    affineValue p s hps f (e * d) a =
      affineValue p s hps f e (affineValue p s hps f d a) := by
  let := kernelAction p s
  have hc := congrArg Prod.fst (toCoordinates_mul p s hps e d)
  change (toCoordinates p s hps (e * d)).1 =
    (toCoordinates p s hps e).1 * (p e) • (toCoordinates p s hps d).1 at hc
  simp [affineValue, hc, f.map_mul, f.map_action, map_mul, smul_add, mul_smul, add_assoc]

/-- Actual group action constructed from a continuous equivariant character
in `K2-018#eq:k2018-pointed-character`, on the module source basis. -/
@[instance_reducible] def characterAction (p : E →* G) (s : G →* E)
    (hps : ∀ g, p (s g) = g) (f : KernelCharacter p s R) : MulAction E R where
  smul := affineValue p s hps f
  one_smul := affineValue_one p s hps f
  mul_smul := affineValue_mul p s hps f

/-- Actual permutation homomorphism constructed from the character action
in `K2-018#eq:k2018-pointed-character`, on the module source basis. -/
def characterPermHom (p : E →* G) (s : G →* E) (hps : ∀ g, p (s g) = g)
    (f : KernelCharacter p s R) : E →* Equiv.Perm R := by
  letI := characterAction p s hps f
  exact MulAction.toPermHom E R

variable [TopologicalSpace G] [IsTopologicalGroup E] [IsTopologicalAddGroup R]
  [ContinuousSMul G R]

/-- A character constructs an actual continuous pointed affine action in
`K2-018#eq:k2018-pointed-character`, on the module source basis. The maps and
their continuity are explicit inputs, not scheme realization assumptions. -/
def fromCharacter (p : E →* G) (s : G →* E) (hps : ∀ g, p (s g) = g)
    (hp : Continuous p) (hs : Continuous s) (f : KernelCharacter p s R) :
    PointedAffineAction p s R where
  rho := characterPermHom p s hps f
  continuous_eval := by
    let := kernelAction p s
    change Continuous (fun x : E × R =>
      f.toFun (toCoordinates p s hps x.1).1 + (p x.1) • x.2)
    exact (f.continuous_toFun.comp
      (continuous_fst.comp ((continuous_toCoordinates p s hps hp hs).comp continuous_fst))).add
      ((hp.comp continuous_fst).smul continuous_snd)
  affine := by
    intro e a b
    change affineValue p s hps f e (a + b) =
      affineValue p s hps f e a + (p e) • b
    simp [affineValue, smul_add, add_assoc]
  section_zero := by
    let := kernelAction p s
    intro g
    change affineValue p s hps f (s g) 0 = 0
    simp [affineValue, toCoordinates_section, f.map_one]

/-- Explicit constructed-action formula for
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
@[simp] theorem fromCharacter_apply (p : E →* G) (s : G →* E)
    (hps : ∀ g, p (s g) = g) (hp : Continuous p) (hs : Continuous s)
    (f : KernelCharacter p s R) (e : E) (a : R) :
    letI := kernelAction p s
    (fromCharacter p s hps hp hs f).rho e a =
      f.toFun (toCoordinates p s hps e).1 + (p e) • a := by
  let := kernelAction p s
  rfl

/-- Restriction after action construction recovers the character in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
@[simp] theorem toCharacter_fromCharacter (p : E →* G) (s : G →* E)
    (hps : ∀ g, p (s g) = g) (hp : Continuous p) (hs : Continuous s)
    (f : KernelCharacter p s R) :
    (fromCharacter p s hps hp hs f).toCharacter hps = f := by
  let := kernelAction p s
  apply EquivariantCharacter.ext
  intro n
  simp [PointedAffineAction.toCharacter_apply, fromCharacter_apply, toCoordinates_kernel]

/-- Action construction after restriction recovers the entire permutation
representation in `K2-018#eq:k2018-pointed-character`, on the module source basis. -/
@[simp] theorem fromCharacter_toCharacter (p : E →* G) (s : G →* E)
    (hps : ∀ g, p (s g) = g) (hp : Continuous p) (hs : Continuous s)
    (rho : PointedAffineAction p s R) :
    fromCharacter p s hps hp hs (rho.toCharacter hps) = rho := by
  apply PointedAffineAction.ext
  intro e a
  exact (rho.coordinate_formula hps e a).symm

/-- The proved continuous pointed-action/character equivalence behind
`K2-018#eq:k2018-pointed-character`, on the module source basis. Both directions
construct their target from the supplied action or character. Finite-etale
classification and torsor transport remain outside this equivalence. -/
def pointedAffineCharacterEquiv (p : E →* G) (s : G →* E)
    (hps : ∀ g, p (s g) = g) (hp : Continuous p) (hs : Continuous s) :
    PointedAffineAction p s R ≃ KernelCharacter p s R where
  toFun rho := rho.toCharacter hps
  invFun := fromCharacter p s hps hp hs
  left_inv := fromCharacter_toCharacter p s hps hp hs
  right_inv := toCharacter_fromCharacter p s hps hp hs

/-- The existing direct pointed continuous H¹ model constructs actual pointed
affine actions through the proved character equivalences in
`K2-018#eq:k2018-pointed-character`, on the module source basis. This is still
continuous group cohomology, with the scheme and étale comparisons outstanding. -/
def pointedH1AffineActionEquiv (p : E →* G) (s : G →* E)
    (hps : ∀ g, p (s g) = g) (hp : Continuous p) (hs : Continuous s) :
    letI := kernelAction p s
    PointedH1 (G := G) (N := p.ker) (A := R) ≃ PointedAffineAction p s R := by
  letI := kernelAction p s
  exact (pointedH1AddEquiv (G := G) (N := p.ker) (A := R)).toEquiv.trans
    (pointedAffineCharacterEquiv p s hps hp hs).symm

/-- The actual action associated to a direct pointed continuous H¹ class has
the class's geometric character in `K2-018#eq:k2018-pointed-character`, on the
module source basis. -/
theorem pointedH1AffineAction_character (p : E →* G) (s : G →* E)
    (hps : ∀ g, p (s g) = g) (hp : Continuous p) (hs : Continuous s) :
    letI := kernelAction p s
    ∀ q : PointedH1 (G := G) (N := p.ker) (A := R),
      (pointedH1AffineActionEquiv p s hps hp hs q).toCharacter hps =
        pointedH1AddEquiv q := by
  let := kernelAction p s
  intro q
  exact (pointedAffineCharacterEquiv p s hps hp hs).apply_symm_apply
    (pointedH1AddEquiv q)

end TopologicalGroup.PointedAffineActions

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 f771d3c7d9b6bc473e8d5b93987d985e729be04b7f80f37f5a3e750ffac0da12.
Definitions, hypotheses and universes are retained modulo native names. -/
