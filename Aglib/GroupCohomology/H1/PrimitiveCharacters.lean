/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Aglib.GroupCohomology.H1.SplitExtension
public import Aglib.GroupTheory.Cyclic.Characters
public import Mathlib.GroupTheory.OrderOfElement

/-!
This module retains generic pointed, primitive and translation character algebra.
The original source context below describes the full pre-split family;
its stated hypotheses and uninstantiated comparison boundaries remain in force.
-/

@[expose] public section

/-!
# Primitive pointed characters and translation monodromy

Source: `K2-018#eq:k2018-pointed-character` (lines 341–355) and
`K2-018#prop:k2018-arithmetic-characters` (lines 392–432),
`research/exposes/K2/018/expose.tex`, at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.

Forgetting continuity and equivariance embeds continuous geometric characters
additively into actual additive homomorphisms from `Additive N`. It therefore
preserves their additive order. Together with the additive pointed H¹ theorem
and the finite cyclic character theorem, this proves that exact order `n` is
equivalent to surjective geometric monodromy into `ZMod n`.

Surjectivity is equivalent to transitivity of the translation action on the
coefficient group. This is the geometric monodromy algebra for the primitive
cover step. Comparison with étale H¹, arithmetic fundamental groups, torsors,
geometric connectedness via Galois categories, and elliptic isogenies remains
outside this file. No finite quotient or finiteness assumption on `N` is used.
Coefficient topology and continuity of its `G`-action are supplied explicitly.
Each declaration's source pointer uses the module source basis above.
-/

namespace GroupCohomology.PrimitiveCharacters

open GroupCohomology.PointedCohomology

section CharacterBridge

variable {G N A : Type*} [Group G] [Group N] [AddCommGroup A]
  [MulDistribMulAction G N] [DistribMulAction G A]
  [TopologicalSpace G] [TopologicalSpace N] [TopologicalSpace A]
  [IsTopologicalAddGroup A]

/-- Auxiliary additive forgetful bridge from the continuous character side of
`K2-018#eq:k2018-pointed-character`, on the module source basis.
The target is an actual additive homomorphism, with no continuity requirement. -/
def forgetCharacter : EquivariantCharacter G N A →+ (Additive N →+ A) where
  toFun f := {
    toFun u := f.toFun u.toMul
    map_zero' := f.map_one
    map_add' u v := f.map_mul u.toMul v.toMul }
  map_zero' := by apply AddMonoidHom.ext; intro u; rfl
  map_add' f k := by apply AddMonoidHom.ext; intro u; rfl

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypothesis and binder order.
/-- Auxiliary evaluation formula for the forgetful bridge in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[simp, nolint unusedArguments]
theorem forgetCharacter_apply (f : EquivariantCharacter G N A) (u : N) :
    forgetCharacter f (Additive.ofMul u) = f.toFun u := rfl

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypothesis and binder order.
/-- Forgetting continuity and equivariance is injective for the character
side of `K2-018#eq:k2018-pointed-character`, on the module source basis. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem forgetCharacter_injective :
    Function.Injective (forgetCharacter (G := G) (N := N) (A := A)) := by
  intro f k h
  apply EquivariantCharacter.ext
  intro u
  exact DFunLike.congr_fun h (Additive.ofMul u)

/-- The forgetful bridge preserves exact additive order in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem forgetCharacter_addOrderOf (f : EquivariantCharacter G N A) :
    addOrderOf (forgetCharacter f) = addOrderOf f :=
  addOrderOf_injective forgetCharacter forgetCharacter_injective f

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypothesis and binder order.
/-- Auxiliary comparison of the two domain presentations in the character
side of `K2-018#eq:k2018-pointed-character`, on the module source basis. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem forgetCharacter_surjective_iff (f : EquivariantCharacter G N A) :
    Function.Surjective (forgetCharacter f) ↔ Function.Surjective f.toFun := by
  constructor
  · intro h a
    obtain ⟨u, hu⟩ := h a
    exact ⟨u.toMul, hu⟩
  · intro h a
    obtain ⟨u, hu⟩ := h a
    exact ⟨Additive.ofMul u, hu⟩

variable [ContinuousSMul G A]

/-- The pointed continuous H¹ class mapped to its actual geometric additive
homomorphism in `K2-018#eq:k2018-pointed-character`, on the module source basis. -/
def pointedGeometricHom : PointedH1 (G := G) (N := N) (A := A) →+ (Additive N →+ A) :=
  forgetCharacter.comp (pointedH1AddEquiv (G := G) (N := N) (A := A)).toAddMonoidHom

/-- Auxiliary evaluation formula for the pointed geometric homomorphism in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
@[simp] theorem pointedGeometricHom_apply
    (q : PointedH1 (G := G) (N := N) (A := A)) (u : N) :
    pointedGeometricHom q (Additive.ofMul u) =
      (pointedH1AddEquiv (G := G) (N := N) (A := A) q).toFun u := rfl

/-- The actual geometric homomorphism determines a pointed continuous H¹
class in `K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem pointedGeometricHom_injective :
    Function.Injective (pointedGeometricHom (G := G) (N := N) (A := A)) :=
  forgetCharacter_injective.comp
    (pointedH1AddEquiv (G := G) (N := N) (A := A)).injective

/-- Exact additive order survives the complete pointed-H¹-to-character
bridge in `K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem pointedGeometricHom_addOrderOf
    (q : PointedH1 (G := G) (N := N) (A := A)) :
    addOrderOf (pointedGeometricHom q) = addOrderOf q :=
  (forgetCharacter_addOrderOf
    (pointedH1AddEquiv (G := G) (N := N) (A := A) q)).trans
    ((pointedH1AddEquiv (G := G) (N := N) (A := A)).addOrderOf_eq q)

end CharacterBridge

section TranslationAction

variable {N A : Type*} [Group N] [AddCommGroup A]

/-- Translation monodromy associated to an actual geometric character in the
primitive-cover step of `K2-018#prop:k2018-arithmetic-characters`, on the module
source basis. This constructs an action, not a scheme or torsor comparison. -/
@[instance_reducible]
def translationAction (f : Additive N →+ A) : MulAction N A where
  smul u a := f (Additive.ofMul u) + a
  one_smul a := by
    change f (0 : Additive N) + a = a
    simp
  mul_smul u v a := by
    change f (Additive.ofMul u + Additive.ofMul v) + a =
      f (Additive.ofMul u) + (f (Additive.ofMul v) + a)
    rw [f.map_add, add_assoc]

/-- Auxiliary formula for geometric translation monodromy in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
@[simp] theorem translationAction_apply (f : Additive N →+ A) (u : N) (a : A) :
    letI := translationAction f
    u • a = f (Additive.ofMul u) + a := rfl

/-- Geometric translation monodromy is transitive exactly when the character
is surjective, the primitive-cover deduction in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis.
Actual geometric connectedness requires the separate Galois-category bridge. -/
theorem translation_transitive_iff_surjective (f : Additive N →+ A) :
    letI := translationAction f
    MulAction.IsPretransitive N A ↔ Function.Surjective f := by
  let _ := translationAction f
  constructor
  · intro h a
    obtain ⟨u, hu⟩ := h.exists_smul_eq (0 : A) a
    refine ⟨Additive.ofMul u, ?_⟩
    simpa [translationAction] using hu
  · intro h
    constructor
    intro a b
    obtain ⟨u, hu⟩ := h (b - a)
    refine ⟨u.toMul, ?_⟩
    change f u + a = b
    rw [hu]
    abel

end TranslationAction

section FiniteLevel

variable {G N : Type*} [Group G] [Group N] [MulDistribMulAction G N]
  [TopologicalSpace G] [TopologicalSpace N]
variable {n : ℕ} [NeZero n]
  [DistribMulAction G (ZMod n)] [TopologicalSpace (ZMod n)]
  [IsTopologicalAddGroup (ZMod n)]

/-- A continuous equivariant character is primitive at level `n` exactly when
its actual geometric map is surjective, the primitive-cover step of
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis.
This combines an injective additive forgetful map with the proved cyclic
coefficient character theorem; surjectivity is not an input hypothesis. -/
theorem character_primitive_iff_surjective (f : EquivariantCharacter G N (ZMod n)) :
    addOrderOf f = n ↔ Function.Surjective f.toFun := by
  rw [← forgetCharacter_addOrderOf f, ← forgetCharacter_surjective_iff f]
  exact AddMonoidHom.CyclicCharacters.character_order_eq_level_iff_surjective
    (forgetCharacter f)

variable [ContinuousSMul G (ZMod n)]

/-- A pointed continuous H¹ class is primitive exactly when its geometric
additive homomorphism is surjective, the primitive-cover step of
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem pointed_primitive_iff_surjective
    (q : PointedH1 (G := G) (N := N) (A := ZMod n)) :
    addOrderOf q = n ↔ Function.Surjective (pointedGeometricHom q) := by
  rw [← pointedGeometricHom_addOrderOf q]
  exact AddMonoidHom.CyclicCharacters.character_order_eq_level_iff_surjective
    (pointedGeometricHom q)

/-- Continuous-character formulation of the primitive pointed-H¹ criterion
in `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem pointed_primitive_iff_character_surjective
    (q : PointedH1 (G := G) (N := N) (A := ZMod n)) :
    addOrderOf q = n ↔ Function.Surjective
      (pointedH1AddEquiv (G := G) (N := N) (A := ZMod n) q).toFun := by
  rw [← (pointedH1AddEquiv (G := G) (N := N) (A := ZMod n)).addOrderOf_eq q]
  exact character_primitive_iff_surjective _

/-- A primitive pointed class has transitive geometric translation monodromy,
and conversely, in the primitive-cover step of
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis.
No connected-torsor or isogeny theorem is assumed. -/
theorem pointed_primitive_iff_transitive
    (q : PointedH1 (G := G) (N := N) (A := ZMod n)) :
    letI := translationAction (pointedGeometricHom q)
    addOrderOf q = n ↔ MulAction.IsPretransitive N (ZMod n) :=
  (pointed_primitive_iff_surjective q).trans
    (translation_transitive_iff_surjective (pointedGeometricHom q)).symm

end FiniteLevel

end GroupCohomology.PrimitiveCharacters

/-!
This module retains the assigned pointed-character and geometric-comparison declarations.
The original source context below describes the full pre-split family;
its stated hypotheses and uninstantiated comparison boundaries remain in force.
-/

/-!
# Primitive pointed characters and marked incoming isogenies

Source: `K2-018#eq:k2018-pointed-character` and
`K2-018#prop:k2018-arithmetic-characters`, lines 341–445 of
`research/exposes/K2/018/expose.tex` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.

The direct continuous cocycle model `PointedH1` is used explicitly. Primitive
classes are first identified with surjective continuous equivariant characters,
using proved order preservation and finite cyclic algebra. General finite-etale
monodromy inputs then classify pointed geometrically connected coefficient
covers. The separately proved geometry comparison gives marked incoming cyclic
isogenies of actual group schemes over F, up to marked F-isomorphism.

The monodromy background quantifies over general finite etale coefficient
schemes and finite discrete modules; none of its fields mentions H¹, primitive
order, or isogenies. The geometric coefficient marking uses actual points over
an algebraically closed field and an explicit descent action. In particular,
cyclicity alone never identifies a coefficient scheme with the chi-square twist.
G and N are supplied continuous fundamental-group model data. Their actual
fundamental-group realization and the etale/cochain comparison are named
background boundaries, rather than an implicit replacement by discrete cohomology.
Each declaration's source pointer uses the module source basis above.
-/

noncomputable section

open CategoryTheory

open GroupCohomology.PointedCohomology GroupCohomology.PrimitiveCharacters

namespace GroupCohomology.PrimitiveCharacters.Translation

universe u v
attribute [local instance] Over.cartesianMonoidalCategory

variable {G N : Type*} [Group G] [Group N] [MulDistribMulAction G N]
  [TopologicalSpace G] [TopologicalSpace N]

/-- Primitive classes in the direct continuous model of
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
abbrev PrimitivePointed (n : ℕ) [DistribMulAction G (ZMod n)]
    [TopologicalSpace (ZMod n)] [IsTopologicalAddGroup (ZMod n)]
    [ContinuousSMul G (ZMod n)] :=
  {q : PointedH1 (G := G) (N := N) (A := ZMod n) // addOrderOf q = n}

/-- Surjective continuous equivariant characters in the primitive-cover step
of `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
abbrev SurjectiveCharacters (R : Type*) [AddCommGroup R] [DistribMulAction G R]
    [TopologicalSpace R] :=
  {f : EquivariantCharacter G N R // Function.Surjective f.toFun}

/-- The first stage of `K2-018#prop:k2018-arithmetic-characters`, on the module
source basis: a proved primitive-class/surjective-character equivalence. -/
def primitiveCharacterEquiv {n : ℕ} [NeZero n] [DistribMulAction G (ZMod n)]
    [TopologicalSpace (ZMod n)] [IsTopologicalAddGroup (ZMod n)]
    [ContinuousSMul G (ZMod n)] :
    PrimitivePointed (G := G) (N := N) n ≃ SurjectiveCharacters (G := G) (N := N) (ZMod n) where
  toFun q := ⟨pointedH1AddEquiv q.1,
    (pointed_primitive_iff_character_surjective q.1).mp q.2⟩
  invFun f := ⟨pointedH1AddEquiv.symm f.1,
    (pointed_primitive_iff_character_surjective (pointedH1AddEquiv.symm f.1)).mpr
      (by simpa using f.2)⟩
  left_inv q := Subtype.ext (pointedH1AddEquiv.symm_apply_apply q.1)
  right_inv f := Subtype.ext (pointedH1AddEquiv.apply_symm_apply f.1)

end GroupCohomology.PrimitiveCharacters.Translation

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 540b94a37c877a1a789075ca3ce962435a39b2cab7400b8b94681e49422be55d.
Definitions, hypotheses and universes are retained modulo native names. -/
