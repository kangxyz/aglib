/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.GroupCohomology.H1.SplitExtension

/-!
# Coefficient functoriality on actual continuous degree-one cohomology

Source: `research/exposes/K2/018/expose.tex`,
`K2-018#eq:k2018-coefficient-compatibility`, lines 292–306,
`K2-018#eq:k2018-pointed-character`, lines 341–355, and the unique-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442, at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Complete source-file SHA-256:
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.
The source identity applies to every declaration below.

The cocycle and H¹ types are those of the accepted `PointedCohomology` module,
source SHA-256 `098608d067477daa65ddd87788e3e1e615900cd374b1e96d26c0d5826376aced`.
Its H¹ is the shared continuous-cohomology quotient in split coordinates.
Composition with a continuous equivariant additive coefficient map preserves
continuous cocycles and coboundaries, hence induces an additive H¹ map. The
proofs include section restriction, geometric restriction, and the pointed
subgroup, as well as the identity and composition laws. Pointed injectivity is
derived through the existing equivalence with continuous geometric characters.
No global H¹ coefficient-injectivity theorem is assumed or asserted.

This is auxiliary cohomological algebra in the topological split-group model.
Étale realization, cyclotomic-character construction, and connecting-morphism
coefficient-triangle comparisons remain separate general backgrounds. In
particular, no Bockstein equation is included as data in the constructed maps.
-/

@[expose] public section

namespace GroupCohomology.CoefficientFunctoriality

open GroupCohomology.PointedCohomology

variable {G N A B C : Type*} [Group G] [Group N] [MulDistribMulAction G N]
  [TopologicalSpace G] [TopologicalSpace N]
  [AddCommGroup A] [DistribMulAction G A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddCommGroup B] [DistribMulAction G B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [AddCommGroup C] [DistribMulAction G C] [TopologicalSpace C] [IsTopologicalAddGroup C]

variable (f : A →+ B) (hf : Continuous f) (he : ∀ g : G, ∀ a : A, f (g • a) = g • f a)

/-- Compose actual continuous cocycles with a continuous equivariant additive coefficient map.
Source: auxiliary continuous coefficient algebra for `K2-018#eq:k2018-coefficient-compatibility` and
`K2-018#eq:k2018-pointed-character`,
at the documented source snapshot. -/
def cocycleMap : ContinuousCocycle G N A →+ ContinuousCocycle G N B where
  toFun c := {
    toFun x := f (c.toFun x)
    continuous_toFun := hf.comp c.continuous_toFun
    cocycle u v g h := by rw [c.cocycle, map_add, he] }
  map_zero' := by apply ContinuousCocycle.ext; intro x; exact map_zero f
  map_add' c d := by apply ContinuousCocycle.ext; intro x; exact map_add f _ _

/-- The constructed coefficient cocycle map evaluates by composition.
Source: auxiliary continuous coefficient algebra for `K2-018#eq:k2018-coefficient-compatibility` and
`K2-018#eq:k2018-pointed-character`,
at the documented source snapshot. -/
@[simp] theorem cocycleMap_apply (c : ContinuousCocycle G N A) (x : N × G) :
    (cocycleMap f hf he c).toFun x = f (c.toFun x) := rfl

/-- Compose continuous geometric characters with the same coefficient map.
Source: auxiliary continuous coefficient algebra for `K2-018#eq:k2018-coefficient-compatibility` and
`K2-018#eq:k2018-pointed-character`,
at the documented source snapshot. -/
def characterMap : EquivariantCharacter G N A →+ EquivariantCharacter G N B where
  toFun c := {
    toFun x := f (c.toFun x)
    continuous_toFun := hf.comp c.continuous_toFun
    map_mul u v := by rw [c.map_mul, map_add]
    map_action g u := by rw [c.map_action, he] }
  map_zero' := by apply EquivariantCharacter.ext; intro x; exact map_zero f
  map_add' c d := by apply EquivariantCharacter.ext; intro x; exact map_add f _ _

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypothesis and binder order.
/-- The constructed character map evaluates by composition.
Source: auxiliary continuous coefficient algebra for `K2-018#eq:k2018-coefficient-compatibility` and
`K2-018#eq:k2018-pointed-character`,
at the documented source snapshot. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[simp, nolint unusedArguments]
theorem characterMap_apply (c : EquivariantCharacter G N A) (u : N) :
    (characterMap f hf he c).toFun u = f (c.toFun u) := rfl

/-- The faithful additive-homomorphism form of a continuous equivariant character; continuity
remains in its source type.
Source: auxiliary continuous coefficient algebra for `K2-018#eq:k2018-pointed-character`,
at the documented source snapshot. -/
def characterToAddHom : EquivariantCharacter G N A →+ (Additive N →+ A) where
  toFun c := {
    toFun x := c.toFun x.toMul
    map_zero' := c.map_one
    map_add' u v := c.map_mul u.toMul v.toMul }
  map_zero' := by ext u; rfl
  map_add' c d := by ext u; rfl

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypothesis and binder order.
/-- Evaluation of the underlying additive character on the tagged geometric group.
Source: auxiliary continuous coefficient algebra for `K2-018#eq:k2018-pointed-character`,
at the documented source snapshot. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[simp, nolint unusedArguments]
theorem characterToAddHom_apply (c : EquivariantCharacter G N A) (u : N) :
    characterToAddHom c (Additive.ofMul u) = c.toFun u := rfl

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypothesis and binder order.
/-- Forgetting continuity and equivariance preserves character equality, by pointwise
extensionality.
Source: auxiliary continuous coefficient algebra for `K2-018#eq:k2018-pointed-character`,
at the documented source snapshot. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem characterToAddHom_injective :
    Function.Injective (characterToAddHom (G := G) (N := N) (A := A)) := by
  intro c d h
  apply EquivariantCharacter.ext
  intro u
  exact DFunLike.congr_fun h (Additive.ofMul u)

variable [ContinuousSMul G A] [ContinuousSMul G B] [ContinuousSMul G C]

/-- A coefficient map sends a coboundary to the coboundary of the image coefficient.
Source: auxiliary continuous coefficient algebra for `K2-018#eq:k2018-coefficient-compatibility` and
`K2-018#eq:k2018-pointed-character`,
at the documented source snapshot. -/
theorem cocycleMap_coboundary (a : A) :
    cocycleMap f hf he (coboundaryHom (G := G) (N := N) a) =
      coboundaryHom (G := G) (N := N) (f a) := by
  apply ContinuousCocycle.ext
  intro x
  change f (x.2 • a - a) = x.2 • f a - f a
  rw [map_sub, he]

/-- The additive coefficient map on the existing continuous cocycle/coboundary quotient.
Source: auxiliary continuous coefficient algebra for `K2-018#eq:k2018-coefficient-compatibility` and
`K2-018#eq:k2018-pointed-character`,
at the documented source snapshot. -/
def h1Map : ContinuousH1 (G := G) (N := N) (A := A) →+
    ContinuousH1 (G := G) (N := N) (A := B) :=
  continuousH1Lift ((continuousH1Mk (G := G) (N := N) (A := B)).comp
    (cocycleMap f hf he)) (by
      rintro c ⟨a, rfl⟩
      change continuousH1Mk (cocycleMap f hf he (coboundaryHom a)) = 0
      rw [cocycleMap_coboundary]
      exact (continuousH1Mk_eq_zero_iff _).2 ⟨f a, fun _ _ => rfl⟩)

/-- The induced cohomology map has the prescribed cocycle-composition representative.
Source: auxiliary continuous coefficient algebra for `K2-018#eq:k2018-coefficient-compatibility` and
`K2-018#eq:k2018-pointed-character`,
at the documented source snapshot. -/
-- Keep this original canonical-map simp formula alongside its lower evaluation expansion.
@[simp, nolint simpNF] theorem h1Map_mk (c : ContinuousCocycle G N A) :
    h1Map f hf he (continuousH1Mk c) = continuousH1Mk (cocycleMap f hf he c) := rfl

/-- Coefficient change commutes with actual section restriction.
Source: auxiliary continuous coefficient algebra for `K2-018#eq:k2018-coefficient-compatibility` and
`K2-018#eq:k2018-pointed-character`,
at the documented source snapshot. -/
theorem h1Map_section (q : ContinuousH1 (G := G) (N := N) (A := A)) :
    continuousH1SectionRestriction (h1Map f hf he q) =
      h1Map (N := PUnit.{1}) f hf he (continuousH1SectionRestriction q) := by
  obtain ⟨c, rfl⟩ := continuousH1Mk_surjective q
  rw [h1Map_mk, continuousH1SectionRestriction_mk,
    continuousH1SectionRestriction_mk, h1Map_mk]
  rfl

/-- Coefficient change commutes with actual geometric-character restriction.
Source: auxiliary continuous coefficient algebra for `K2-018#eq:k2018-coefficient-compatibility` and
`K2-018#eq:k2018-pointed-character`,
at the documented source snapshot. -/
theorem h1Map_geometric (q : ContinuousH1 (G := G) (N := N) (A := A)) :
    geometricH1Hom (h1Map f hf he q) = characterMap f hf he (geometricH1Hom q) := by
  obtain ⟨c, rfl⟩ := continuousH1Mk_surjective q
  rw [h1Map_mk, geometricH1Hom_mk, geometricH1Hom_mk]
  rfl

/-- The induced coefficient map restricts to the kernel of section cohomology.
Source: auxiliary continuous coefficient algebra for `K2-018#eq:k2018-coefficient-compatibility` and
`K2-018#eq:k2018-pointed-character`,
at the documented source snapshot. -/
def pointedH1Map : PointedH1 (G := G) (N := N) (A := A) →+
    PointedH1 (G := G) (N := N) (A := B) where
  toFun q := ⟨h1Map f hf he q.1, by
    change continuousH1SectionRestriction (h1Map f hf he q.1) = 0
    rw [h1Map_section]
    have hq : continuousH1SectionRestriction q.1 = 0 := q.2
    rw [hq, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' q r := Subtype.ext (map_add _ _ _)

/-- The pointed map is the restriction of the actual H¹ coefficient map.
Source: auxiliary continuous coefficient algebra for `K2-018#eq:k2018-coefficient-compatibility` and
`K2-018#eq:k2018-pointed-character`,
at the documented source snapshot. -/
@[simp] theorem pointedH1Map_coe (q : PointedH1 (G := G) (N := N) (A := A)) :
    (pointedH1Map f hf he q).1 = h1Map f hf he q.1 := rfl

/-- The pointed-character equivalence is natural under coefficient change.
Source: auxiliary continuous coefficient algebra for `K2-018#eq:k2018-coefficient-compatibility` and
`K2-018#eq:k2018-pointed-character`,
at the documented source snapshot. -/
theorem pointedH1Map_geometric (q : PointedH1 (G := G) (N := N) (A := A)) :
    pointedH1AddEquiv (pointedH1Map f hf he q) =
      characterMap f hf he (pointedH1AddEquiv q) := h1Map_geometric f hf he q.1

omit [ContinuousSMul G A] [ContinuousSMul G B] in
set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypothesis and binder order.
/-- An injective coefficient map is injective on continuous geometric characters.
Source: auxiliary continuous coefficient algebra for `K2-018#eq:k2018-coefficient-compatibility` and
`K2-018#eq:k2018-pointed-character`,
at the documented source snapshot. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem characterMap_injective (hi : Function.Injective f) :
    Function.Injective (characterMap (N := N) f hf he) := by
  intro c d h
  apply EquivariantCharacter.ext
  intro u
  apply hi
  exact congrArg (fun c : EquivariantCharacter G N B => c.toFun u) h

/-- An injective coefficient map is injective on pointed H¹, by geometric-character restriction.
This proof uses no global H¹ injectivity.
Source: auxiliary continuous coefficient algebra for `K2-018#eq:k2018-coefficient-compatibility` and
`K2-018#eq:k2018-pointed-character`,
at the documented source snapshot. -/
theorem pointedH1Map_injective (hi : Function.Injective f) :
    Function.Injective (pointedH1Map (N := N) f hf he) := by
  intro q r h
  apply (pointedH1AddEquiv (G := G) (N := N) (A := A)).injective
  apply characterMap_injective f hf he hi
  rw [← pointedH1Map_geometric, ← pointedH1Map_geometric, h]

/-- The constructed continuous H¹ coefficient map preserves the identity coefficient homomorphism.
Source: auxiliary continuous coefficient algebra for `K2-018#eq:k2018-coefficient-compatibility` and
`K2-018#eq:k2018-pointed-character`,
at the documented source snapshot. -/
theorem h1Map_id : h1Map (G := G) (N := N) (AddMonoidHom.id A)
    continuous_id (fun _ _ => rfl) = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro q
  obtain ⟨c, rfl⟩ := continuousH1Mk_surjective q
  rw [h1Map_mk]
  rfl

/-- The constructed continuous H¹ coefficient map preserves composition of coefficient
homomorphisms.
Source: auxiliary continuous coefficient algebra for `K2-018#eq:k2018-coefficient-compatibility` and
`K2-018#eq:k2018-pointed-character`,
at the documented source snapshot. -/
theorem h1Map_comp (k : B →+ C) (hk : Continuous k)
    (hke : ∀ g : G, ∀ b : B, k (g • b) = g • k b) :
    h1Map (G := G) (N := N) (k.comp f) (hk.comp hf)
      (fun g a => by change k (f (g • a)) = _; rw [he, hke]; rfl) =
    (h1Map k hk hke).comp (h1Map f hf he) := by
  apply AddMonoidHom.ext
  intro q
  obtain ⟨c, rfl⟩ := continuousH1Mk_surjective q
  rw [h1Map_mk]
  change continuousH1Mk _ = h1Map k hk hke (h1Map f hf he (continuousH1Mk c))
  rw [h1Map_mk, h1Map_mk]
  rfl

end GroupCohomology.CoefficientFunctoriality

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 dda2fb0abf45fd2e335dba2b6b888aa56d32f270a7abbc34abd51a615cc054c4.
Definitions, hypotheses and universes are retained modulo native names. -/
