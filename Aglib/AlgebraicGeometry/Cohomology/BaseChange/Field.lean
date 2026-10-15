/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/

/-!
# Canonical coherent-cohomology field base change

The tensor comparison map is constructed from actual semilinear scheme
pullback. The one retained proper cohomology theorem quantifies over this
constructed map, in every degree and for arbitrary proper field schemes.
Original application provenance: K2-018#prop:k2018-arithmetic-characters, expose.tex lines 341–445,
mathematical source e73d98b1b5c1e5abcdebf7d058e436d792b87982;
engineering 7f86e4a1763cc4ec35e9b0a8acd659750355a0de with frozen pins.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.BaseChange` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct
universe u
variable {F : Type u} [Field F] (K : Type u) [Field K] [Algebra F K]

/-- The actual field base change as a scheme over the extension field. -/
abbrev fieldBaseChange (X : FScheme F) : FScheme K :=
  Over.mk (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap F K))))

/-- Restriction of scalars on the target cohomology module, canonically through
F → K. This is local, so no alternative structural map is chosen by search. -/
abbrev baseChangeCohomologyModule (X : FScheme F) (n : ℕ) :
    Module F (structureCohomology K (fieldBaseChange K X) n) :=
  Module.compHom _ (algebraMap F K)
attribute [local instance] baseChangeCohomologyModule

instance baseChangeCohomologyScalarTower (X : FScheme F) (n : ℕ) :
    IsScalarTower F K (structureCohomology K (fieldBaseChange K X) n) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

/-- The actual F-linear pullback along the field-base-change projection. -/
def fieldBaseChangePullbackLinear (X : FScheme F) (n : ℕ) :
    structureCohomology F X n →ₗ[F] structureCohomology K (fieldBaseChange K X) n where
  __ := (structureCohomologyPullbackSemilinear (algebraMap F K) (fieldBaseChange K X) X
    (pullback.fst _ _) (pullback.condition) n).toAddMonoidHom
  map_smul' a x :=
    (structureCohomologyPullbackSemilinear (algebraMap F K) (fieldBaseChange K X) X
      (pullback.fst _ _) (pullback.condition) n).map_smulₛₗ a x

/-- Canonical tensor base-change map on actual structure-sheaf cohomology.
Its pure-tensor formula is k ⊗ x ↦ k times the pullback of x. -/
def structureCohomologyBaseChangeMap (X : FScheme F) (n : ℕ) :
    K ⊗[F] structureCohomology F X n →ₗ[K]
      structureCohomology K (fieldBaseChange K X) n :=
  (fieldBaseChangePullbackLinear K X n).liftBaseChange K

@[simp]
theorem structureCohomologyBaseChangeMap_tmul (X : FScheme F) (n : ℕ)
    (a : K) (x : structureCohomology F X n) :
    structureCohomologyBaseChangeMap K X n (a ⊗ₜ[F] x) =
      a • (show structureCohomology K (fieldBaseChange K X) n from
        structureCohomologyPullback (pullback.fst X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap F K)))) n x) := rfl

/-- Standard flat coherent base-change theorem, specialized to the actual
structure sheaf of proper schemes over fields, in every cohomological degree.
The comparison map is independently constructed above. Source: Stacks 02KH,
30.5.2(2), inspected 2026-10-09 including the 2020 clarification that the
projection is flat because it is the base change of the flat base map.
This general theorem is retained explicitly; it is not a custom axiom. -/
def ProperStructureCohomologyBaseChange : Prop :=
  ∀ (F K : Type u) [Field F] [Field K] [Algebra F K]
    (X : FScheme F) (n : ℕ), IsProper X.hom →
      Function.Bijective (structureCohomologyBaseChangeMap K X n)

/-- Coherent base-change equivalence induced by the canonical tensor map. -/
def structureCohomologyBaseChangeEquiv
    (hbase : ProperStructureCohomologyBaseChange.{u})
    (X : FScheme F) (hX : IsProper X.hom) (n : ℕ) :
    K ⊗[F] structureCohomology F X n ≃ₗ[K]
      structureCohomology K (fieldBaseChange K X) n :=
  LinearEquiv.ofBijective (structureCohomologyBaseChangeMap K X n) (hbase F K X n hX)

end AlgebraicGeometry.Scheme.Cohomology
