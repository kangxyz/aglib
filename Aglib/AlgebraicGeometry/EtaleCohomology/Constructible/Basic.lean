/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteCoefficientPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Topology.Constructible

/-! # Constructible abelian coefficients on the original small-etale site

Constructibility is the affine-local finite-partition definition of SGA 4 IX 2.3
and Stacks, Definition 59.71.1 (03RW). Strata are actual locally closed subschemes
with constructible ranges, and their coefficient restrictions are the original
inverse images. Finite local values refer to finite abelian groups, rather than
finitely generated abelian groups or finite sets of sections on every test scheme.

No presentation, finite cogenerator, or colimit conclusion is part of the
definition. Those require separate constructions.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

attribute [local instance] hasSheafifyLarge

/-- A finite partition by actual constructible locally closed subschemes.
Empty strata and an empty partition of the empty scheme are permitted. -/
structure FiniteLocallyClosedPartition (X : Scheme.{u}) where
  /-- The number of parts. -/
  count : ℕ
  /-- The actual scheme of each part. -/
  stratum : Fin count → Scheme.{u}
  /-- The original immersion of each part into the base. -/
  inclusion : ∀ i, stratum i ⟶ X
  /-- Each part is a locally closed subscheme. -/
  immersion : ∀ i, IsImmersion (inclusion i)
  /-- Each image is constructible in the original base. -/
  constructible_range : ∀ i, Topology.IsConstructible (Set.range (inclusion i))
  /-- Distinct parts have disjoint images. -/
  disjoint : Pairwise fun i j => Disjoint (Set.range (inclusion i)) (Set.range (inclusion j))
  /-- The original immersions cover every point. -/
  covers : ∀ x : X, ∃ i, ∃ y : stratum i, inclusion i y = x

/-- The identity immersion gives the one-part constructible partition. -/
def FiniteLocallyClosedPartition.singleton (X : Scheme.{u}) :
    FiniteLocallyClosedPartition X where
  count := 1
  stratum _ := X
  inclusion _ := 𝟙 X
  immersion _ := inferInstance
  constructible_range _ := by
    change Topology.IsConstructible (Set.range (id : X → X))
    rw [Set.range_id]
    exact Topology.IsConstructible.univ
  disjoint := by
    intro i j hij
    exact False.elim (hij (Subsingleton.elim i j))
  covers x := ⟨0, x, rfl⟩

/-- A constructible partition carries finite locally constant restrictions of
the original coefficient sheaf on each actual part. -/
structure ConstructiblePartition {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X)
    extends FiniteLocallyClosedPartition X where
  /-- The actual inverse-image coefficient is finite locally constant. -/
  locally_constant : ∀ i, IsFiniteLocallyConstant ((inverseImage (inclusion i)).obj F)

/-- Finite local constancy produces an actual one-part constructible partition. -/
def ConstructiblePartition.ofFiniteLocallyConstant {X : Scheme.{u}}
    {F : AbelianSheaf.{u, u + 1} X} (hF : IsFiniteLocallyConstant F) :
    ConstructiblePartition F where
  toFiniteLocallyClosedPartition := FiniteLocallyClosedPartition.singleton X
  locally_constant _ := isFiniteLocallyConstant_pullback (𝟙 X) hF

/-- A coefficient isomorphism transports the same original partition and immersions. -/
def ConstructiblePartition.ofIso {X : Scheme.{u}} {F G : AbelianSheaf.{u, u + 1} X}
    (t : ConstructiblePartition F) (e : F ≅ G) : ConstructiblePartition G where
  toFiniteLocallyClosedPartition := t.toFiniteLocallyClosedPartition
  locally_constant i :=
    (isFiniteLocallyConstant_iff_of_iso ((inverseImage (t.inclusion i)).mapIso e)).mp
      (t.locally_constant i)

/-- An abelian sheaf is constructible when every affine open admits a finite
constructible locally closed partition with finite locally constant restrictions. -/
def IsConstructible {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X) : Prop :=
  ∀ U : X.affineOpens,
    Nonempty (ConstructiblePartition ((inverseImage U.1.ι).obj F))

/-- Constructibility is invariant under actual coefficient isomorphisms. -/
theorem isConstructible_iff_of_iso {X : Scheme.{u}}
    {F G : AbelianSheaf.{u, u + 1} X} (e : F ≅ G) :
    IsConstructible F ↔ IsConstructible G := by
  constructor
  · intro h U
    obtain ⟨t⟩ := h U
    exact ⟨t.ofIso ((inverseImage U.1.ι).mapIso e)⟩
  · intro h U
    obtain ⟨t⟩ := h U
    exact ⟨t.ofIso ((inverseImage U.1.ι).mapIso e.symm)⟩

/-- Every finite locally constant coefficient is constructible, on any scheme. -/
theorem isConstructible_of_isFiniteLocallyConstant {X : Scheme.{u}}
    {F : AbelianSheaf.{u, u + 1} X} (hF : IsFiniteLocallyConstant F) :
    IsConstructible F := by
  intro U
  exact ⟨ConstructiblePartition.ofFiniteLocallyConstant
    (isFiniteLocallyConstant_pullback U.1.ι hF)⟩

/-- The actual constant sheaf of any finite abelian value has its identity-chart
finite local trivialization, in the original coefficient universe. -/
def finiteConstantTrivialization (X : Scheme.{u}) (A : AddCommGrpCat.{u + 1}) [Finite A] :
    FiniteLocalTrivialization
      ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A) where
  index := PUnit.{u + 1}
  chart _ := etaleTerminal X
  covers x := ⟨PUnit.unit, x, rfl⟩
  value _ := A
  finite_value _ := inferInstance
  trivialization _ := (inverseImageConstantIso (𝟙 X)).app A

/-- Finite constant abelian sheaves are constructible without an order condition. -/
theorem isConstructible_constant (X : Scheme.{u}) (A : AddCommGrpCat.{u + 1}) [Finite A] :
    IsConstructible
      ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A) :=
  isConstructible_of_isFiniteLocallyConstant ⟨finiteConstantTrivialization X A⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
