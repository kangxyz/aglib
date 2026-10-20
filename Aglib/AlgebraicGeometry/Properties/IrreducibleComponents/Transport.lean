/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.Topology.Irreducible

/-!
# Irreducible components and morphism fibres under isomorphisms

Source: `R5Lab.Aglib.AlgebraicGeometry.IrreducibleComponents.Transport`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `425225e5eb630f5d1d98d06a5d86725ddcfbd59b850891a33a1c1efc303d1f63`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme
/-- Actual component sets are transported by a scheme isomorphism. -/
def componentsEquiv {X Y : Scheme.{u}} (e : X ≅ Y) :
    irreducibleComponents X ≃ irreducibleComponents Y := by
  let h := e.hom.homeomorph
  exact (irreducibleComponentsEquivOfIsPreirreducibleFiber h h.continuous h.isOpenMap
    (fun _ => (Set.subsingleton_singleton.preimage h.injective).isPreirreducible)
    h.surjective).toEquiv.symm

/-- Postcomposing a normalization map with an actual target isomorphism
transports its point fibres without supplying any branch cardinality. -/
def fibreEquivOfTargetIso {N C S : Scheme.{u}} (ν : N ⟶ C) (e : S ≅ C) (y : C) :
    {z : N // (ν ≫ e.inv) z = e.inv y} ≃ {z : N // ν z = y} :=
  Equiv.subtypeEquivRight fun z => by
    change e.inv (ν z) = e.inv y ↔ ν z = y
    exact e.inv.homeomorph.injective.eq_iff


end AlgebraicGeometry.Scheme
