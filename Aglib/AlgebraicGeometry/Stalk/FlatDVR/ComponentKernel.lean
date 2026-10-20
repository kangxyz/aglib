/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.Scalar
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Conditional stalk-kernel interface for vertical components

Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.FlatDVRComponentKernel`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `ed9a5d78e7c17a989ab5c1dca63b611cc83fa10efbcb6d333a052fc91b13f07a`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.FlatDVR

/-- Actual scalar map to the actual scheme stalk: pull back a global constant
on Spec R and then take its germ. -/
def stalkScalar {R : Type u} [CommRing R] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of R)) (x : X) : R →+* X.presheaf.stalk x :=
  π.stalkScalar x

/-- The component interface uses the canonical structural scalar map without changing it. -/
@[simp]
theorem stalkScalar_eq_canonical {R : Type u} [CommRing R] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of R)) (x : X) : stalkScalar π x = π.stalkScalar x := rfl

/-- Conditional kernel family for actual integral components of the literal special fibre.
The nonzerodivisor conclusion follows from the generic
`Scheme.Hom.stalkScalar_mem_nonZeroDivisors` theorem. The assertion that the actual
closed-immersion stalk kernel is minimal above the actual uniformizer ideal
remains an explicit input; this definition does not supply it.

No regularity, properness, whole-fibre reducedness or component inventory is assumed. -/
def FlatDVRFibreComponentKernel : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X C : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral C]
    (π : X ⟶ Spec (.of R))
    (i : C ⟶ pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (ϖ : R),
    Flat π → IsClosedImmersion i →
    Set.range i ∈ irreducibleComponents
      (pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) : Scheme.{u}) →
    Irreducible ϖ → ∀ c : C,
      let j := i ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
      stalkScalar π (j c) ϖ ∈ nonZeroDivisors (X.presheaf.stalk (j c)) ∧
      RingHom.ker (j.stalkMap c).hom ∈
        (Ideal.span {stalkScalar π (j c) ϖ}).minimalPrimes


end AlgebraicGeometry.Scheme.FlatDVR
