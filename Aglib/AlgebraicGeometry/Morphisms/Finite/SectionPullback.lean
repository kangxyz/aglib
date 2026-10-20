/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Finite.GenericSection
public import Mathlib.AlgebraicGeometry.Limits

/-!
# A specified generic point above a section of a finite morphism

The literal pullback of the finite morphism along the supplied base section
is finite over the same integrally closed domain. Extending its specified
generic point and composing with its first projection gives a point of the
original source. Both its generic specialization and the original section
triangle are retained. The source need not be integral or connected.

Source: unmarked `originPullback` and `sourceOrigin` slices of
`R5Lab.AlgebraicGeometry.Curves.LocalModels.CyclicCovers.Origin:55–115`,
R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`3c7bd17bab5363e790aacf9c9e5821790b27464213f5e58a6021a979accac414`.
The application supplied the point using an elliptic identity; the general
statement takes that same actual generic point and its original triangle.
The algebraic base assumptions remain those of `Finite.GenericSection`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom.FiniteSection

universe u
variable {R F : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field F] [Algebra R F] [IsFractionRing R F]
  {X Y : Scheme.{u}} (p : X ⟶ Y) [IsFinite p] (σ : Spec (.of R) ⟶ Y)
  (g : Spec (.of F) ⟶ X)
  (hg : g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ σ)

/-- Extend the given generic point of the literal finite pullback and project
back to the same source scheme. -/
def aboveSection : Spec (.of R) ⟶ X :=
  extendedSection (pullback.snd p σ)
    (pullback.lift g (Spec.map (CommRingCat.ofHom (algebraMap R F))) hg)
    (pullback.lift_snd _ _ _) ≫ pullback.fst p σ

@[reassoc (attr := simp)] theorem aboveSection_over :
    aboveSection p σ g hg ≫ p = σ := by
  rw [aboveSection, Category.assoc, pullback.condition,
    ← Category.assoc, extendedSection_over, Category.id_comp]

@[reassoc (attr := simp)] theorem aboveSection_generic :
    Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ aboveSection p σ g hg = g := by
  rw [aboveSection, ← Category.assoc, extendedSection_generic]
  exact pullback.lift_fst _ _ _

/-- A compatible original structural map makes the constructed source point
a section of that same structural map. -/
@[reassoc (attr := simp)] theorem aboveSection_structure
    (πX : X ⟶ Spec (.of R)) (πY : Y ⟶ Spec (.of R))
    (hp : p ≫ πY = πX) (hσ : σ ≫ πY = 𝟙 _) :
    aboveSection p σ g hg ≫ πX = 𝟙 _ := by
  rw [← hp, ← Category.assoc, aboveSection_over, hσ]

end AlgebraicGeometry.Scheme.Hom.FiniteSection
