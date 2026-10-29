/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.InfinitesimalLifting

/-!
# Consumer checks for smoothness from lifting of points

For a morphism `π : X ⟶ Spec k`, `k` a field (or any Noetherian ring), locally of finite type,
whose points lift along Noetherian square-zero thickenings: the stalk lifting, formal smoothness
of every stalk map, smoothness and the smooth locus; axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AglibTest.InfinitesimalLifting

variable {k : Type u} [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))

/-- The lifting at a stalk, for the structural `k`-algebra structure. -/
example (H : π.LiftsAlongNoetherianSquareZero) (x : X) :
    letI := (π.stalkScalar x).toAlgebra
    ∀ (A' A : Type u) [CommRing A'] [CommRing A] [IsLocalRing A'] [IsArtinianRing A']
      [Algebra k A'] [Algebra k A] (g : A' →ₐ[k] A), Function.Surjective g →
      RingHom.ker g ^ 2 = ⊥ → ∀ φ : X.presheaf.stalk x →ₐ[k] A, Function.Surjective φ →
        ∃ ψ : X.presheaf.stalk x →ₐ[k] A', g.comp ψ = φ :=
  H.exists_lift_stalk x

variable [LocallyOfFiniteType π]

/-- Every stalk map is formally smooth, at every point and over any field. -/
example (H : π.LiftsAlongNoetherianSquareZero) (x : X) : (π.stalkMap x).hom.FormallySmooth :=
  Hom.formallySmooth_stalkMap_of_liftsAlongNoetherianSquareZero H x

/-- Smoothness, and the smooth locus is the whole scheme. -/
example (H : π.LiftsAlongNoetherianSquareZero) : Smooth π ∧ π.smoothLocus = ⊤ :=
  have := Hom.smooth_of_liftsAlongNoetherianSquareZero H
  ⟨this, π.smoothLocus_eq_top⟩

end AglibTest.InfinitesimalLifting

/--
info: 'AlgebraicGeometry.Scheme.Hom.LiftsAlongNoetherianSquareZero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.LiftsAlongNoetherianSquareZero

/--
info: 'AlgebraicGeometry.Scheme.Hom.LiftsAlongNoetherianSquareZero.exists_lift_stalk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.LiftsAlongNoetherianSquareZero.exists_lift_stalk

/--
info: 'AlgebraicGeometry.Scheme.Hom.formallySmooth_stalkMap_of_formallySmooth_stalkScalar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.formallySmooth_stalkMap_of_formallySmooth_stalkScalar

/--
info: 'AlgebraicGeometry.Scheme.Hom.formallySmooth_stalkMap_of_liftsAlongNoetherianSquareZero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.formallySmooth_stalkMap_of_liftsAlongNoetherianSquareZero

/--
info: 'AlgebraicGeometry.Scheme.Hom.smooth_of_liftsAlongNoetherianSquareZero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.smooth_of_liftsAlongNoetherianSquareZero
