/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.Coproduct.Family

/-! Focused consumer of the flatness, properness and surjectivity of the family on `Z ×_S ∐_j H j`
glued from families on the `Z ×_S H j`, with axiom guards. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-- Flat proper families on the components glue to a flat proper family over `∐ H`. -/
example {S Z : Scheme.{u}} (πZ : Z ⟶ S) {J : Type} [Finite J] {H : J → Scheme.{u}}
    (πH : ∀ j, H j ⟶ S) (D : ∀ j, (pullback πZ (πH j)).IdealSheafData)
    (hflat : ∀ j, Flat ((D j).subschemeι ≫ pullback.snd πZ (πH j)))
    (hprop : ∀ j, IsProper ((D j).subschemeι ≫ pullback.snd πZ (πH j))) :
    Flat ((Scheme.IdealSheafData.sigmaGlue πZ πH D).subschemeι ≫
        pullback.snd πZ (Sigma.desc πH)) ∧
      IsProper ((Scheme.IdealSheafData.sigmaGlue πZ πH D).subschemeι ≫
        pullback.snd πZ (Sigma.desc πH)) :=
  ⟨Scheme.IdealSheafData.flat_sigmaGlue πZ πH D hflat,
    Scheme.IdealSheafData.isProper_sigmaGlue πZ πH D hprop⟩

/-- Surjectivity over `∐ H` is checked on the components, in both directions. -/
example {S Z : Scheme.{u}} (πZ : Z ⟶ S) {J : Type} [Finite J] {H : J → Scheme.{u}}
    (πH : ∀ j, H j ⟶ S) (D : ∀ j, (pullback πZ (πH j)).IdealSheafData) :
    Surjective ((Scheme.IdealSheafData.sigmaGlue πZ πH D).subschemeι ≫
        pullback.snd πZ (Sigma.desc πH)) ↔
      ∀ j, Surjective ((D j).subschemeι ≫ pullback.snd πZ (πH j)) :=
  Scheme.IdealSheafData.sigmaGlue_iff πZ πH D

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.sigmaGlue_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.sigmaGlue_iff

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.flat_sigmaGlue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.flat_sigmaGlue
