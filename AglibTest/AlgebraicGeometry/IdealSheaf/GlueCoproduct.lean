/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.IdealSheaf.GlueCoproduct

/-! Focused consumer of closed subschemes over a disjoint union of bases: the family on
`Z ×_S ∐_j H j` glued from families on the `Z ×_S H j`, its restrictions, uniqueness and base
change along a component, and closed subschemes of `Z ×_S T` compared over an open cover of `T`,
with axiom guards. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-- The glued family restricts to the given families. -/
example {S Z : Scheme.{u}} (πZ : Z ⟶ S) {J : Type} [Finite J] {H : J → Scheme.{u}}
    (πH : ∀ j, H j ⟶ S) (D : ∀ j, (pullback πZ (πH j)).IdealSheafData) (j : J) :
    (Scheme.IdealSheafData.sigmaGlue πZ πH D).comap (Scheme.pullbackSigmaι πZ πH j) = D j :=
  Scheme.IdealSheafData.comap_sigmaGlue πZ πH D j

/-- A closed subscheme of `Z ×_S ∐ H` restricting to every `D j` is the glued family. -/
example {S Z : Scheme.{u}} (πZ : Z ⟶ S) {J : Type} [Finite J] {H : J → Scheme.{u}}
    (πH : ∀ j, H j ⟶ S) (D : ∀ j, (pullback πZ (πH j)).IdealSheafData)
    (V : (pullback πZ (Sigma.desc πH)).IdealSheafData)
    (hV : ∀ j, V.comap (Scheme.pullbackSigmaι πZ πH j) = D j) :
    V = Scheme.IdealSheafData.sigmaGlue πZ πH D :=
  (Scheme.IdealSheafData.eq_sigmaGlue_iff πZ πH D V).mpr hV

/-- The pullback of the glued family along a morphism into one component. -/
example {S Z : Scheme.{u}} (πZ : Z ⟶ S) {J : Type} [Finite J] {H : J → Scheme.{u}}
    (πH : ∀ j, H j ⟶ S) (D : ∀ j, (pullback πZ (πH j)).IdealSheafData) {T : Scheme.{u}}
    (j : J) (b : T ⟶ H j) :
    (Scheme.IdealSheafData.sigmaGlue πZ πH D).comap
        (pullback.map πZ (b ≫ πH j) πZ (Sigma.desc πH) (𝟙 Z) (b ≫ Sigma.ι H j) (𝟙 S)
          (by simp) (by simp)) =
      (D j).comap (pullback.map πZ (b ≫ πH j) πZ (πH j) (𝟙 Z) b (𝟙 S) (by simp) (by simp)) :=
  Scheme.IdealSheafData.comap_sigmaGlue_pullbackMap πZ πH D _ j b rfl

/-- Closed subschemes of `Z ×_S T` agreeing over an open cover of `T` are equal. -/
example {S Z T : Scheme.{u}} (πZ : Z ⟶ S) (g : T ⟶ S) {ι : Type} {U : ι → Scheme.{u}}
    (j : ∀ i, U i ⟶ T) [∀ i, IsOpenImmersion (j i)] (hj : ∀ t, ∃ i y, j i y = t)
    (I I' : (pullback πZ g).IdealSheafData)
    (h : ∀ i, I.comap (pullback.map πZ (j i ≫ g) πZ g (𝟙 Z) (j i) (𝟙 S) (by simp) (by simp)) =
      I'.comap (pullback.map πZ (j i ≫ g) πZ g (𝟙 Z) (j i) (𝟙 S) (by simp) (by simp))) :
    I = I' :=
  Scheme.IdealSheafData.ext_of_comap_pullbackMap_eq πZ g j hj h

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.comap_sigmaGlue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.comap_sigmaGlue

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.ext_of_comap_pullbackMap_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.ext_of_comap_pullbackMap_eq
