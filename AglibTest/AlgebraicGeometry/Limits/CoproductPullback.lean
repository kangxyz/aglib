/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Limits.CoproductPullback

/-! Focused consumer of the components `Z ×_S H j` of the base change `Z ×_S ∐_j H j`: the
cartesian square, the image, the disjoint cover and, for finitely many components, the comparison
with `FiniteCoproductPullback.iso`, with axiom guards. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-- `Z ×_S H j` is the base change of `Sigma.ι H j`. -/
example {S Z : Scheme.{u}} (πZ : Z ⟶ S) {J : Type} {H : J → Scheme.{u}} (πH : ∀ j, H j ⟶ S)
    (j : J) :
    IsPullback (Scheme.pullbackSigmaι πZ πH j) (pullback.snd πZ (πH j))
      (pullback.snd πZ (Sigma.desc πH)) (Sigma.ι H j) :=
  Scheme.isPullback_pullbackSigmaι πZ πH j

/-- The components cover and are pairwise disjoint. -/
example {S Z : Scheme.{u}} (πZ : Z ⟶ S) {J : Type} {H : J → Scheme.{u}} (πH : ∀ j, H j ⟶ S) :
    (∀ x : ↑(pullback πZ (Sigma.desc πH)), ∃ j y, Scheme.pullbackSigmaι πZ πH j y = x) ∧
      Pairwise fun i j => Disjoint (Set.range (Scheme.pullbackSigmaι πZ πH i))
        (Set.range (Scheme.pullbackSigmaι πZ πH j)) :=
  ⟨Scheme.exists_pullbackSigmaι_eq πZ πH, Scheme.pairwise_disjoint_range_pullbackSigmaι πZ πH⟩

/-- For finitely many components, the component maps are the coprojections of the finite
coproduct–pullback comparison. -/
example {S Z : Scheme.{u}} (πZ : Z ⟶ S) {J : Type} [Finite J] {H : J → Scheme.{u}}
    (πH : ∀ j, H j ⟶ S) (j : J) :
    Scheme.pullbackSigmaι πZ πH j = (pullbackSymmetry πZ (πH j)).hom ≫
      Sigma.ι (fun j => pullback (πH j) πZ) j ≫ (FiniteCoproductPullback.iso H πH πZ).hom ≫
        (pullbackSymmetry (Sigma.desc πH) πZ).hom :=
  Scheme.pullbackSigmaι_eq_sigmaι_iso πZ πH j

/--
info: 'AlgebraicGeometry.Scheme.isPullback_pullbackSigmaι' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.isPullback_pullbackSigmaι

/--
info: 'AlgebraicGeometry.Scheme.pullbackSigmaι_eq_sigmaι_iso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.pullbackSigmaι_eq_sigmaι_iso
