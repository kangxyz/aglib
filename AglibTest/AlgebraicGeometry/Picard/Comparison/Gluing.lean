/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.Comparison.Gluing
public import Aglib.AlgebraicGeometry.Picard.Comparison.GluingDescent

/-! Focused consumer of the gluing of rigidified pairs (Stacks 0B9N; Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Thm 2.5(2), p. 18): the rigidification of pulled-back pairs through the
origin pullback (`Gluing.lean`), the descent datum of compatible pairs and its effectivity along
`X ×_S U i ⟶ X ×_S T` (`GluingDescent.lean`), and the generic coherence
(`Rigidification.lean`). -/

@[expose] public section

noncomputable section
open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.RelativePicard Pseudofunctor
open Over (homMkFamily)

universe u

variable {S X : Scheme.{u}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

example (hc : ∀ Y : Over S, IsIso (pullback.snd p Y.hom).c) {T : Over S} {ι : Type (u + 1)}
    {U : ι → Scheme.{u}} (g : ∀ i, U i ⟶ T.left)
    (hg : Sieve.ofArrows U g ∈ Scheme.fppfTopology T.left)
    (P : ∀ i, RigidifiedPair p o ho (Over.mk (g i ≫ T.hom)))
    (hP : ∀ ⦃Y : Over S⦄ (q : Y ⟶ T) ⦃i₁ i₂ : ι⦄ (y₁ : Y ⟶ Over.mk (g i₁ ≫ T.hom))
      (y₂ : Y ⟶ Over.mk (g i₂ ≫ T.hom)), y₁ ≫ homMkFamily g i₁ = q → y₂ ≫ homMkFamily g i₂ = q →
        Nonempty (RigidifiedPair.Iso (RigidifiedPair.map y₁ (P i₁))
          (RigidifiedPair.map y₂ (P i₂)))) :
    ∃ L : Scheme.Modules.Invertible.LineBundle (pullback p T.hom), ∀ i,
      Nonempty ((Scheme.Modules.pullback ((familyScheme p).map (homMkFamily g i))).obj L.val ≅
        (P i).bundle.val) :=
  exists_lineBundle_of_rigidifiedPairs_of_isIso_c p o ho hc g hg P hP

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.map_rigidification_hom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms map_rigidification_hom

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.mapComp'_unit_pullbackUnitIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms mapComp'_unit_pullbackUnitIso

/--
info: 'CategoryTheory.CompEq.eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms CategoryTheory.CompEq.eq

/--
info: 'CategoryTheory.Pseudofunctor.CompTrans.rigCompat_pullHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CategoryTheory.Pseudofunctor.CompTrans.rigCompat_pullHom

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.RigidifiedPair.hom_eq_of_pairCompat_of_isIso_c' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RigidifiedPair.hom_eq_of_pairCompat_of_isIso_c

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.gluingDescentData' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms gluingDescentData

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.familyDescentData' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms familyDescentData

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.exists_iso_of_familyDescentData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exists_iso_of_familyDescentData

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.exists_lineBundle_of_rigidifiedPairs_of_isIso_c' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exists_lineBundle_of_rigidifiedPairs_of_isIso_c
