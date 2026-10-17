/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.Comparison.Injectivity

/-! Focused consumer of the reduction of Kleiman's Thm 2.5(1) (*The Picard scheme*,
arXiv:math/0504020v1, p. 18) to fppf descent of locally trivial classes. The comparison map is
the committed `toFppfPicardSheaf p`, Mathlib's sheafification unit for
`Scheme.fppfTopology.over S`; the descent property is stated on the committed
`familyPicardFunctor p` and `baseImage p`. The property is a hypothesis here. -/

@[expose] public section

noncomputable section
open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.RelativePicard

universe u

variable {S X : Scheme.{u}} (p : X ⟶ S)

example : FppfLocallyTrivialMemBaseImage p ↔
    ∀ T : (Over S)ᵒᵖ, ∀ a : (familyPicardFunctor p).obj T,
      Presheaf.equalizerSieve (F := familyPicardFunctor p) a 0 ∈
        (Scheme.fppfTopology.over S) T.unop → a ∈ baseImage p T :=
  Iff.rfl

example : FppfLocallyTrivialMemBaseImage p ↔
    ∀ T, Function.Injective ((toFppfPicardSheaf p).app T).hom :=
  fppfLocallyTrivialMemBaseImage_iff_injective p

example (h : FppfLocallyTrivialMemBaseImage p) : Mono (toFppfPicardSheaf p) :=
  mono_toFppfPicardSheaf_of_fppfLocallyTrivialMemBaseImage p h

example {T : (Over S)ᵒᵖ} (a : (familyPicardFunctor p).obj T)
    (ha : (toFppfPicardSheaf p).app T (QuotientAddGroup.mk a) = 0) :
    ∃ R : Sieve T.unop.left, R ∈ Scheme.fppfTopology T.unop.left ∧
      ∀ ⦃U : Scheme.{u}⦄ (g : U ⟶ T.unop.left), R g →
        Scheme.Modules.Invertible.pullbackClass ((familyScheme p).map
          (Over.homMk g : Over.mk (g ≫ T.unop.hom) ⟶ T.unop)) a = 0 :=
  exists_sieve_of_toFppfPicardSheaf_app_eq_zero p a ha

example [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] {T : Scheme.{u}}
    (g : T ⟶ S) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd p g)).unit.app
      (SheafOfModules.unit T.ringCatSheaf)) :=
  Scheme.Modules.isIso_unit_app_unit_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral p g

/--
info: 'AlgebraicGeometry.Scheme.Modules.isIso_unit_app_unit_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Scheme.Modules.isIso_unit_app_unit_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.fppfLocallyTrivialMemBaseImage_iff_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fppfLocallyTrivialMemBaseImage_iff_injective

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.exists_sieve_of_toFppfPicardSheaf_app_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exists_sieve_of_toFppfPicardSheaf_app_eq_zero

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.mono_toFppfPicardSheaf_of_fppfLocallyTrivialMemBaseImage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms mono_toFppfPicardSheaf_of_fppfLocallyTrivialMemBaseImage
