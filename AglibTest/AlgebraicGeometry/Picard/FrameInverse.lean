/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.FrameInverse

/-! Native consumers of inverse-frame class and all-level compatible-power laws. -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent
open AlgebraicGeometry.Scheme.Modules.Invertible.FrameInverse
open AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower
open AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower
open AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients

universe u w
variable (X : Scheme.{u})

example [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] (L : LineBundle X) :
    torsorExtClass (coframeTorsor etaleLineBundleDescent X L) =
      FrameTensor.picardH1Equiv.{u, w} X (-classOf X L) :=
  torsorExtClass_coframe_picard X L

example {n : ℕ} (P : Pair X n)
    (φ : P.lineBundle.val ≅ SheafOfModules.unit X.ringCatSheaf) :
    TrivializedPowerTorsor.powerValue X P φ = 1 ↔
      (coframePowerIso X P φ.symm).hom = 𝟙 _ :=
  powerValue_eq_one_iff_inverse X P φ

example (P : Pair X 1) :
    TrivializedPowerTorsor.CompatibleFrame X P ≃ CompatibleCoframe X P :=
  compatibleInverseEquiv X P

example (h : EtaleLineBundleDescent.{u}) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) (P : Pair X n) (U : X.Etaleᵒᵖ)
    (ζ : (mu X n).obj.obj U)
    (s : (TrivializedPowerTorsor.torsor h X n hn hinv P).carrier.obj.obj U) :
    (inverseSectionsEquiv h X n hn hinv P U
      ((TrivializedPowerTorsor.torsor h X n hn hinv P).action U ζ s)).val =
      (inverseSectionsEquiv h X n hn hinv P U s).val ≪≫
        ScalarAutomorphisms.scalarIso U.unop.left
          ((Scheme.Modules.pullback U.unop.hom).obj P.lineBundle.val)
          ((rootsSections X n U (-ζ)).toMul : Γ(U.unop.left, ⊤)ˣ) :=
  inverseSectionsEquiv_action h X n hn hinv P U ζ s

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.FrameInverse.torsorExtClass_coframe_picard' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms torsorExtClass_coframe_picard

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.FrameInverse.inverseSectionsEquiv_action' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms inverseSectionsEquiv_action
