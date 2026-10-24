/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Root.Basic

/-! # The actual power error of a fixed-target bundle isomorphism

The error is an automorphism of the original fixed target. It is identity
exactly for root-pair isomorphisms. Its pullback and scalar-correction
equations retain the original tensor-power comparisons.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Invertible.Root

universe u

variable {X : Scheme.{u}} {L : LineBundle X} {n : ℕ}

/-- The original tensor-power error, as an actual automorphism of the fixed target. -/
def powerError (P Q : Pair L n) (e : P.bundle.val ≅ Q.bundle.val) : L.val ≅ L.val :=
  P.powerIso.symm ≪≫ TrivializedPower.powerIso X e n ≪≫ Q.powerIso

/-- Identity error is exactly the original power compatibility equation. -/
theorem powerError_eq_refl_iff (P Q : Pair L n) (e : P.bundle.val ≅ Q.bundle.val) :
    powerError P Q e = CategoryTheory.Iso.refl _ ↔
      (TrivializedPower.powerIso X e n).hom ≫ Q.powerIso.hom = P.powerIso.hom := by
  constructor
  · intro h
    apply (cancel_epi P.powerIso.inv).mp
    calc
      P.powerIso.inv ≫ ((TrivializedPower.powerIso X e n).hom ≫ Q.powerIso.hom) =
          (powerError P Q e).hom := rfl
      _ = 𝟙 _ := congrArg CategoryTheory.Iso.hom h
      _ = P.powerIso.inv ≫ P.powerIso.hom := P.powerIso.inv_hom_id.symm
  · intro h
    apply CategoryTheory.Iso.ext
    change P.powerIso.inv ≫ ((TrivializedPower.powerIso X e n).hom ≫ Q.powerIso.hom) = 𝟙 _
    rw [h, CategoryTheory.Iso.inv_hom_id]

/-- The power error pulls back by the original module functor, with no change of target. -/
theorem powerError_pullback {T : Scheme.{u}} (f : T ⟶ X)
    (P Q : Pair L n) (e : P.bundle.val ≅ Q.bundle.val) :
    powerError (P.pullback f) (Q.pullback f) ((Scheme.Modules.pullback f).mapIso e) =
      (Scheme.Modules.pullback f).mapIso (powerError P Q e) := by
  apply CategoryTheory.Iso.ext
  have hn := congrArg CategoryTheory.Iso.hom
    (PowerPullbackNaturality.pullbackPowerIso_naturality f e n)
  have ht := congrArg
    (fun z => z ≫ (PowerPullback.pullbackPowerIso f Q.bundle n).inv) hn
  simp only [CategoryTheory.Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    CategoryTheory.Iso.hom_inv_id, Category.comp_id] at ht
  simp only [powerError, Pair.pullback, CategoryTheory.Iso.trans_hom,
    CategoryTheory.Iso.trans_inv, CategoryTheory.Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  rw [ht]
  simp only [CategoryTheory.Iso.symm_inv, Category.assoc]

/-- Precomposing by an original scalar changes the error by its actual nth power. -/
theorem powerError_scalar_precomp (P Q : Pair L n) (e : P.bundle.val ≅ Q.bundle.val)
    (a : Γ(X, ⊤)ˣ) :
    powerError P Q (ScalarAutomorphisms.scalarIso X P.bundle.val a ≪≫ e) =
      ScalarAutomorphisms.scalarIso X L.val (a ^ n) ≪≫ powerError P Q e := by
  apply CategoryTheory.Iso.ext
  simp only [powerError, UnitPower.powerIso_trans, ScalarAutomorphisms.powerIso_scalar,
    CategoryTheory.Iso.trans_hom, CategoryTheory.Iso.symm_hom, Category.assoc]
  change P.powerIso.inv ≫
      TrivializedPower.scalarMap X (tensorPowerLineBundle X P.bundle n).val
        ((a ^ n : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) ≫
      (TrivializedPower.powerIso X e n).hom ≫ Q.powerIso.hom =
    TrivializedPower.scalarMap X L.val ((a ^ n : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) ≫
      P.powerIso.inv ≫ (TrivializedPower.powerIso X e n).hom ≫ Q.powerIso.hom
  exact (ScalarAutomorphisms.scalarMap_naturality_assoc X
    ((a ^ n : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) P.powerIso.inv
    ((TrivializedPower.powerIso X e n).hom ≫ Q.powerIso.hom)).symm

end AlgebraicGeometry.Scheme.Modules.Invertible.Root
