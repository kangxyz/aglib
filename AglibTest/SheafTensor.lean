/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Basic

/-! Public tensor and braiding interfaces on a general site. Site, morphism and
coefficient universes remain independent; sheafification hypotheses are explicit. -/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
open SheafOfModulesOfCommRing

universe u v w
variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (R : Sheaf J CommRingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

example (M N : SheafOfModulesOfCommRing R) :
    ((tensorFunctor R).obj M).obj N ≅ ((tensorFunctor R).obj N).obj M := by
  simpa only [tensorFunctor_obj] using tensorBraiding R M N

example {M N P Q : SheafOfModulesOfCommRing R} (f : M ⟶ N) (g : P ⟶ Q) :
    (tensorLeftFunctor R M).map g ≫ ((tensorFunctor R).map f).app Q =
      ((tensorFunctor R).map f).app P ≫ (tensorLeftFunctor R N).map g :=
  tensorFunctor_naturality R f g
