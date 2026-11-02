/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.RingTheory.Kaehler.TensorProduct


/-!
# Algebra / Category / ModuleCat / Differentials / BaseChange

Source: `IntegralTrace/AffineDifferentialArrow.lean`.
Incoming SHA256: `8daf9e33570b16efa9957574da7ee494b42a3b082bf7325496b0778840cb9c01`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory TensorProduct

universe u

namespace CommRingCat.KaehlerDifferential

variable {Λ A B : CommRingCat.{u}} (α : Λ ⟶ A) (σ : A ⟶ B)

/-- Native scalar extension of the original ring differential map. -/
def affineDifferentialLinearMap :
    (ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α) ⟶
      CommRingCat.KaehlerDifferential (α ≫ σ) := by
  letI := α.hom.toAlgebra
  letI := σ.hom.toAlgebra
  letI := (α ≫ σ).hom.toAlgebra
  letI : IsScalarTower Λ A B := IsScalarTower.of_algebraMap_eq' rfl
  exact ModuleCat.ofHom (X := B ⊗[A] _root_.KaehlerDifferential Λ A)
    (Y := _root_.KaehlerDifferential Λ B) (_root_.KaehlerDifferential.mapBaseChange Λ A B)
/-- The original positive differential formula, with the unchanged scalar maps. -/
theorem affineDifferentialLinearMap_tmul (b : B) (a : A) :
    letI := σ.hom.toAlgebra
    affineDifferentialLinearMap α σ
      (b ⊗ₜ[A] CommRingCat.KaehlerDifferential.d (f := α) a) =
        b • CommRingCat.KaehlerDifferential.d (f := α ≫ σ) (σ a) := by
  let := α.hom.toAlgebra
  let := σ.hom.toAlgebra
  let := (α ≫ σ).hom.toAlgebra
  let : IsScalarTower Λ A B := IsScalarTower.of_algebraMap_eq' rfl
  change _root_.KaehlerDifferential.mapBaseChange Λ A B
    (b ⊗ₜ[A] _root_.KaehlerDifferential.D Λ A a) = b • _root_.KaehlerDifferential.D Λ B (σ a)
  rw [_root_.KaehlerDifferential.mapBaseChange_tmul, _root_.KaehlerDifferential.map_D]
  rfl

end CommRingCat.KaehlerDifferential
