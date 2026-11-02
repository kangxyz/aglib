/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Differentials.BaseChange
public import Aglib.RingTheory.Kaehler.Exterior.Map
public import Aglib.RingTheory.Kaehler.Exterior.Values
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.RingTheory.Kaehler.TensorProduct


/-!
# The original scalar-extended raw exterior map in affine module categories

The source is scalar extension of the original raw exterior module. The
literal original differential map and raw scalar-extension equivalence are
retained, together with the exact ordered-wedge formula.
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

universe u


open _root_.KaehlerDifferential

namespace CommRingCat.KaehlerDifferential

variable {Λ A B : CommRingCat.{u}} (α : Λ ⟶ A) (σ : A ⟶ B) (n : ℕ)

/-- The original raw exterior map, in the actual affine scalar-extension categories. -/
def affineRawLinearMap :
    (ModuleCat.extendScalars σ.hom).obj
      (ModuleCat.of A (⋀[A]^n (CommRingCat.KaehlerDifferential α))) ⟶
    ModuleCat.of B (⋀[B]^n (CommRingCat.KaehlerDifferential (α ≫ σ))) := by
  letI := α.hom.toAlgebra
  letI := σ.hom.toAlgebra
  letI := (α ≫ σ).hom.toAlgebra
  letI : IsScalarTower Λ A B := IsScalarTower.of_algebraMap_eq' rfl
  exact ModuleCat.ofHom (X := B ⊗[A] (⋀[A]^n (_root_.KaehlerDifferential Λ A)))
    (Y := ⋀[B]^n (_root_.KaehlerDifferential Λ B))
    (_root_.KaehlerDifferential.mapExteriorBaseChange Λ A B n)

/-- The actual raw arrow keeps every original coefficient and ordered vector,
using the same degree-one affine differential map. -/
theorem affineRawLinearMap_tmul_mk (s : B)
    (v : Fin n → CommRingCat.KaehlerDifferential α) :
    letI := σ.hom.toAlgebra
    affineRawLinearMap α σ n (s ⊗ₜ[A] exteriorPower.ιMulti A n v) =
      s • exteriorPower.ιMulti B n
        (fun i => affineDifferentialLinearMap α σ ((1 : B) ⊗ₜ[A] v i)) := by
  let := α.hom.toAlgebra
  let := σ.hom.toAlgebra
  let := (α ≫ σ).hom.toAlgebra
  let : IsScalarTower Λ A B := IsScalarTower.of_algebraMap_eq' rfl
  change _root_.KaehlerDifferential.mapExteriorBaseChange Λ A B n
    (s ⊗ₜ[A] exteriorPower.ιMulti A n v) =
      s • exteriorPower.ιMulti B n
        (fun i => _root_.KaehlerDifferential.mapBaseChange Λ A B ((1 : B) ⊗ₜ[A] v i))
  refine (_root_.KaehlerDifferential.mapExteriorBaseChange_tmul_mk Λ A B n s v).trans ?_
  congr 2
  funext i
  exact ((_root_.KaehlerDifferential.mapBaseChange_tmul Λ A B 1 (v i)).trans (one_smul B _)).symm

end CommRingCat.KaehlerDifferential
