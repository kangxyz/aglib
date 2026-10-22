/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineQuotientReduction
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Naturality
public import Aglib.RingTheory.AdicCompletion.CompatibleSystemQuotient

/-! # Native compatible systems of original affine global sections -/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {K : (Spec B).IdealSheafData} (F : AdicSystem (Spec B) K)

/-- The original diagram of global sections, with its native B-linear maps. -/
abbrev affineSectionsTower : ℕᵒᵖ ⥤ ModuleCat B := F.obj ⋙ moduleSpecΓFunctor

/-- Every original global-section coefficient is finite over B. -/
theorem affineSectionsTower_finite (n : ℕ) :
    Module.Finite B (F.affineSectionsTower.obj (op n)) :=
  ((QuasiCoherent.affineLocallyFiniteType_spec_iff B _).mp (F.property.coherent n)).2

/-- The entire reduction comparison retains its original transition proof. -/
def affineSectionsReductionComparison {n m : ℕ} (h : n ≤ m) :
    {c : (F.affineSectionsTower.obj (op m) ⧸
        (affineIdeal B K ^ n •
          (⊤ : Submodule B (F.affineSectionsTower.obj (op m))))) ≃ₗ[B]
            F.affineSectionsTower.obj (op n) //
      ∀ x, c (Submodule.Quotient.mk x) =
        F.affineSectionsTower.map (homOfLE h).op x} := by
  let M := F.obj.obj (op m)
  letI : M.IsQuasicoherent :=
    ((QuasiCoherent.affineLocallyFiniteType_spec_iff B M).mp (F.property.coherent m)).1
  exact affineQuotientReductionCoordinates B K M (F.obj.obj (op n)) n
    (F.reductionIsoOfLE h) (F.obj.map (homOfLE h).op) (F.unit_reductionIsoOfLE_hom h)

/-- All-order quotient coordinates for the actual global-section diagram. -/
def affineSectionsReductionEquiv {n m : ℕ} (h : n ≤ m) :
    (F.affineSectionsTower.obj (op m) ⧸
      (affineIdeal B K ^ n •
        (⊤ : Submodule B (F.affineSectionsTower.obj (op m))))) ≃ₗ[B]
          F.affineSectionsTower.obj (op n) :=
  (F.affineSectionsReductionComparison h).val

theorem affineSectionsReductionEquiv_mk {n m : ℕ} (h : n ≤ m)
    (x : F.affineSectionsTower.obj (op m)) :
    F.affineSectionsReductionEquiv h (Submodule.Quotient.mk x) =
      F.affineSectionsTower.map (homOfLE h).op x :=
  (F.affineSectionsReductionComparison h).property x

/-- An actual coherent adic system on an affine gives a native compatible
finite system, without a separate kernel/cartesian-system assumption. -/
theorem affineSections_isCompatibleSystem :
    AdicCompletion.IsCompatibleSystem (affineIdeal B K) F.affineSectionsTower :=
  AdicCompletion.isCompatibleSystem_of_originalQuotientEquiv (affineIdeal B K)
    F.affineSectionsTower F.affineSectionsTower_finite
    (fun h => F.affineSectionsReductionEquiv h)
    (fun h x => F.affineSectionsReductionEquiv_mk h x)

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
