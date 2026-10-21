/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.Scalars
public import Aglib.AlgebraicGeometry.Cohomology.Exact.Modules
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# The actual ideal-power quotient cohomology tower

The diagram uses the original sheaf quotients and original cohomology maps.
Its zero stage is included; no surjectivity of higher cohomology transitions is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable (X : Scheme.{u}) {A : Type u} [CommRing A]
variable (α : A →+* Γ(X, ⊤)) (F : X.Modules) (I : Ideal A)

/-- The inverse coefficient diagram of actual quotients, with degree zero included. -/
def idealPowerQuotientFunctor : ℕᵒᵖ ⥤ X.Modules where
  obj n := idealPowerQuotient X α F I n.unop
  map f := idealPowerQuotientMap X α F I (leOfHom f.unop)
  map_id n := idealQuotientMap_refl X α F (I ^ n.unop)
  map_comp _ _ := (idealQuotientMap_comp X α F _ _).symm

/-- The actual module-valued cohomology tower, with the specified structural action. -/
def idealPowerQuotientCohomology (p : ℕ) : ℕᵒᵖ ⥤ ModuleCat.{u + 1} A :=
  idealPowerQuotientFunctor X α F I ⋙ moduleCohomologyFunctorOfHom X α p

/-- The original reductions form a natural transformation from constant coefficients. -/
def idealPowerQuotientReduction : (Functor.const ℕᵒᵖ).obj F ⟶
    idealPowerQuotientFunctor X α F I where
  app n := idealQuotientπ X α F (I ^ n.unop)
  naturality m n f := by
    change 𝟙 F ≫ idealQuotientπ X α F (I ^ n.unop) =
      idealQuotientπ X α F (I ^ m.unop) ≫
        idealPowerQuotientMap X α F I (leOfHom f.unop)
    rw [Category.id_comp, idealQuotientπ_map]

/-- Cohomology of the original reductions, as a compatible family of linear maps. -/
def idealPowerQuotientCohomologyReduction (p : ℕ) :
    (Functor.const ℕᵒᵖ).obj ((moduleCohomologyFunctorOfHom X α p).obj F) ⟶
      idealPowerQuotientCohomology X α F I p where
  app n := (moduleCohomologyFunctorOfHom X α p).map (idealQuotientπ X α F (I ^ n.unop))
  naturality m n f := by
    change 𝟙 _ ≫ (moduleCohomologyFunctorOfHom X α p).map
        (idealQuotientπ X α F (I ^ n.unop)) =
      (moduleCohomologyFunctorOfHom X α p).map (idealQuotientπ X α F (I ^ m.unop)) ≫
        (moduleCohomologyFunctorOfHom X α p).map
          (idealPowerQuotientMap X α F I (leOfHom f.unop))
    rw [Category.id_comp, ← Functor.map_comp, idealQuotientπ_map]

/-- Naturality of the original connecting maps under an arbitrary power reduction. -/
theorem idealPowerQuotient_connecting_naturality {n m : ℕ} (h : n ≤ m) (p : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X (idealPowerQuotient X α F I m)) p) :
    moduleCohomologyConnectingOfHom X α (idealSequence X α F (I ^ n))
        (idealSequence_shortExact X α F (I ^ n)) p
        (moduleCohomologyMapOfHom X α (idealPowerQuotientMap X α F I h) p x) =
      moduleCohomologyMapOfHom X α (idealPowerMap X α F I h) (p + 1)
        (moduleCohomologyConnectingOfHom X α (idealSequence X α F (I ^ m))
          (idealSequence_shortExact X α F (I ^ m)) p x) :=
  moduleCohomologyConnectingOfHom_naturality X α
    (idealSequence_shortExact X α F (I ^ m))
    (idealSequence_shortExact X α F (I ^ n))
    (idealSequenceMap X α F (Ideal.pow_le_pow_right h)) p x

/-- Every element of `Iⁿ` annihilates original quotient cohomology in every degree. -/
theorem idealPowerQuotientCohomology_smul_eq_zero (n p : ℕ) (a : ↥(I ^ n))
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X (idealPowerQuotient X α F I n)) p) :
    letI := moduleCohomologyModuleOfHom X α (idealPowerQuotient X α F I n) p
    (a : A) • x = 0 := by
  rw [moduleCohomologyModuleOfHom_smul]
  have hscalar : moduleScalarOfGlobal X (idealPowerQuotient X α F I n) (α a) = 0 := by
    have he : (SheafOfModules.toSheaf X.ringCatSheaf).map
        (globalScalarEndomorphism X (idealPowerQuotient X α F I n) (α a)) =
        moduleScalarOfGlobal X (idealPowerQuotient X α F I n) (α a) := by
      ext V y
      exact globalScalarEndomorphism_app X _ _ V.unop y
    rw [← he, idealQuotient_scalar_eq_zero, Functor.map_zero]
  rw [hscalar]
  change (Sheaf.functorH _ p).map 0 x = 0
  rw [Functor.map_zero]
  rfl

end AlgebraicGeometry.Scheme.Cohomology
