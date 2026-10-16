/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Restriction

/-!
# Actual derived restriction on chain-endpoint Hom types

Restriction of native derived morphisms is expressed at the actual restricted
chain objects by the inverse source and forward target components of the
canonical factorization. Composition, chain-map images and restriction of
isomorphism/inverse components retain those exact maps. No perfectness or
boundedness is assumed.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/DerivedMorphisms.lean`.
Frozen dirty Quillen:
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `23964e63cdb44a65757340bc8ad3a8053d15161446d5d79167e813f98a069e75`.
Selected declaration ranges: 68–73, 77–81, 86–96.
Source: `Quillen/AlgebraicGeometry/PerfectComplexes/DerivedRightFractions.lean`.
Frozen dirty Quillen:
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `8495eeb20d93744604c24e4af532138b92860019829b9f0e54192c2a0aa4b213`.
Selected declaration ranges: 43–46, 49–51, 54–57, 60–64, 67–71.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Complex

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

variable {X : Scheme.{u}} {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Restriction of a derived morphism, expressed at the actual restricted
complexes using the localization factorization isomorphism. -/
def restrictDerivedHom {K L : CochainComplex X.Modules ℤ}
    (φ : (DerivedCategory.Q (C := X.Modules)).obj K ⟶ (DerivedCategory.Q (C := X.Modules)).obj L) :
    (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj K) ⟶
      (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj L) :=
  (derivedRestrictFactors j).inv.app K ≫ (derivedRestrict j).map φ ≫
    (derivedRestrictFactors j).hom.app L

@[simp]
theorem restrictDerivedHom_comp {K L M : CochainComplex X.Modules ℤ}
    (φ : (DerivedCategory.Q (C := X.Modules)).obj K ⟶ (DerivedCategory.Q (C := X.Modules)).obj L)
    (ψ : (DerivedCategory.Q (C := X.Modules)).obj L ⟶ (DerivedCategory.Q (C := X.Modules)).obj M) :
    restrictDerivedHom j (φ ≫ ψ) = restrictDerivedHom j φ ≫ restrictDerivedHom j ψ := by
  simp [restrictDerivedHom, Functor.map_comp, Category.assoc]

@[simp]
theorem restrictDerivedHom_map {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L) :
    restrictDerivedHom j ((DerivedCategory.Q (C := X.Modules)).map f) =
      (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map f) := by
  have h := (derivedRestrictFactors j).hom.naturality f
  change (derivedRestrict j).map ((DerivedCategory.Q (C := X.Modules)).map f) ≫
    (derivedRestrictFactors j).hom.app L =
      (derivedRestrictFactors j).hom.app K ≫ (DerivedCategory.Q (C := U.Modules)).map
        ((restrict j).map f) at h
  unfold restrictDerivedHom
  rw [h]
  simp

@[simp]
theorem restrictDerivedHom_id (K : CochainComplex X.Modules ℤ) :
    restrictDerivedHom j (𝟙 ((DerivedCategory.Q (C := X.Modules)).obj K)) =
      𝟙 ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj K)) := by
  simp [restrictDerivedHom]

@[simp]
theorem restrictDerivedIso_hom {K L : CochainComplex X.Modules ℤ}
    (e : (DerivedCategory.Q (C := X.Modules)).obj K ≅ (DerivedCategory.Q (C := X.Modules)).obj L) :
    (restrictDerivedIso j e).hom = restrictDerivedHom j e.hom := rfl

@[simp]
theorem restrictDerivedIso_inv {K L : CochainComplex X.Modules ℤ}
    (e : (DerivedCategory.Q (C := X.Modules)).obj K ≅ (DerivedCategory.Q (C := X.Modules)).obj L) :
    (restrictDerivedIso j e).inv = restrictDerivedHom j e.inv := by
  simp [restrictDerivedIso, restrictDerivedHom, Category.assoc]

@[simp]
theorem restrictDerivedIso_asIso_map {K L : CochainComplex X.Modules ℤ} (s : K ⟶ L) [QuasiIso s] :
    restrictDerivedIso j (asIso ((DerivedCategory.Q (C := X.Modules)).map s)) =
      asIso ((DerivedCategory.Q (C := U.Modules)).map ((restrict j).map s)) := by
  apply Iso.ext
  exact restrictDerivedHom_map j s

@[simp]
theorem restrictDerivedHom_inv_map {K L : CochainComplex X.Modules ℤ} (s : K ⟶ L) [QuasiIso s] :
    restrictDerivedHom j (inv ((DerivedCategory.Q (C := X.Modules)).map s)) =
      inv ((DerivedCategory.Q (C := U.Modules)).map ((restrict j).map s)) := by
  simpa only [restrictDerivedIso_inv, asIso_inv] using
    congrArg Iso.inv (restrictDerivedIso_asIso_map j s)

end AlgebraicGeometry.Scheme.Modules.Complex
