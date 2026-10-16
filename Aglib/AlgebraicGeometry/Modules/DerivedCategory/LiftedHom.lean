/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic

/-!
# Derived Hom transport through a supplied factorization

An actual functor between native derived categories, together with the
specified localization factorization for an actual complex functor, gives
Hom transport at the original chain endpoints. The inverse source and
forward target components are retained, as are composition and chain-map
equations. The functors are supplied; no additional existence or exactness
statement is asserted.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/DerivedRepresentativeNaturality.lean`.
Frozen dirty Quillen:
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `371fd87889a354c81f42b4fe21c57fa3e4046c84df2cf2b069b73ed02d181184`.
Selected declaration ranges: 45–49, 52–56, 59–67.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Complex

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

variable {X Y : Scheme.{u}} {R : CochainComplex X.Modules ℤ ⥤ CochainComplex Y.Modules ℤ}
    {F : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules}
      (e : DerivedCategory.Q (C := X.Modules) ⋙ F ≅ R ⋙ DerivedCategory.Q (C := Y.Modules))

/-- A derived functor expressed at the localized chain objects through its
specified factorization isomorphism. -/
def liftedDerivedHom {K L : CochainComplex X.Modules ℤ}
    (φ : (DerivedCategory.Q (C := X.Modules)).obj K ⟶ (DerivedCategory.Q (C := X.Modules)).obj L) :
    (DerivedCategory.Q (C := Y.Modules)).obj (R.obj K) ⟶ (DerivedCategory.Q (C := Y.Modules)).obj
      (R.obj L) :=
  e.inv.app K ≫ F.map φ ≫ e.hom.app L

@[simp]
theorem liftedDerivedHom_comp {K L M : CochainComplex X.Modules ℤ}
    (φ : (DerivedCategory.Q (C := X.Modules)).obj K ⟶ (DerivedCategory.Q (C := X.Modules)).obj L)
    (ψ : (DerivedCategory.Q (C := X.Modules)).obj L ⟶ (DerivedCategory.Q (C := X.Modules)).obj M) :
    liftedDerivedHom e (φ ≫ ψ) = liftedDerivedHom e φ ≫ liftedDerivedHom e ψ := by
  simp [liftedDerivedHom, Functor.map_comp, Category.assoc]

@[simp]
theorem liftedDerivedHom_map {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L) :
    liftedDerivedHom e ((DerivedCategory.Q (C := X.Modules)).map f) =
      (DerivedCategory.Q (C := Y.Modules)).map (R.map f) := by
  have h := e.hom.naturality f
  change F.map ((DerivedCategory.Q (C := X.Modules)).map f) ≫ e.hom.app L =
    e.hom.app K ≫ (DerivedCategory.Q (C := Y.Modules)).map (R.map f) at h
  unfold liftedDerivedHom
  rw [h]
  simp

end AlgebraicGeometry.Scheme.Modules.Complex
