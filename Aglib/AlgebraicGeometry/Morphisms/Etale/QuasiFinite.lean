/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Etale morphisms are locally quasi-finite

The proof uses the native quasi-finiteness of finite-type formally unramified
algebras on the original affine section maps.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- An etale morphism is locally quasi-finite. -/
instance locallyQuasiFinite_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] :
    LocallyQuasiFinite f where
  quasiFinite_appLE {U} hU {V} hV e := by
    have h := f.etale_appLE hU hV e
    algebraize [(f.appLE _ _ e).hom]
    exact inferInstanceAs (Algebra.QuasiFinite Γ(Y, U) Γ(X, V))

end AlgebraicGeometry
