/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Linear

/-! Actual structural pullback linearity, with independent scalar universe. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u v

example {S : Type v} [CommRing S] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (α : S →+* Γ(Y, ⊤)) (β : S →+* Γ(X, ⊤)) (h : p.appTop.hom.comp α = β) :
    letI := moduleCategoryLinearOfHom X β
    letI := moduleCategoryLinearOfHom Y α
    (Scheme.Modules.pullback p).Linear S :=
  pullback_linearOfCompatibleHom p α β h

end
