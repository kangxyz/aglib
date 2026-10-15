/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward

/-! Finite direct image retains the actual sheaf functor over arbitrary schemes.
These clients require finiteness of the morphism and no local Noetherianity. -/

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.QuasiCoherent

universe u

example {Z X : Scheme.{u}} (f : Z ⟶ X) [AlgebraicGeometry.IsFinite f] :
    finiteTypePushforward f ⋙ finiteTypeSheavesToModules X =
      finiteTypeSheavesToModules Z ⋙ Scheme.Modules.pushforward f :=
  finiteTypePushforward_comp_inclusion f

example {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.Finite) :
    finiteTypePushforwardSpec φ hφ ⋙ finiteTypeSheavesToModules (Spec R) =
      finiteTypeSheavesToModules (Spec S) ⋙ Scheme.Modules.pushforward (Spec.map φ) :=
  finiteTypePushforwardSpec_comp_inclusion φ hφ

example (X : Scheme.{u}) :
    finiteTypePushforward (𝟙 X) ≅ 𝟭 (FiniteTypeSheaves X) :=
  finiteTypePushforwardIdIso X
