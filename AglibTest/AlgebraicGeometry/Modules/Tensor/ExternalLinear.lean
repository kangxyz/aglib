/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.ExternalLinear

/-! Original external tensor linearity needs only compatible actual scalars. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u v

example {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    {R : Type v} [CommRing R]
    (α : R →+* Γ(X, ⊤)) (β : R →+* Γ((Limits.pullback f g : Scheme), ⊤))
    (h : (Limits.pullback.fst f g).appTop.hom.comp α = β) (N : Y.Modules) :
    letI := moduleCategoryLinearOfHom X α
    letI := moduleCategoryLinearOfHom (Limits.pullback f g) β
    ((externalTensor f g).flip.obj N).Linear R :=
  externalTensor_flip_obj_linearOfHom f g α β h N

example {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    {R : Type v} [CommRing R]
    (α : R →+* Γ(Y, ⊤)) (β : R →+* Γ((Limits.pullback f g : Scheme), ⊤))
    (h : (Limits.pullback.snd f g).appTop.hom.comp α = β)
    (M : X.Modules) {N N' : Y.Modules} (a : N ⟶ N') (r : R) :
    letI := moduleCategoryLinearOfHom Y α
    letI := moduleCategoryLinearOfHom (Limits.pullback f g) β
    ((externalTensor f g).obj M).map (r • a) =
      r • ((externalTensor f g).obj M).map a :=
  externalTensor_obj_map_smul f g α β h M a r
