/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.External
public import Aglib.AlgebraicGeometry.Modules.Tensor.Linear
public import Aglib.AlgebraicGeometry.Modules.Pullback.Linear

/-!
# Structural linearity of the original external tensor

Each partial external tensor is the original projection pullback followed by
original sheaf tensor. Compatibility of the specified structural ring maps
therefore makes it linear. The tensor symmetry proves the first-variable
case on the same category; no new tensor model or action is introduced.
No flatness, quasicoherence or geometric finiteness assumption is needed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Modules

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  {R : Type v} [CommRing R]

/-- The original second-variable external tensor is linear for compatible
actual scalars on the second factor and on the actual fibre product. -/
theorem externalTensor_obj_linearOfHom
    (α : R →+* Γ(Y, ⊤)) (β : R →+* Γ((Limits.pullback f g : Scheme), ⊤))
    (h : (Limits.pullback.snd f g).appTop.hom.comp α = β) (M : X.Modules) :
    letI := moduleCategoryLinearOfHom Y α
    letI := moduleCategoryLinearOfHom (Limits.pullback f g) β
    ((externalTensor f g).obj M).Linear R := by
  let := moduleCategoryLinearOfHom Y α
  let := moduleCategoryLinearOfHom (Limits.pullback f g) β
  let : (Scheme.Modules.pullback (Limits.pullback.snd f g)).Linear R :=
    pullback_linearOfCompatibleHom (Limits.pullback.snd f g) α β h
  change (Scheme.Modules.pullback (Limits.pullback.snd f g) ⋙
    moduleTensorLeftFunctor (Limits.pullback f g)
      ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj M)).Linear R
  infer_instance

/-- The original first-variable external tensor is linear for compatible
actual scalars, using the original tensor symmetry. -/
theorem externalTensor_flip_obj_linearOfHom
    (α : R →+* Γ(X, ⊤)) (β : R →+* Γ((Limits.pullback f g : Scheme), ⊤))
    (h : (Limits.pullback.fst f g).appTop.hom.comp α = β) (N : Y.Modules) :
    letI := moduleCategoryLinearOfHom X α
    letI := moduleCategoryLinearOfHom (Limits.pullback f g) β
    ((externalTensor f g).flip.obj N).Linear R := by
  let := moduleCategoryLinearOfHom X α
  let := moduleCategoryLinearOfHom (Limits.pullback f g) β
  let : (Scheme.Modules.pullback (Limits.pullback.fst f g)).Linear R :=
    pullback_linearOfCompatibleHom (Limits.pullback.fst f g) α β h
  let E := (Scheme.Modules.pullback (Limits.pullback.snd f g)).obj N
  let : (tensorLeft E).Linear R := moduleTensorLeftFunctor_linearOfHom
    (Limits.pullback f g) β E
  let : (tensorRight E).Linear R :=
    Functor.linear_of_iso R (BraidedCategory.tensorLeftIsoTensorRight E)
  change (Scheme.Modules.pullback (Limits.pullback.fst f g) ⋙ tensorRight E).Linear R
  infer_instance

/-- Whole second-variable morphism compatibility on the original bifunctor. -/
theorem externalTensor_obj_map_smul
    (α : R →+* Γ(Y, ⊤)) (β : R →+* Γ((Limits.pullback f g : Scheme), ⊤))
    (h : (Limits.pullback.snd f g).appTop.hom.comp α = β)
    (M : X.Modules) {N N' : Y.Modules} (a : N ⟶ N') (r : R) :
    letI := moduleCategoryLinearOfHom Y α
    letI := moduleCategoryLinearOfHom (Limits.pullback f g) β
    ((externalTensor f g).obj M).map (r • a) =
      r • ((externalTensor f g).obj M).map a := by
  let := moduleCategoryLinearOfHom Y α
  let := moduleCategoryLinearOfHom (Limits.pullback f g) β
  let := externalTensor_obj_linearOfHom f g α β h M
  exact Functor.map_smul _ r a

/-- Whole first-variable morphism compatibility on the original bifunctor. -/
theorem externalTensor_map_smul_app
    (α : R →+* Γ(X, ⊤)) (β : R →+* Γ((Limits.pullback f g : Scheme), ⊤))
    (h : (Limits.pullback.fst f g).appTop.hom.comp α = β)
    {M M' : X.Modules} (a : M ⟶ M') (N : Y.Modules) (r : R) :
    letI := moduleCategoryLinearOfHom X α
    letI := moduleCategoryLinearOfHom (Limits.pullback f g) β
    ((externalTensor f g).map (r • a)).app N =
      r • ((externalTensor f g).map a).app N := by
  let := moduleCategoryLinearOfHom X α
  let := moduleCategoryLinearOfHom (Limits.pullback f g) β
  let := externalTensor_flip_obj_linearOfHom f g α β h N
  exact Functor.map_smul ((externalTensor f g).flip.obj N) r a

end AlgebraicGeometry.Scheme.Modules
