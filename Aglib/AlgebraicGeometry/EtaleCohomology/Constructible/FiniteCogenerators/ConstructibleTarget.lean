/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.Constructible
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ConstructibleNoetherian
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.General
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Closure
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-! # Constructible targets and cokernels of the original finite cogenerators

Each original finite constant direct-image factor is constructible on a
Noetherian base. The original finite product is identified with the native
finite biproduct colimit. The cokernel of the original embedding is therefore
constructible by the original weak cokernel closure. This is an actual
cogenerator step inside constructible coefficients, not a higher-image
induction or an assertion of arbitrary-subobject closure.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators

universe u v

attribute [local instance] hasSheafifyLarge

/-- A literal finite product of original constructible abelian coefficients
is constructible, using the native biproduct colimit and product comparison. -/
theorem isConstructible_finiteProduct
    {X : Scheme.{u}} {I : Type v} [Finite I]
    (E : I → AbelianSheaf.{u, u + 1} X) (hE : ∀ i, IsConstructible (E i)) :
    IsConstructible (∏ᶜ E) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have : HasFiniteBiproducts (AbelianSheaf.{u, u + 1} X) := Abelian.hasFiniteBiproducts
  have hsum : IsConstructible (⨁ E) :=
    FiniteColimits.isConstructible_of_isColimit (Discrete.functor E)
      (biproduct.isColimit E) (fun i => hE i.as)
  exact (isConstructible_iff_of_iso (biproduct.isoProduct E)).mp hsum

/-- The literal target of the given original finite constant-product
embedding is constructible on a Noetherian base. -/
theorem FiniteConstantProductEmbedding.isConstructible_target
    {X : Scheme.{u}} [IsNoetherian X] {F : AbelianSheaf.{u, u + 1} X}
    (t : FiniteConstantProductEmbedding F) :
    IsConstructible (∏ᶜ fun i => (directImage (t.morphism i)).obj
      (ConstantFinite.coefficient (t.value i) (t.source i))) := by
  apply isConstructible_finiteProduct
  intro i
  exact Finite.isConstructible_directImage_of_isNoetherian (t.morphism i)
    (isConstructible_constant (t.source i) (ConstantFinite.value (t.value i)))

/-- The cokernel of the same original embedding is constructible; neither
its source nor target is replaced by a new coefficient model. -/
theorem FiniteConstantProductEmbedding.isConstructible_cokernel
    {X : Scheme.{u}} [IsNoetherian X] {F : AbelianSheaf.{u, u + 1} X}
    (t : FiniteConstantProductEmbedding F) (hF : IsConstructible F) :
    IsConstructible (cokernel t.map) :=
  Constructible.isConstructible_cokernel t.map hF t.isConstructible_target

/-- The actual no-FP-input global cogenerator produces a constructible target
and a constructible cokernel for every original constructible coefficient. -/
theorem finiteConstantProductEmbeddingOfConstructible_cokernel
    {X : Scheme.{u}} [IsNoetherian X] (F : AbelianSheaf.{u, u + 1} X)
    (hF : IsConstructible F) :
    IsConstructible (cokernel (Global.finiteConstantProductEmbeddingOfConstructible X F hF).map) :=
  (Global.finiteConstantProductEmbeddingOfConstructible X F hF).isConstructible_cokernel hF

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators
