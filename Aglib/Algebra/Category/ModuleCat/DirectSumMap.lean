/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# Direct-sum descent for bundled module coefficients
-/

@[expose] public section

noncomputable section

universe u v w a b

open CategoryTheory CategoryTheory.Limits DirectSum

namespace ModuleCat

variable {R : Type u} [Ring R] {ι : Type v}

/-- The direct-sum descent map, using the native bundled module instances. -/
def directSumDesc (M : ι → ModuleCat.{w} R) (N : ModuleCat.{w} R)
    (f : ∀ i, M i ⟶ N) : (⨁ i, M i) →ₗ[R] N := by
  classical
  exact DirectSum.toModule R ι N (fun i => (f i).hom)

/-- Bundled direct-sum descent restricts to the specified coefficient map. -/
theorem directSumDesc_lof [d : DecidableEq ι] (M : ι → ModuleCat.{w} R)
    (N : ModuleCat.{w} R) (f : ∀ i, M i ⟶ N) (i : ι) (x : M i) :
    directSumDesc M N f (DirectSum.lof R ι _ i x) = f i x := by
  have hd : d = Classical.decEq ι := Subsingleton.elim _ _
  subst d
  classical
  exact DirectSum.toModule_lof R (φ := fun i => (f i).hom) i x

variable {C : Type a} [Category.{b} C]

/-- The canonical direct-sum comparison for any module-valued functor. -/
def functorCoproductMap (F : C ⥤ ModuleCat.{w} R) (M : ι → C) [HasCoproduct M] :
    (⨁ i, F.obj (M i)) →ₗ[R] F.obj (∐ M) :=
  directSumDesc (fun i => F.obj (M i)) (F.obj (∐ M)) (fun i => F.map (Sigma.ι M i))

/-- The abstract comparison is induced by the actual coproduct inclusions. -/
theorem functorCoproductMap_lof [DecidableEq ι] (F : C ⥤ ModuleCat.{w} R)
    (M : ι → C) [HasCoproduct M] (i : ι) (x : F.obj (M i)) :
    functorCoproductMap F M (DirectSum.lof R ι _ i x) = F.map (Sigma.ι M i) x :=
  directSumDesc_lof (fun i => F.obj (M i)) (F.obj (∐ M))
    (fun i => F.map (Sigma.ι M i)) i x

end ModuleCat
