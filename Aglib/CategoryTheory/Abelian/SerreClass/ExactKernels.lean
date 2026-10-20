/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.Abelian.SerreClass.Exact

/-!
# Kernels of actual exact functors and intersections of Serre classes, with all category and hom
universes retained.

Source: `lean/R5Lab/Aglib/CategoryTheory/Abelian/SerreClass/ExactKernels.lean`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `2bf8602bbfbda800cf35c02a69e9a9a4eba6c96ec6c6409a8b09563603e82f80`.
Native objects and canonical maps are reused; provenance does not select declaration namespaces.
-/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ExactCategory
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts
namespace CategoryTheory.ExactCategory.ExactFunctor
universe u v w z
variable {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
  [Abelian C] [Abelian D]
  (F : ExactFunctor (abelianExactStructure C) (abelianExactStructure D))

instance preservesFiniteLimits : PreservesFiniteLimits F.toFunctor := by
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).mpr
  intro S h
  exact ⟨(F.map_conflation S h).exact, (F.map_conflation S h).mono_f⟩

instance preservesFiniteColimits : PreservesFiniteColimits F.toFunctor := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).mpr
  intro S h
  exact ⟨(F.map_conflation S h).exact, (F.map_conflation S h).epi_g⟩

end CategoryTheory.ExactCategory.ExactFunctor

namespace CategoryTheory.ObjectProperty
universe u v w z

/-- The kernel of an actual abelian exact functor is a Serre class. -/
theorem exactKernelSerre {C : Type u} {D : Type v}
    [Category.{w} C] [Category.{z} D] [Abelian C] [Abelian D]
    (F : CategoryTheory.ExactCategory.ExactFunctor (abelianExactStructure C)
      (abelianExactStructure D)) : F.toFunctor.kernel.IsSerreClass := by
  infer_instance

/-- Arbitrary intersections preserve the defining Serre closure conditions. -/
theorem forallSerre {C : Type u} [Category.{w} C] [Abelian C] {I : Type v}
    (P : I → ObjectProperty C) [∀ i, (P i).IsSerreClass] :
    ObjectProperty.IsSerreClass (fun M => ∀ i, P i M) := {
  exists_zero := ⟨0, isZero_zero C, fun i => (P i).prop_zero⟩
  prop_of_mono f _ h i := (P i).prop_of_mono f (h i)
  prop_of_epi f _ h i := (P i).prop_of_epi f (h i)
  prop_X₂_of_shortExact h h₁ h₃ i := (P i).prop_X₂_of_shortExact h (h₁ i) (h₃ i) }

end CategoryTheory.ObjectProperty
