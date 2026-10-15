/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
/-!
# Exact inclusion of an abelian full subcategory

An object property containing zero and closed under subobjects, quotients, and
finite products gives an actual abelian full subcategory. The inclusion creates
kernels and cokernels, preserves finite limits and colimits, and is exact for
the standard abelian exact structures. No extension-closure premise is added.
-/
@[expose] public section


noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ExactCategory
open scoped ZeroObject

namespace CategoryTheory.ObjectProperty

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)

/-- Under subobject closure, the usual nonemptiness requirement is equivalent
to containing a zero object. -/
theorem containsZero_iff_nonempty [P.IsClosedUnderSubobjects] :
    P.ContainsZero ↔ P.Nonempty := by
  constructor
  · intro h
    let := h
    infer_instance
  · intro h
    let := h
    exact ⟨⟨0, isZero_zero C,
      P.prop_of_mono (0 : (0 : C) ⟶ P.arbitrary) P.prop_arbitrary⟩⟩

variable [P.ContainsZero] [P.IsClosedUnderSubobjects] [P.IsClosedUnderQuotients]
  [P.IsClosedUnderFiniteProducts]

/-- The full subcategory selected by the object property. -/
abbrev Subcategory := P.FullSubcategory

/-- The abelian structure is constructed from the closure hypotheses, rather
than supplied as extra data. -/
@[instance_reducible]
def subcategoryAbelian : Abelian (Subcategory P) := inferInstance

/-- The standard exact structure on the full abelian subcategory. -/
def subcategoryExactStructure : ExactCategory.ExactStructure (Subcategory P) :=
  ExactCategory.abelianExactStructure (Subcategory P)

/-- The full-subcategory inclusion preserves finite limits because it creates
kernels. -/
theorem inclusion_preservesFiniteLimits : PreservesFiniteLimits P.ι := by
  let : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) P.ι := fun f => P.preservesKernels_ι f
  exact Functor.preservesFiniteLimits_of_preservesKernels P.ι

/-- The full-subcategory inclusion preserves finite colimits because it creates
cokernels. -/
theorem inclusion_preservesFiniteColimits : PreservesFiniteColimits P.ι := by
  let : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) P.ι := fun f => P.preservesCokernels_ι f
  exact Functor.preservesFiniteColimits_of_preservesCokernels P.ι

/-- The actual inclusion is exact for the standard abelian exact structures. -/
def exactInclusion :
    ExactCategory.ExactFunctor (subcategoryExactStructure P)
      (ExactCategory.abelianExactStructure C) where
  toFunctor := P.ι
  map_conflation S hS := by
    let := inclusion_preservesFiniteLimits P
    let := inclusion_preservesFiniteColimits P
    exact hS.map_of_exact P.ι

/-- The exact inclusion remains the ordinary fully faithful inclusion on its
underlying category. -/
def inclusionFullyFaithful : (exactInclusion P).toFunctor.FullyFaithful :=
  P.fullyFaithfulι

end CategoryTheory.ObjectProperty
