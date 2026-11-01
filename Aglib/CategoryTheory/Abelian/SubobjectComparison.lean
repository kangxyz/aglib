/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Functor.EpiMono

/-! # Original coimages inside a specified subobject

The coimage of a composite through a monomorphism maps canonically into the
original intermediate object. The original cokernel descent supplies this
comparison, its factorization equations and its monomorphism property.
Epimorphy after a mono-preserving functor, or vanishing in the ambient
cokernel, detects when that same comparison is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.Abelian

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {P F G : C} (q : P ⟶ F) (f : F ⟶ G) [Mono f]

/-- The original coimage of a composite maps into the specified subobject. -/
def coimageSubobjectComparison : Abelian.coimage (q ≫ f) ⟶ F :=
  cokernel.desc (kernel.ι (q ≫ f)) q (by
    apply (cancel_mono f).mp
    simpa only [Category.assoc, zero_comp] using kernel.condition (q ≫ f))

/-- The comparison retains the original map from the source. -/
@[reassoc (attr := simp)]
theorem coimage_π_subobjectComparison :
    Abelian.coimage.π (q ≫ f) ≫ coimageSubobjectComparison q f = q :=
  cokernel.π_desc _ _ _

/-- The comparison followed by the original inclusion is the canonical
coimage inclusion of the composite. -/
@[reassoc (attr := simp)]
theorem coimageSubobjectComparison_comp :
    coimageSubobjectComparison q f ≫ f = Abelian.factorThruCoimage (q ≫ f) := by
  apply (cancel_epi (Abelian.coimage.π (q ≫ f))).mp
  simp

/-- The original comparison is a monomorphism, not merely isomorphic to one. -/
instance coimageSubobjectComparison_mono : Mono (coimageSubobjectComparison q f) := by
  have h : Mono (coimageSubobjectComparison q f ≫ f) := by
    rw [coimageSubobjectComparison_comp]
    infer_instance
  exact mono_of_mono (coimageSubobjectComparison q f) f

/-- Any mono-preserving functor under which the original source map becomes
epimorphic sends this same comparison to an isomorphism. -/
theorem isIso_map_coimageSubobjectComparison
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (L : C ⥤ D) [L.PreservesMonomorphisms] [Epi (L.map q)] :
    IsIso (L.map (coimageSubobjectComparison q f)) := by
  have : Epi (L.map (coimageSubobjectComparison q f)) :=
    epi_of_epi_fac (by
      rw [← L.map_comp, coimage_π_subobjectComparison] :
      L.map (Abelian.coimage.π (q ≫ f)) ≫
        L.map (coimageSubobjectComparison q f) = L.map q)
  exact isIso_of_mono_of_epi _

/-- Nested original subobjects agree when the larger inclusion vanishes
in the actual cokernel of the smaller inclusion. -/
theorem isIso_of_comp_cokernel_zero {H F G : C}
    (a : H ⟶ F) (f : F ⟶ G) [Mono a] [Mono f]
    (h : f ≫ cokernel.π (a ≫ f) = 0) : IsIso a := by
  let s : F ⟶ H := Abelian.monoLift (a ≫ f) f h
  have hs : s ≫ a = 𝟙 F := by
    apply (cancel_mono f).mp
    simpa only [Category.assoc, Category.id_comp] using
      (Abelian.monoLift_comp (a ≫ f) f h)
  refine ⟨⟨s, ?_, hs⟩⟩
  apply (cancel_mono a).mp
  simp only [Category.assoc, hs, Category.comp_id, Category.id_comp]

end CategoryTheory.Abelian
