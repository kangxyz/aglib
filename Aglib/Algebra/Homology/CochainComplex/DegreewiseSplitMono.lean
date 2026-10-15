/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
/-! # Degreewise split monomorphisms of complexes -/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject

universe v u

namespace CategoryTheory.Limits.IsPushout

/-- Cobase change of a split monomorphism is split, with no additivity
hypothesis on the category. -/
theorem isSplitMono_inr {C : Type*} [Category* C]
    {A B D P : C} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ P} {j : D ⟶ P}
    [IsSplitMono i] (h : IsPushout i f g j) : IsSplitMono j := by
  exact IsSplitMono.mk' {
    retraction := h.desc (retraction i ≫ f) (𝟙 D) (by simp)
    id := h.inr_desc _ _ _ }

end CategoryTheory.Limits.IsPushout

namespace CochainComplex
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Termwise split monomorphisms, without requiring a chain retraction. -/
def degreewiseSplitMono : MorphismProperty (CochainComplex A ℤ) :=
  fun _ _ f ↦ ∀ n : ℤ, IsSplitMono (f.f n)

instance degreewiseSplitMono_multiplicative :
    (degreewiseSplitMono (A := A)).IsMultiplicative where
  id_mem _ _ := by dsimp; infer_instance
  comp_mem f g hf hg n := by
    let : IsSplitMono (f.f n) := hf n
    let : IsSplitMono (g.f n) := hg n
    change IsSplitMono (f.f n ≫ g.f n)
    infer_instance

/-- A degreewise split monomorphism is an ambient monomorphism. -/
theorem degreewiseSplitMono_mono {K L : CochainComplex A ℤ} {f : K ⟶ L}
    (hf : degreewiseSplitMono f) : Mono f :=
  mono_of_mono_f f (fun n ↦ by let := hf n; infer_instance)

/-- Chain isomorphisms are split in every degree. -/
theorem degreewiseSplitMono_of_isIso {K L : CochainComplex A ℤ} (f : K ⟶ L)
    [IsIso f] : degreewiseSplitMono f := by
  intro n
  infer_instance

/-- Every arrow from a zero complex is degreewise split. -/
theorem degreewiseSplitMono_of_isZero {K L : CochainComplex A ℤ} (hK : IsZero K)
    (f : K ⟶ L) : degreewiseSplitMono f := by
  intro n
  have hn := (eval A (ComplexShape.up ℤ) n).map_isZero hK
  exact IsSplitMono.mk' ⟨hn.from_ _, hn.eq_of_src _ _⟩

/-- Degreewise split monomorphisms are stable under arbitrary pushout. -/
theorem degreewiseSplitMono_pushout
    {B D E P : CochainComplex A ℤ}
    {i : B ⟶ D} {f : B ⟶ E} {g : D ⟶ P} {j : E ⟶ P}
    (hi : degreewiseSplitMono i) (h : IsPushout i f g j) : degreewiseSplitMono j := by
  intro n
  let : IsSplitMono ((eval A (ComplexShape.up ℤ) n).map i) := hi n
  exact CategoryTheory.Limits.IsPushout.isSplitMono_inr (h.map (eval A (ComplexShape.up ℤ) n))


end CochainComplex
