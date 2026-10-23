/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.Retracts
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # Injective coefficient retracts along a faithful inverse image

Embed the actual inverse image in an injective object upstairs and take the
original adjoint map. Reflection of monomorphisms makes that map monic, and
injectivity downstairs supplies its retraction. Naturality then transports
invertibility of the original exchange. No assertion about injectivity after
forgetting module scalars is used.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

universe c h d k a b

/-- A faithful left adjoint with enough injectives in its target exhibits each
injective source object as a genuine retract of the right image of an injective. -/
theorem exists_injective_rightAdjoint_retract
    {C : Type c} [Category.{h} C] {D : Type d} [Category.{k} D]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    [L.Faithful] [EnoughInjectives D] (I : C) [Injective I] :
    ∃ J : D, Injective J ∧ Nonempty (Retract I (R.obj J)) := by
  obtain ⟨P⟩ := EnoughInjectives.presentation (L.obj I)
  let i : I ⟶ R.obj P.J := adj.homEquiv I P.J P.f
  have : Mono i := inferInstance
  let r : Retract I (R.obj P.J) :=
    { i := i
      r := Injective.factorThru (𝟙 I) i
      retract := Injective.comp_factorThru (𝟙 I) i }
  exact ⟨P.J, inferInstance, ⟨r⟩⟩

/-- An original natural transformation invertible on right images of target
injectives is invertible on source injectives, by the constructed coefficient retract. -/
theorem isIso_app_injective_of_rightAdjoint_injectives
    {C : Type c} [Category.{h} C] {D : Type d} [Category.{k} D]
    {E : Type a} [Category.{b} E]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    [L.Faithful] [EnoughInjectives D]
    {F G : C ⥤ E} (α : F ⟶ G)
    (hα : ∀ (J : D) [Injective J], IsIso (α.app (R.obj J)))
    (I : C) [Injective I] : IsIso (α.app I) := by
  obtain ⟨J, hJ, ⟨r⟩⟩ := exists_injective_rightAdjoint_retract L R adj I
  have : Injective J := hJ
  exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms _)
    (α.retractArrowApp r) (hα J)

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
