/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.NatIso

/-!
# Original injective tests and faithful-adjunction retracts

The original adjunct of an injective presentation and its injective splitting
produce the coefficient retract. Native natural-transformation arrow retracts
then transport the same component isomorphism. The formal composition/descent
tests keep their actual comparison isomorphisms and proved pasting step.
No injectivity after a coefficient-forgetting functor is inferred here.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Adjunction

universe c h d k a b

section OriginalInjectiveRetracts

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

end OriginalInjectiveRetracts

section OriginalInjectiveTests

variable {M N C D E E' : Type*}
  [Category* M] [Category* N] [Category* C] [Category* D] [Category* E] [Category* E']
  (V : M ⥤ N) (a : M ⥤ C) (b : N ⥤ D) (R : C ⥤ D)
  {U W : D ⥤ E} (β : U ⟶ W)
  {L L' : C ⥤ E'} (γ : L ⟶ L') {T T' : C ⥤ E} (δ : T ⟶ T')

theorem injectiveTest_comp [V.PreservesInjectiveObjects]
    (e : ∀ (J : M) [Injective J], R.obj (a.obj J) ≅ b.obj (V.obj J))
    (hpaste : ∀ K : C, IsIso (β.app (R.obj K)) → IsIso (γ.app K) → IsIso (δ.app K))
    (hOuter : ∀ (I : N) [Injective I], IsIso (β.app (b.obj I)))
    (hInner : ∀ (J : M) [Injective J], IsIso (γ.app (a.obj J)))
    (J : M) [Injective J] : IsIso (δ.app (a.obj J)) := by
  have : Injective (V.obj J) := inferInstance
  have hR : IsIso (β.app (R.obj (a.obj J))) :=
    (NatTrans.isIso_app_iff_of_iso β (e J)).mpr (hOuter (V.obj J))
  exact hpaste (a.obj J) hR (hInner J)

theorem injectiveTest_descent
    (e : ∀ (J : M) [Injective J], R.obj (a.obj J) ≅ b.obj (V.obj J))
    (rtest : ∀ (I : N) [Injective I],
      ∃ J : M, Injective J ∧ Nonempty (Retract I (V.obj J)))
    (hcancel : ∀ K : C, IsIso (γ.app K) → IsIso (δ.app K) → IsIso (β.app (R.obj K)))
    (hInner : ∀ (J : M) [Injective J], IsIso (γ.app (a.obj J)))
    (hComposite : ∀ (J : M) [Injective J], IsIso (δ.app (a.obj J)))
    (I : N) [Injective I] : IsIso (β.app (b.obj I)) := by
  obtain ⟨J, hJ, ⟨r⟩⟩ := rtest I
  have : Injective J := hJ
  have hR : IsIso (β.app (R.obj (a.obj J))) :=
    hcancel (a.obj J) (hInner J) (hComposite J)
  let t : Retract (b.obj I) (R.obj (a.obj J)) :=
    (r.map b).trans (Retract.ofIso (e J).symm)
  exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms E)
    (β.retractArrowApp t) hR

end OriginalInjectiveTests

end CategoryTheory.Adjunction
