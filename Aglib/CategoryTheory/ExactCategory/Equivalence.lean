/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.CategoryTheory.ExactCategory.Isomorphisms
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
/-!
# Transport of exact structures through equivalences

The transported conflations are tested by the actual functor of an additive
categorical equivalence. All exact-category axioms are derived below.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  (E : ExactStructure D) (e : C ≌ D) [e.functor.Additive]

/-- Conflations pulled back along the forward equivalence. -/
def equivalenceConflation (S : ShortComplex C) : Prop := E.conflation (S.map e.functor)

omit [HasFiniteBiproducts C] in
lemma equivalenceConflation_inflation_iff {X Y : C} (i : X ⟶ Y) :
    Conflations.inflation C (E.equivalenceConflation e) i ↔ E.inflation (e.functor.map i) := by
  constructor
  · rintro ⟨Z, p, h, hs⟩
    exact E.inflation_of_conflation hs
  · rintro ⟨Z, p, h, hs⟩
    let p' : Y ⟶ e.inverse.obj Z := e.functor.preimage (p ≫ (e.counitIso.app Z).inv)
    have hp' : e.functor.map p' = p ≫ (e.counitIso.app Z).inv :=
      e.functor.map_preimage _
    have h' : i ≫ p' = 0 := by
      apply e.functor.map_injective
      simp only [Functor.map_comp, hp', ← Category.assoc, h, zero_comp, Functor.map_zero]
    refine ⟨e.inverse.obj Z, p', h', ?_⟩
    exact E.iso_closed (S := ShortComplex.mk (e.functor.map i) p h)
      (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (e.counitIso.app Z).symm
        (by simp) (by simpa using hp')) hs

omit [HasFiniteBiproducts C] in
lemma equivalenceConflation_deflation_iff {X Y : C} (p : X ⟶ Y) :
    Conflations.deflation C (E.equivalenceConflation e) p ↔ E.deflation (e.functor.map p) := by
  constructor
  · rintro ⟨Z, i, h, hs⟩
    exact E.deflation_of_conflation hs
  · rintro ⟨Z, i, h, hs⟩
    let i' : e.inverse.obj Z ⟶ X := e.functor.preimage ((e.counitIso.app Z).hom ≫ i)
    have hi' : e.functor.map i' = (e.counitIso.app Z).hom ≫ i :=
      e.functor.map_preimage _
    have h' : i' ≫ p = 0 := by
      apply e.functor.map_injective
      simp only [Functor.map_comp, hi', Category.assoc, h, comp_zero, Functor.map_zero]
    refine ⟨e.inverse.obj Z, i', h', ?_⟩
    exact E.iso_closed (S := ShortComplex.mk i (e.functor.map p) h)
      (ShortComplex.isoMk (e.counitIso.app Z).symm (Iso.refl _) (Iso.refl _)
        (by simp [hi']) (by simp)) hs

/-- The exact structure transported along an additive equivalence. -/
def ofEquivalence : ExactStructure C where
  conflation := E.equivalenceConflation e
  kernel S hS := isLimitOfReflects e.functor
    ((KernelFork.isLimitMapConeEquiv _ _).symm (E.kernel _ hS))
  cokernel S hS := isColimitOfReflects e.functor
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm (E.cokernel _ hS))
  iso_closed h hS := E.iso_closed (e.functor.mapShortComplex.mapIso h) hS
  inflation_id X := (E.equivalenceConflation_inflation_iff e _).2 (by
    simpa using E.inflation_id (e.functor.obj X))
  deflation_id X := (E.equivalenceConflation_deflation_iff e _).2 (by
    simpa using E.deflation_id (e.functor.obj X))
  inflation_comp i j hi hj := (E.equivalenceConflation_inflation_iff e _).2 (by
    simpa using E.inflation_comp _ _
      ((E.equivalenceConflation_inflation_iff e _).1 hi)
      ((E.equivalenceConflation_inflation_iff e _).1 hj))
  deflation_comp p q hp hq := (E.equivalenceConflation_deflation_iff e _).2 (by
    simpa using E.deflation_comp _ _
      ((E.equivalenceConflation_deflation_iff e _).1 hp)
      ((E.equivalenceConflation_deflation_iff e _).1 hq))
  inflation_hasPushouts := ⟨by
    intro X Y Z i f hi
    have : HasPushout (e.functor.map i) (e.functor.map f) :=
      E.inflation.hasPushout _ ((E.equivalenceConflation_inflation_iff e _).1 hi)
    have : HasColimit (span i f ⋙ e.functor) :=
      hasColimit_of_iso (spanCompIso e.functor i f)
    exact Adjunction.hasColimit_of_comp_equivalence (span i f) e.functor⟩
  inflation_cobaseChange := ⟨by
    intro A A' B B' f g f' g' sq hf
    apply (E.equivalenceConflation_inflation_iff e _).2
    exact E.inflation.of_isPushout (sq.map e.functor)
      ((E.equivalenceConflation_inflation_iff e _).1 hf)⟩
  deflation_hasPullbacks := ⟨by
    intro X Y Z p f hp
    have : HasPullback (e.functor.map p) (e.functor.map f) :=
      E.deflation.hasPullback _ ((E.equivalenceConflation_deflation_iff e _).1 hp)
    have : HasLimit (cospan p f ⋙ e.functor) :=
      hasLimit_of_iso (cospanCompIso e.functor p f).symm
    exact Adjunction.hasLimit_of_comp_equivalence (cospan p f) e.functor⟩
  deflation_baseChange := ⟨by
    intro X Y Y' S f g f' g' sq hg
    apply (E.equivalenceConflation_deflation_iff e _).2
    exact E.deflation.of_isPullback (sq.map e.functor)
      ((E.equivalenceConflation_deflation_iff e _).1 hg)⟩

@[simp]
lemma ofEquivalence_conflation (S : ShortComplex C) :
    (E.ofEquivalence e).conflation S ↔ E.conflation (S.map e.functor) := Iff.rfl

@[simp]
lemma ofEquivalence_inflation_iff {X Y : C} (i : X ⟶ Y) :
    (E.ofEquivalence e).inflation i ↔ E.inflation (e.functor.map i) :=
  E.equivalenceConflation_inflation_iff e i

@[simp]
lemma ofEquivalence_deflation_iff {X Y : C} (p : X ⟶ Y) :
    (E.ofEquivalence e).deflation p ↔ E.deflation (e.functor.map p) :=
  E.equivalenceConflation_deflation_iff e p

/-- The actual forward equivalence is exact for the transported structure. -/
def equivalenceExactFunctor : ExactFunctor (E.ofEquivalence e) E where
  toFunctor := e.functor
  map_conflation _ h := h

/-- Its genuine inverse is exact, by the counit natural isomorphism. -/
def equivalenceInverseExactFunctor : ExactFunctor E (E.ofEquivalence e) := by
  letI : e.inverse.Additive := e.inverse_additive
  exact
    { toFunctor := e.inverse
      map_conflation := fun S h => E.iso_closed (S.mapNatIso e.counitIso.symm) h }

end CategoryTheory.ExactCategory.ExactStructure
