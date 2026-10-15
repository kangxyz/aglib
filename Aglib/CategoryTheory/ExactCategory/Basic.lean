/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.MorphismProperty.Limits
/-!
# Exact structures and their admissible maps

An exact structure is a specified isomorphism-closed class of kernel–cokernel pairs
in an additive category, with the usual identity, composition, pushout, and pullback
axioms. No ambient abelian category, balancedness, or arbitrary pullbacks are assumed.
The formulation uses the equivalent axioms [E0], [E0op], [E1], [E1op], [E2], [E2op]
of Bühler, *Exact Categories*, Definition 2.1.
-/
@[expose] public section


universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory

variable (C : Type u) [Category.{v} C] [Preadditive C]

namespace Conflations

/-- The first maps in a specified class of short complexes. -/
def inflation (conflation : ShortComplex C → Prop) : MorphismProperty C :=
  fun _X Y i => ∃ (Z : C) (p : Y ⟶ Z) (h : i ≫ p = 0),
    conflation (ShortComplex.mk i p h)

/-- The second maps in a specified class of short complexes. -/
def deflation (conflation : ShortComplex C → Prop) : MorphismProperty C :=
  fun Y _Z p => ∃ (X : C) (i : X ⟶ Y) (h : i ≫ p = 0),
    conflation (ShortComplex.mk i p h)

end Conflations

/-- A Quillen exact structure on an additive category.

The fields are defining exact-category axioms, not assumed conclusions about the
Q-construction. In particular its category laws and mixed base-change property
are not fields of this structure. -/
structure ExactStructure [HasFiniteBiproducts C] where
  /-- The selected kernel–cokernel pairs. -/
  conflation : ShortComplex C → Prop
  /-- A conflation's first map has the actual kernel universal property. -/
  kernel : ∀ S, conflation S → IsLimit (KernelFork.ofι S.f S.zero)
  /-- A conflation's second map has the actual cokernel universal property. -/
  cokernel : ∀ S, conflation S → IsColimit (CokernelCofork.ofπ S.g S.zero)
  /-- Closure under isomorphism of short complexes. -/
  iso_closed : ∀ {S T}, (S ≅ T) → conflation S → conflation T
  /-- [E0]. -/
  inflation_id : ∀ X, Conflations.inflation C conflation (𝟙 X)
  /-- [E0op]. -/
  deflation_id : ∀ X, Conflations.deflation C conflation (𝟙 X)
  /-- [E1]. -/
  inflation_comp : ∀ {X Y Z} (i : X ⟶ Y) (j : Y ⟶ Z),
    Conflations.inflation C conflation i → Conflations.inflation C conflation j →
      Conflations.inflation C conflation (i ≫ j)
  /-- [E1op]. -/
  deflation_comp : ∀ {X Y Z} (p : X ⟶ Y) (q : Y ⟶ Z),
    Conflations.deflation C conflation p → Conflations.deflation C conflation q →
      Conflations.deflation C conflation (p ≫ q)
  /-- Existence part of [E2]: only pushouts along admissible monomorphisms. -/
  inflation_hasPushouts : (Conflations.inflation C conflation).HasPushouts
  /-- Stability part of [E2]. -/
  inflation_cobaseChange : (Conflations.inflation C conflation).IsStableUnderCobaseChange
  /-- Existence part of [E2op]: only pullbacks along admissible epimorphisms. -/
  deflation_hasPullbacks : (Conflations.deflation C conflation).HasPullbacks
  /-- Stability part of [E2op]. -/
  deflation_baseChange : (Conflations.deflation C conflation).IsStableUnderBaseChange

namespace ExactStructure

variable {C} [HasFiniteBiproducts C] (E : ExactStructure C)

/-- Admissible monomorphisms for this exact structure. -/
abbrev inflation : MorphismProperty C := Conflations.inflation C E.conflation

/-- Admissible epimorphisms for this exact structure. -/
abbrev deflation : MorphismProperty C := Conflations.deflation C E.conflation

instance inflation_containsIdentities : E.inflation.ContainsIdentities :=
  ⟨E.inflation_id⟩

instance deflation_containsIdentities : E.deflation.ContainsIdentities :=
  ⟨E.deflation_id⟩

instance inflation_isStableUnderComposition : E.inflation.IsStableUnderComposition :=
  ⟨E.inflation_comp⟩

instance deflation_isStableUnderComposition : E.deflation.IsStableUnderComposition :=
  ⟨E.deflation_comp⟩

instance inflation_hasPushouts_inst : E.inflation.HasPushouts := E.inflation_hasPushouts

instance inflation_isStableUnderCobaseChange : E.inflation.IsStableUnderCobaseChange :=
  E.inflation_cobaseChange

instance deflation_hasPullbacks_inst : E.deflation.HasPullbacks := E.deflation_hasPullbacks

instance deflation_isStableUnderBaseChange : E.deflation.IsStableUnderBaseChange :=
  E.deflation_baseChange

lemma inflation_of_conflation {S : ShortComplex C} (h : E.conflation S) : E.inflation S.f :=
  ⟨S.X₃, S.g, S.zero, h⟩

lemma deflation_of_conflation {S : ShortComplex C} (h : E.conflation S) : E.deflation S.g :=
  ⟨S.X₁, S.f, S.zero, h⟩

/-- Admissibility really implies the ordinary categorical mono property. -/
lemma mono_of_inflation {X Y : C} {i : X ⟶ Y} (hi : E.inflation i) : Mono i := by
  obtain ⟨Z, p, h, hs⟩ := hi
  exact Fork.IsLimit.mono (E.kernel (ShortComplex.mk i p h) hs)

/-- Admissibility really implies the ordinary categorical epi property. -/
lemma epi_of_deflation {X Y : C} {p : X ⟶ Y} (hp : E.deflation p) : Epi p := by
  obtain ⟨Z, i, h, hs⟩ := hp
  exact Cofork.IsColimit.epi (E.cokernel (ShortComplex.mk i p h) hs)

/-- Any kernel of an admissible epimorphism is admissible. The proof transports
its defining conflation through the unique isomorphism between kernels. -/
lemma inflation_of_isKernel {X Y Z : C} {i : X ⟶ Y} {p : Y ⟶ Z}
    (h : i ≫ p = 0) (hi : IsLimit (KernelFork.ofι i h))
    (hp : E.deflation p) : E.inflation i := by
  obtain ⟨X', i', h', hs⟩ := hp
  let hi' := E.kernel (ShortComplex.mk i' p h') hs
  let e : X' ≅ X := hi'.conePointUniqueUpToIso hi
  have he : e.hom ≫ i = i' :=
    hi'.conePointUniqueUpToIso_hom_comp hi WalkingParallelPair.zero
  let se : ShortComplex.mk i' p h' ≅ ShortComplex.mk i p h :=
    ShortComplex.isoMk e (Iso.refl _) (Iso.refl _) (by simpa using he) (by simp)
  exact ⟨Z, p, h, E.iso_closed se hs⟩

/-- Any cokernel of an admissible monomorphism is admissible. -/
lemma deflation_of_isCokernel {X Y Z : C} {i : X ⟶ Y} {p : Y ⟶ Z}
    (h : i ≫ p = 0) (hp : IsColimit (CokernelCofork.ofπ p h))
    (hi : E.inflation i) : E.deflation p := by
  obtain ⟨Z', p', h', hs⟩ := hi
  let hp' := E.cokernel (ShortComplex.mk i p' h') hs
  let e : Z' ≅ Z := hp'.coconePointUniqueUpToIso hp
  have he : p' ≫ e.hom = p :=
    hp'.comp_coconePointUniqueUpToIso_hom hp WalkingParallelPair.one
  let se : ShortComplex.mk i p' h' ≅ ShortComplex.mk i p h :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e (by simp) (by simpa using he.symm)
  exact ⟨X, i, h, E.iso_closed se hs⟩

open ZeroObject in
/-- The unique map from the original category's zero object is admissible. -/
lemma inflation_zero (X : C) : E.inflation (0 : 0 ⟶ X) :=
  E.inflation_of_isKernel (by simp) (kernel.isLimitConeZeroCone (𝟙 X))
    (E.deflation_id X)

open ZeroObject in
/-- The unique map to the original category's zero object is admissible. -/
lemma deflation_zero (X : C) : E.deflation (0 : X ⟶ 0) :=
  E.deflation_of_isCokernel (by simp) (cokernel.isColimitCoconeZeroCocone (𝟙 X))
    (E.inflation_id X)

/-- Pulling an admissible monomorphism back along an admissible epimorphism
preserves admissibility. This is derived from the exact-category axioms, rather
than included as an extra assumption (Bühler, Proposition 2.15). -/
lemma inflation_of_isPullback {A B P T : C}
    {i : A ⟶ T} {p : B ⟶ T} {a : P ⟶ A} {b : P ⟶ B}
    (sq : IsPullback a b i p) (hi : E.inflation i) (hp : E.deflation p) :
    E.inflation b := by
  obtain ⟨Z, q, hq, hs⟩ := hi
  let hk := E.kernel (ShortComplex.mk i q hq) hs
  let : Mono i := Fork.IsLimit.mono hk
  have hqp : E.deflation (p ≫ q) := E.deflation_comp p q hp (E.deflation_of_conflation hs)
  have hb : b ≫ (p ≫ q) = 0 := by
    rw [← Category.assoc, ← sq.w, Category.assoc, hq, comp_zero]
  apply E.inflation_of_isKernel hb _ hqp
  refine KernelFork.IsLimit.ofι b hb
    (fun {W} g hg => sq.lift (hk.lift (KernelFork.ofι (g ≫ p) (by
      simpa only [Category.assoc] using hg))) g (by
        simpa using hk.fac (KernelFork.ofι (g ≫ p) (by
          simpa only [Category.assoc] using hg)) WalkingParallelPair.zero))
    (fun g hg => by apply IsPullback.lift_snd)
    (fun g hg m hm => ?_)
  apply sq.hom_ext
  · apply (cancel_mono i).1
    rw [Category.assoc, sq.w, ← Category.assoc, hm]
    simp only [IsPullback.lift_fst]
    symm
    simpa using hk.fac (KernelFork.ofι (g ≫ p) (by
      simpa only [Category.assoc] using hg)) WalkingParallelPair.zero
  · simpa only [IsPullback.lift_snd] using hm

/-- The mixed base-change instance needed for restricted span composition. -/
instance inflation_isStableUnderBaseChangeAgainst_deflation :
    E.inflation.IsStableUnderBaseChangeAgainst E.deflation where
  isStableUnderBaseChangeAlong {_ _} _p hp :=
    ⟨fun {_ _ _ _ _} sq hi => E.inflation_of_isPullback sq hi hp⟩

end ExactStructure

end CategoryTheory.ExactCategory
