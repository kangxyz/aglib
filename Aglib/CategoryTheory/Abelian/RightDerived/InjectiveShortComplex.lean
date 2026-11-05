/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Right-derived sequences of functors exact on injectives

A short complex of additive functors need only be short exact on injective
objects. Mapping one actual injective resolution gives its short exact
sequence of cochain complexes. Its homology sequence retains the original
`NatTrans.rightDerived` maps and the native connecting morphism. In particular,
this applies to relative source-cover sequences without acyclicity of an
intermediate open direct image or a derived composition assumption.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v u' v'

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (S : ShortComplex (C ⥤ D)) [S.X₁.Additive] [S.X₂.Additive] [S.X₃.Additive]

/-- Apply the three original functors and transformations to one resolution. -/
abbrev mapInjectiveResolution {X : C} (I : InjectiveResolution X) :
    ShortComplex (CochainComplex D ℕ) where
  X₁ := (S.X₁.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  X₂ := (S.X₂.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  X₃ := (S.X₃.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  f := (NatTrans.mapHomologicalComplex S.f (.up ℕ)).app I.cocomplex
  g := (NatTrans.mapHomologicalComplex S.g (.up ℕ)).app I.cocomplex
  zero := by
    ext n
    exact congrArg (fun a => a.app (I.cocomplex.X n)) S.zero

omit [EnoughInjectives C] in
/-- Exactness is required only on genuine injectives, not all coefficients. -/
theorem mapInjectiveResolution_shortExact
    (hS : ∀ (J : C) [Injective J],
      (S.map ((evaluation C D).obj J)).ShortExact)
    {X : C} (I : InjectiveResolution X) : (S.mapInjectiveResolution I).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact hS (I.cocomplex.X n)

variable {X : C} (I : InjectiveResolution X)

include I

/-- The existing normalization relates each original derived map to its cochain map. -/
@[reassoc]
theorem rightDerived_homologyMap_f (n : ℕ) :
    (NatTrans.rightDerived S.f n).app X ≫ (I.isoRightDerivedObj S.X₂ n).hom =
      (I.isoRightDerivedObj S.X₁ n).hom ≫
        HomologicalComplex.homologyMap (S.mapInjectiveResolution I).f n := by
  rw [I.rightDerived_app_eq S.f n]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- The second original transformation has the same native normalization. -/
@[reassoc]
theorem rightDerived_homologyMap_g (n : ℕ) :
    (NatTrans.rightDerived S.g n).app X ≫ (I.isoRightDerivedObj S.X₃ n).hom =
      (I.isoRightDerivedObj S.X₂ n).hom ≫
        HomologicalComplex.homologyMap (S.mapInjectiveResolution I).g n := by
  rw [I.rightDerived_app_eq S.g n]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- The unchanged natural-degree derived transformations form a complex. -/
theorem rightDerived_comp_eq_zero (n : ℕ) :
    (NatTrans.rightDerived S.f n).app X ≫ (NatTrans.rightDerived S.g n).app X = 0 := by
  apply (cancel_mono (I.isoRightDerivedObj S.X₃ n).hom).mp
  rw [Category.assoc, S.rightDerived_homologyMap_g I n,
    ← Category.assoc, S.rightDerived_homologyMap_f I n, Category.assoc,
    ← HomologicalComplex.homologyMap_comp, (S.mapInjectiveResolution I).zero,
    HomologicalComplex.homologyMap_zero,
    comp_zero, zero_comp]

variable (hS : ∀ (J : C) [Injective J],
  (S.map ((evaluation C D).obj J)).ShortExact)

include hS

/-- The boundary uses the native homology boundary and the original derived comparisons. -/
def rightDerivedBoundary (n : ℕ) :
    (S.X₃.rightDerived n).obj X ⟶ (S.X₁.rightDerived (n + 1)).obj X :=
  (I.isoRightDerivedObj S.X₃ n).hom ≫
    (S.mapInjectiveResolution_shortExact hS I).δ n (n + 1) rfl ≫
      (I.isoRightDerivedObj S.X₁ (n + 1)).inv

@[reassoc (attr := simp)]
theorem rightDerivedBoundary_comp (n : ℕ) :
    S.rightDerivedBoundary I hS n ≫ (NatTrans.rightDerived S.f (n + 1)).app X = 0 := by
  apply (cancel_mono (I.isoRightDerivedObj S.X₂ (n + 1)).hom).mp
  simp only [Category.assoc, rightDerivedBoundary,
    S.rightDerived_homologyMap_f I (n + 1), Iso.inv_hom_id_assoc, zero_comp]
  rw [(S.mapInjectiveResolution_shortExact hS I).δ_comp n (n + 1) rfl, comp_zero]

@[reassoc (attr := simp)]
theorem rightDerived_comp_boundary (n : ℕ) :
    (NatTrans.rightDerived S.g n).app X ≫ S.rightDerivedBoundary I hS n = 0 := by
  dsimp only [rightDerivedBoundary]
  rw [← Category.assoc, S.rightDerived_homologyMap_g I n]
  simp only [Category.assoc]
  rw [reassoc_of% ((S.mapInjectiveResolution_shortExact hS I).comp_δ n (n + 1) rfl)]
  simp only [zero_comp, comp_zero]

/-- Exactness at the first functor in the next degree, with its native map. -/
theorem rightDerived_exact₁ (n : ℕ) :
    (ShortComplex.mk _ _ (S.rightDerivedBoundary_comp I hS n)).Exact := by
  let T := ShortComplex.mk _ _
    ((S.mapInjectiveResolution_shortExact hS I).δ_comp n (n + 1) rfl)
  apply ShortComplex.exact_of_iso
    (ShortComplex.isoMk (S₂ := T) (I.isoRightDerivedObj S.X₃ n)
      (I.isoRightDerivedObj S.X₁ (n + 1)) (I.isoRightDerivedObj S.X₂ (n + 1))
      (by simp [rightDerivedBoundary, T, Category.assoc])
      (S.rightDerived_homologyMap_f I (n + 1)).symm).symm
  exact (S.mapInjectiveResolution_shortExact hS I).homology_exact₁ n (n + 1) rfl

/-- Exactness at the middle functor in every degree. -/
theorem rightDerived_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _ (S.rightDerived_comp_eq_zero I n)).Exact := by
  let T := (S.mapInjectiveResolution I).map (HomologicalComplex.homologyFunctor D (.up ℕ) n)
  apply ShortComplex.exact_of_iso
    (ShortComplex.isoMk (S₂ := T) (I.isoRightDerivedObj S.X₁ n)
      (I.isoRightDerivedObj S.X₂ n) (I.isoRightDerivedObj S.X₃ n)
      (S.rightDerived_homologyMap_f I n).symm
      (S.rightDerived_homologyMap_g I n).symm).symm
  exact (S.mapInjectiveResolution_shortExact hS I).homology_exact₂ n

/-- Exactness at the third functor before the original connecting morphism. -/
theorem rightDerived_exact₃ (n : ℕ) :
    (ShortComplex.mk _ _ (S.rightDerived_comp_boundary I hS n)).Exact := by
  let T := ShortComplex.mk _ _
    ((S.mapInjectiveResolution_shortExact hS I).comp_δ n (n + 1) rfl)
  apply ShortComplex.exact_of_iso
    (ShortComplex.isoMk (S₂ := T) (I.isoRightDerivedObj S.X₂ n)
      (I.isoRightDerivedObj S.X₃ n) (I.isoRightDerivedObj S.X₁ (n + 1))
      (S.rightDerived_homologyMap_g I n).symm
      (by simp [rightDerivedBoundary, T, Category.assoc])).symm
  exact (S.mapInjectiveResolution_shortExact hS I).homology_exact₃ n (n + 1) rfl

/-- A surjective preceding difference and a zero middle image kill the next
first image. This is the degree-one source-cover step with its actual maps. -/
theorem rightDerived_isZero_left_succ_of_epi (n : ℕ)
    [Epi ((NatTrans.rightDerived S.g n).app X)]
    (hzero : IsZero ((S.X₂.rightDerived (n + 1)).obj X)) :
    IsZero ((S.X₁.rightDerived (n + 1)).obj X) := by
  have hδ : S.rightDerivedBoundary I hS n = 0 := by
    apply (cancel_epi ((NatTrans.rightDerived S.g n).app X)).mp
    simp only [S.rightDerived_comp_boundary I hS n, comp_zero]
  exact (S.rightDerived_exact₁ I hS n).isZero_X₂ hδ (hzero.eq_of_tgt _ _)

/-- Higher source-cover vanishing uses only the preceding intersection image
and the same-degree middle image, without any intermediate direct-image acyclicity. -/
theorem rightDerived_isZero_left_succ (n : ℕ)
    (hprev : IsZero ((S.X₃.rightDerived n).obj X))
    (hzero : IsZero ((S.X₂.rightDerived (n + 1)).obj X)) :
    IsZero ((S.X₁.rightDerived (n + 1)).obj X) :=
  (S.rightDerived_exact₁ I hS n).isZero_X₂
    (hprev.eq_of_src _ _) (hzero.eq_of_tgt _ _)

end CategoryTheory.ShortComplex
