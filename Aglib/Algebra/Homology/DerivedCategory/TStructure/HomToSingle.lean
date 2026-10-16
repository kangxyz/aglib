/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.TStructure.Homology
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Morphisms from an upper-bounded object to its top-degree single

For an object with no homology above degree n, maps to a native single in
degree n are exactly maps from its original degree-n homology. The forward
map is the native homology map followed by the original single comparison.
The inverse factors through native lower truncation and its normalized
concentrated-homology reconstruction. Both source and coefficient naturality
retain the original arrows.

No lower bound, injective availability or projective availability is assumed.
The coefficient category and the derived size universes remain independent.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w
namespace DerivedCategory
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The original lower-truncation projection preserves every retained homology degree. -/
theorem isIso_homology_truncGEπ (K : DerivedCategory C) (a i : ℤ) (hi : a ≤ i) :
    IsIso ((homologyFunctor C i).map ((TStructure.t.truncGEπ a).app K)) := by
  let T := (TStructure.t.triangleLTGE a).obj K
  have hT := TStructure.t.triangleLTGE_distinguished a K
  have h₀ := isZero_of_isLE T.obj₁ (a - 1) i (by omega)
  have hnext := isZero_of_isLE T.obj₁ (a - 1) (i + 1) (by omega)
  change IsIso (((homologyFunctor C 0).shift i).map T.mor₂)
  let : Mono (((homologyFunctor C 0).shift i).map T.mor₂) :=
    ((homologyFunctor C 0).homologySequence_mono_shift_map_mor₂_iff T hT i).mpr
      (h₀.eq_of_src _ _)
  let : Epi (((homologyFunctor C 0).shift i).map T.mor₂) :=
    ((homologyFunctor C 0).homologySequence_epi_shift_map_mor₂_iff
      T hT i (i + 1) rfl).mpr (hnext.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- The canonical map from an upper-bounded object to its top homology single. -/
def topHomologyProjection (K : DerivedCategory C) (n : ℤ) [K.IsLE n] :
    K ⟶ (singleFunctor C n).obj ((homologyFunctor C n).obj K) := by
  let T := (TStructure.t.truncGE n).obj K
  let π := (TStructure.t.truncGEπ n).app K
  letI := isIso_homology_truncGEπ K n n (le_refl n)
  exact π ≫ (isoSingleHomology T n).hom ≫
    (singleFunctor C n).map (asIso ((homologyFunctor C n).map π)).inv

/-- The canonical top projection induces the identity on original top homology. -/
@[reassoc]
theorem topHomologyProjection_homology (K : DerivedCategory C) (n : ℤ) [K.IsLE n] :
    (homologyFunctor C n).map (topHomologyProjection K n) ≫
      (singleFunctorCompHomologyFunctorIso C n).hom.app ((homologyFunctor C n).obj K) =
        𝟙 _ := by
  let T := (TStructure.t.truncGE n).obj K
  let π := (TStructure.t.truncGEπ n).app K
  let := isIso_homology_truncGEπ K n n (le_refl n)
  let E := asIso ((homologyFunctor C n).map π)
  let e := singleFunctorCompHomologyFunctorIso C n
  have h := e.hom.naturality E.inv
  change (homologyFunctor C n).map ((singleFunctor C n).map E.inv) ≫
    e.hom.app ((homologyFunctor C n).obj K) =
      e.hom.app ((homologyFunctor C n).obj T) ≫ E.inv at h
  change (homologyFunctor C n).map
    (π ≫ (isoSingleHomology T n).hom ≫ (singleFunctor C n).map E.inv) ≫ _ = _
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, h,
    ← Category.assoc _ _ E.inv, isoSingleHomology_homology, Category.id_comp]
  exact E.hom_inv_id

/-- Top homology detects maps from an upper-bounded object into the same-degree single. -/
theorem homology_map_injective_to_single_of_isLE (K : DerivedCategory C) (n : ℤ)
    [K.IsLE n] (V : C) :
    Function.Injective (fun f : K ⟶ (singleFunctor C n).obj V =>
      (homologyFunctor C n).map f) := by
  intro f g h
  let T := (TStructure.t.truncGE n).obj K
  let π := (TStructure.t.truncGEπ n).app K
  let f' := TStructure.t.descTruncGE f n
  let g' := TStructure.t.descTruncGE g n
  have hf : π ≫ f' = f := TStructure.t.π_descTruncGE f n
  have hg : π ≫ g' = g := TStructure.t.π_descTruncGE g n
  let := isIso_homology_truncGEπ K n n (le_refl n)
  have h' : f' = g' := by
    apply homology_map_injective_of_isGE_of_isLE T _ n
    apply (cancel_epi ((homologyFunctor C n).map π)).mp
    rw [← Functor.map_comp, ← Functor.map_comp, hf, hg]
    exact h
  rw [← hf, ← hg, h']

/-- Apply original homology and the native single/homology comparison to a morphism. -/
def homToSingleAddHom (K : DerivedCategory C) (n : ℤ) (V : C) :
    (K ⟶ (singleFunctor C n).obj V) →+ ((homologyFunctor C n).obj K ⟶ V) where
  toFun f := (homologyFunctor C n).map f ≫
    (singleFunctorCompHomologyFunctorIso C n).hom.app V
  map_zero' := by simp
  map_add' f g := by simp [Preadditive.add_comp]

/-- The normalized top projection lifts every prescribed morphism on top homology. -/
theorem homToSingleAddHom_projection (K : DerivedCategory C) (n : ℤ)
    [K.IsLE n] (V : C) (a : (homologyFunctor C n).obj K ⟶ V) :
    homToSingleAddHom K n V
      (topHomologyProjection K n ≫ (singleFunctor C n).map a) = a := by
  have h := (singleFunctorCompHomologyFunctorIso C n).hom.naturality a
  change (homologyFunctor C n).map ((singleFunctor C n).map a) ≫
    (singleFunctorCompHomologyFunctorIso C n).hom.app V =
      (singleFunctorCompHomologyFunctorIso C n).hom.app ((homologyFunctor C n).obj K) ≫ a at h
  change (homologyFunctor C n).map
    (topHomologyProjection K n ≫ (singleFunctor C n).map a) ≫ _ = _
  rw [Functor.map_comp, Category.assoc, h, ← Category.assoc,
    topHomologyProjection_homology, Category.id_comp]

/-- Maps to a same-degree single are exactly maps from original top homology. -/
def homToSingleAddEquiv (K : DerivedCategory C) (n : ℤ) [K.IsLE n] (V : C) :
    (K ⟶ (singleFunctor C n).obj V) ≃+ ((homologyFunctor C n).obj K ⟶ V) :=
  AddEquiv.ofBijective (homToSingleAddHom K n V) ⟨by
    intro f g h
    apply homology_map_injective_to_single_of_isLE K n V
    exact (cancel_mono ((singleFunctorCompHomologyFunctorIso C n).hom.app V)).mp h,
    fun a => ⟨topHomologyProjection K n ≫ (singleFunctor C n).map a,
      homToSingleAddHom_projection K n V a⟩⟩

/-- The forward map is original homology followed by the native single comparison. -/
theorem homToSingleAddEquiv_apply (K : DerivedCategory C) (n : ℤ) [K.IsLE n]
    (V : C) (f : K ⟶ (singleFunctor C n).obj V) :
    homToSingleAddEquiv K n V f = (homologyFunctor C n).map f ≫
      (singleFunctorCompHomologyFunctorIso C n).hom.app V := rfl

/-- The inverse uses the canonical original top projection and the native single functor. -/
theorem homToSingleAddEquiv_symm_apply (K : DerivedCategory C) (n : ℤ) [K.IsLE n]
    (V : C) (a : (homologyFunctor C n).obj K ⟶ V) :
    (homToSingleAddEquiv K n V).symm a =
      topHomologyProjection K n ≫ (singleFunctor C n).map a := by
  apply (homToSingleAddEquiv K n V).injective
  exact ((homToSingleAddEquiv K n V).apply_symm_apply a).trans
    (homToSingleAddHom_projection K n V a).symm

/-- The top-Hom equivalence preserves precomposition by every bounded source map. -/
theorem homToSingleAddEquiv_naturality_left {K L : DerivedCategory C} (n : ℤ)
    [K.IsLE n] [L.IsLE n] (V : C) (f : K ⟶ L) (g : L ⟶ (singleFunctor C n).obj V) :
    homToSingleAddEquiv K n V (f ≫ g) =
      (homologyFunctor C n).map f ≫ homToSingleAddEquiv L n V g := by
  change (homologyFunctor C n).map (f ≫ g) ≫ _ = _ ≫ (_ ≫ _)
  rw [Functor.map_comp, Category.assoc]

/-- The top-Hom equivalence preserves the original map on target coefficients. -/
theorem homToSingleAddEquiv_naturality_right (K : DerivedCategory C) (n : ℤ)
    [K.IsLE n] {V W : C} (f : K ⟶ (singleFunctor C n).obj V) (g : V ⟶ W) :
    homToSingleAddEquiv K n W (f ≫ (singleFunctor C n).map g) =
      homToSingleAddEquiv K n V f ≫ g := by
  have h := (singleFunctorCompHomologyFunctorIso C n).hom.naturality g
  change (homologyFunctor C n).map ((singleFunctor C n).map g) ≫
    (singleFunctorCompHomologyFunctorIso C n).hom.app W =
      (singleFunctorCompHomologyFunctorIso C n).hom.app V ≫ g at h
  change (homologyFunctor C n).map (f ≫ (singleFunctor C n).map g) ≫ _ = (_ ≫ _) ≫ g
  rw [Functor.map_comp, Category.assoc, h, Category.assoc]

end DerivedCategory
