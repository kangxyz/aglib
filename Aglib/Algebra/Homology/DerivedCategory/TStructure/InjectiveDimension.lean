/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension

/-!
# Injective-dimension vanishing against bounded derived objects

If an actual derived object has cohomology in `[a,b]` and an object `N` has
native injective dimension at most `d`, then maps to `N[0][t]` vanish when
`d < t+a`. The existing finite Postnikov theorem reduces this to the
original homology singles and the native Ext vanishing criterion.

No bound on the terms of a representative, choice of injective resolution,
enough-injectives hypothesis, or new Postnikov construction is required.
The object, morphism, Ext, and selected derived-category sizes are independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Pretriangulated ZeroObject

universe u v w e

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

private theorem subsingleton_hom_single_shift_of_injectiveDimension_single
    [HasExt.{e} C] (M N : C) (j t : ℤ) (d : ℕ) [HasInjectiveDimensionLE N d]
    (ht : (d : ℤ) < t + j) :
    Subsingleton ((singleFunctor C j).obj M ⟶ ((singleFunctor C 0).obj N)⟦t⟧) := by
  let k := (t + j).toNat
  have hk : (k : ℤ) = t + j := Int.toNat_of_nonneg (by omega)
  let F := CategoryTheory.shiftFunctor (DerivedCategory C) j
  let s : F.obj ((singleFunctor C j).obj M) ≅ (singleFunctor C 0).obj M :=
    ((singleFunctors C).shiftIso j 0 j (add_zero j)).app M
  let z : F.obj (((singleFunctor C 0).obj N)⟦t⟧) ≅
      ((singleFunctor C 0).obj N)⟦(k : ℤ)⟧ :=
    ((shiftFunctorAdd' (DerivedCategory C) t j (k : ℤ) (by omega)).app
      ((singleFunctor C 0).obj N)).symm
  let E : ((singleFunctor C j).obj M ⟶ ((singleFunctor C 0).obj N)⟦t⟧) ≃
      Ext.{e} M N k :=
    ((shiftEquiv (DerivedCategory C) j).fullyFaithfulFunctor.homEquiv).trans
      ((Iso.homCongr s z).trans (Ext.homEquiv : Ext.{e} M N k ≃ _).symm)
  let : Subsingleton (Ext.{e} M N k) :=
    HasInjectiveDimensionLT.subsingleton N (d + 1) k (by omega) M
  exact E.injective.subsingleton

/-- Native finite injective dimension kills maps from an actual bounded
cohomology object to a sufficiently shifted single. Only original homology
bounds, not term bounds or a supplied resolution, are needed. -/
theorem subsingleton_hom_single_shift_of_injectiveDimension
    [HasExt.{e} C] (X : DerivedCategory C) (a b t : ℤ) [X.IsGE a] [X.IsLE b]
    (N : C) (d : ℕ) [HasInjectiveDimensionLE N d] (ht : (d : ℤ) < t + a) :
    Subsingleton (X ⟶ ((singleFunctor C 0).obj N)⟦t⟧) := by
  let L : Plus C := ⟨X, a, inferInstance⟩
  let : L.IsGE a := (Plus.isGE_ι_obj_iff L a).mp (inferInstanceAs (X.IsGE a))
  let : L.IsLE b := (Plus.isLE_ι_obj_iff L b).mp (inferInstanceAs (X.IsLE b))
  let U : Plus C ⥤ DerivedCategory C := Plus.ι
  let Z := ((singleFunctor C 0).obj N)⟦t⟧
  let P : ObjectProperty (Plus C) := fun Y => Subsingleton (U.obj Y ⟶ Z)
  let : P.IsClosedUnderIsomorphisms := {
    of_iso := by
      intro A B c hA
      let : Subsingleton (U.obj A ⟶ Z) := hA
      exact (Iso.homCongr (U.mapIso c).symm (Iso.refl Z)).injective.subsingleton }
  let : P.ContainsZero := {
    exists_zero := ⟨0, isZero_zero _,
      ⟨fun f g => (U.map_isZero (isZero_zero _)).eq_of_src f g⟩⟩ }
  let : P.IsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk' (P := P)
    (fun T hT h₁ h₃ => by
      change Subsingleton (U.obj T.obj₂ ⟶ Z)
      have hz (f : U.obj T.obj₂ ⟶ Z) : f = 0 := by
        obtain ⟨g, hg⟩ := (U.mapTriangle.obj T).yoneda_exact₂
          (U.map_distinguished T hT) f (h₁.elim _ _)
        exact hg.trans (by rw [h₃.elim g 0, comp_zero])
      exact ⟨fun f g => (hz f).trans (hz g).symm⟩)
  exact Plus.property_of_homology_bounds P L a b (fun j haj _ =>
    subsingleton_hom_single_shift_of_injectiveDimension_single
      ((Plus.homologyFunctor C j).obj L) N j t d (by omega))

/-- Pointwise form of the same finite-injective-dimension vanishing. -/
theorem hom_single_shift_eq_zero_of_injectiveDimension
    [HasExt.{e} C] (X : DerivedCategory C) (a b t : ℤ) [X.IsGE a] [X.IsLE b]
    (N : C) (d : ℕ) [HasInjectiveDimensionLE N d] (ht : (d : ℤ) < t + a)
    (f : X ⟶ ((singleFunctor C 0).obj N)⟦t⟧) : f = 0 :=
  (subsingleton_hom_single_shift_of_injectiveDimension X a b t N d ht).elim f 0

end DerivedCategory
