/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov

/-!
# Comparisons on bounded-below derived objects

Two triangulated functors preserving the native lower cohomological bounds
can be compared on an arbitrary bounded-below object by its original homology
singles. For each homology degree only one finite truncation is needed.
No upper bound on the object, termwise condition, convergence premise or
cohomological-dimension bound is required.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w u' v' w'

namespace DerivedCategory.Plus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
    {F G : Plus C ⥤ Plus B} [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated] (τ : F ⟶ G) [τ.CommShift ℤ]

/-- A comparison preserving lower bounds is invertible on a bounded-below object
if it is invertible on the singles of that object's original homology. -/
theorem isIso_app_of_homology_singles
    (hF : ∀ (X : Plus C) (a : ℤ), X.IsGE a → (F.obj X).IsGE a)
    (hG : ∀ (X : Plus C) (a : ℤ), X.IsGE a → (G.obj X).IsGE a)
    (K : Plus C)
    (hs : ∀ i : ℤ,
      IsIso (τ.app ((singleFunctor C i).obj ((homologyFunctor C i).obj K)))) :
    IsIso (τ.app K) := by
  obtain ⟨a, ha⟩ := K.property
  let : K.IsGE a := (isGE_ι_obj_iff K a).mp ha
  apply (isIso_iff _).mpr
  intro n
  let L := (TStructure.t.truncLT (n + 1)).obj K
  let : L.IsGE a := by dsimp [L]; infer_instance
  let : L.IsLE n := by dsimp [L]; infer_instance
  have hL : IsIso (τ.app L) := by
    apply isIso_app_of_homology_bounds τ L a n
    intro i hai hin
    exact (NatTrans.isIso_app_iff_of_iso τ
      ((singleFunctor C i).mapIso (homologyTruncLTIso K (n + 1) i (by omega)))).mpr
        (hs i)
  let T := (TStructure.t.triangleLTGE (n + 1)).obj K
  have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished (n + 1) K
  let : (F.obj T.obj₃).IsGE (n + 1) := hF _ _ inferInstance
  let : (G.obj T.obj₃).IsGE (n + 1) := hG _ _ inferInstance
  let : (F.mapTriangle.obj T).obj₃.IsGE (n + 1) := by
    change (F.obj T.obj₃).IsGE (n + 1)
    infer_instance
  let : (G.mapTriangle.obj T).obj₃.IsGE (n + 1) := by
    change (G.obj T.obj₃).IsGE (n + 1)
    infer_instance
  let : IsIso ((homologyFunctor B n).map (F.map T.mor₁)) :=
    isIso_homology_mor₁_of_isGE (F.mapTriangle.obj T) (F.map_distinguished T hT)
      (n + 1) n (by omega)
  let : IsIso ((homologyFunctor B n).map (G.map T.mor₁)) :=
    isIso_homology_mor₁_of_isGE (G.mapTriangle.obj T) (G.map_distinguished T hT)
      (n + 1) n (by omega)
  let : IsIso ((homologyFunctor B n).map (τ.app T.obj₁)) := by
    change IsIso ((homologyFunctor B n).map (τ.app L))
    infer_instance
  have hnat := congrArg ((homologyFunctor B n).map) (τ.naturality T.mor₁)
  simp only [Functor.map_comp] at hnat
  change IsIso ((homologyFunctor B n).map (τ.app T.obj₂))
  apply (isIso_comp_left_iff ((homologyFunctor B n).map (F.map T.mor₁)) _).mp
  rw [hnat]
  infer_instance

/-- A lower-bound-preserving triangulated comparison is a natural isomorphism
when every native single component is invertible. -/
theorem isIso_of_singles
    (hF : ∀ (X : Plus C) (a : ℤ), X.IsGE a → (F.obj X).IsGE a)
    (hG : ∀ (X : Plus C) (a : ℤ), X.IsGE a → (G.obj X).IsGE a)
    (hs : ∀ (M : C) (i : ℤ), IsIso (τ.app ((singleFunctor C i).obj M))) : IsIso τ := by
  let : ∀ K, IsIso (τ.app K) := fun K =>
    isIso_app_of_homology_singles τ hF hG K (fun i => hs _ i)
  exact NatIso.isIso_of_isIso_app τ

end DerivedCategory.Plus
