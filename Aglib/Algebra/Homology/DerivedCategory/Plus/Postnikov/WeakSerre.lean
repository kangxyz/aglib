/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.HomologyObjectProperty
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Serre

/-! # Weak-Serre Postnikov propagation with original coefficients

A property closed under known kernels, known cokernels, and extensions propagates
through the original finite Postnikov tower when tested in all output degrees.
Finite truncation then gives each degree for any lower-bound-preserving original
triangulated functor. No arbitrary-subobject closure or uniform amplitude is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ZeroObject
namespace DerivedCategory.Plus
universe u v w u' v' w'
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
    (F : Plus A ⥤ Plus B) [F.CommShift ℤ] [F.IsTriangulated]
    (P : ObjectProperty B) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]

/-- The all-degree weak-Serre property passes along an actual finite Postnikov tower. -/
theorem homologyProperty_obj_of_homology_bounds_weakSerre
    (K : Plus A) (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hs : ∀ i : ℤ, a ≤ i → i ≤ b → ∀ n : ℤ,
      P ((homologyFunctor B n).obj
        (F.obj ((singleFunctor A i).obj ((homologyFunctor A i).obj K)))))
    (n : ℤ) : P ((homologyFunctor B n).obj (F.obj K)) := by
  let Q : ObjectProperty (Plus A) := fun L =>
    ∀ k : ℤ, P ((homologyFunctor B k).obj (F.obj L))
  let : Q.IsClosedUnderIsomorphisms := {
    of_iso := fun e h k => P.prop_of_iso ((F ⋙ homologyFunctor B k).mapIso e) (h k) }
  let : Q.ContainsZero := {
    exists_zero := ⟨0, isZero_zero _, fun k =>
      P.prop_of_isZero ((F ⋙ homologyFunctor B k).map_isZero (isZero_zero _))⟩ }
  let : Q.IsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk'
    (P := Q) (fun T hT h₁ h₃ k =>
      P.homology_middle_of_distinguished
        (ι.mapTriangle.obj (F.mapTriangle.obj T))
        (ι.map_distinguished _ (F.map_distinguished T hT)) h₁ h₃ k)
  exact property_of_homology_bounds Q K a b hs n

/-- A lower-bound-preserving triangulated functor preserves the all-degree
weak-Serre property when tested on the original homology singles. -/
theorem homologyProperty_obj_of_homology_singles_weakSerre
    (hF : ∀ (L : Plus A) (a : ℤ), L.IsGE a → (F.obj L).IsGE a)
    (K : Plus A)
    (hs : ∀ i n : ℤ, P ((homologyFunctor B n).obj
      (F.obj ((singleFunctor A i).obj ((homologyFunctor A i).obj K)))))
    (n : ℤ) : P ((homologyFunctor B n).obj (F.obj K)) := by
  obtain ⟨a, ha⟩ := K.property
  let : K.IsGE a := (isGE_ι_obj_iff K a).mp ha
  let L := (TStructure.t.truncLT (n + 1)).obj K
  let : L.IsGE a := by dsimp [L]; infer_instance
  let : L.IsLE n := by dsimp [L]; infer_instance
  have hL : P ((homologyFunctor B n).obj (F.obj L)) := by
    apply homologyProperty_obj_of_homology_bounds_weakSerre F P L a n
    intro i hai hin k
    exact P.prop_of_iso ((F ⋙ homologyFunctor B k).mapIso
      ((singleFunctor A i).mapIso (homologyTruncLTIso K (n + 1) i (by omega))).symm)
        (hs i k)
  let T := (TStructure.t.triangleLTGE (n + 1)).obj K
  have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished (n + 1) K
  let : (F.mapTriangle.obj T).obj₃.IsGE (n + 1) := hF _ _ inferInstance
  let φ : (homologyFunctor B n).obj (F.obj L) ⟶
      (homologyFunctor B n).obj (F.obj K) :=
    (homologyFunctor B n).map (F.map T.mor₁)
  have hφ : IsIso φ :=
    isIso_homology_mor₁_of_isGE (F.mapTriangle.obj T) (F.map_distinguished T hT)
      (n + 1) n (by omega)
  exact P.prop_of_iso (@asIso B _ _ _ φ hφ) hL

end DerivedCategory.Plus
