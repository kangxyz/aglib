/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Layers
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Aglib.CategoryTheory.Triangulated.NatTransIso

/-!
# Finite devissage through the original homology layers

An isomorphism-stable property closed under extensions and containing zero
holds on a cohomologically bounded native derived object if it holds on
the singles of its original homology. Only homology bounds are required;
the terms of a chosen representative need not satisfy the property or
an upper bound. This single induction is shared by coherent-image,
support-cone and natural-comparison arguments.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ZeroObject

universe u v w

namespace DerivedCategory.Plus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- An extension-closed property is detected by the finitely many original homology
layers of a cohomologically bounded object. No condition is imposed on its terms. -/
theorem property_of_homology_bounds (P : ObjectProperty (Plus C))
    [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [P.IsTriangulatedClosed₂]
    (K : Plus C) (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hs : ∀ i : ℤ, a ≤ i → i ≤ b →
      P ((singleFunctor C i).obj ((homologyFunctor C i).obj K))) : P K := by
  have aux : ∀ (m : ℕ) (X : Plus C) (a b : ℤ), X.IsGE a → X.IsLE b →
      b - a = (m : ℤ) →
      (∀ i : ℤ, a ≤ i → i ≤ b →
        P ((singleFunctor C i).obj ((homologyFunctor C i).obj X))) → P X := by
    intro m
    induction m with
    | zero =>
      intro X a b hge hle hlen hs
      have hb : b = a := by omega
      subst b
      let : X.IsGE a := hge
      let : X.IsLE a := hle
      exact P.prop_of_iso (isoSingleHomology X a).symm (hs a le_rfl le_rfl)
    | succ m ih =>
      intro X a b hge hle hlen hs
      let : X.IsGE a := hge
      let : X.IsLE b := hle
      let t := TStructure.t (C := C)
      let X₁ : Plus C := (t.truncLT b).obj X
      let X₃ : Plus C := (t.truncGE b).obj X
      have h₁ : P X₁ := by
        apply ih X₁ a (b - 1) (by dsimp [X₁]; infer_instance)
          (by dsimp [X₁]; infer_instance) (by omega)
        intro i hai hib
        exact P.prop_of_iso
          ((singleFunctor C i).mapIso (homologyTruncLTIso X b i (by omega))).symm
          (hs i hai (by omega))
      let : X₃.IsGE b := by dsimp [X₃]; infer_instance
      let : X₃.IsLE b := by dsimp [X₃]; infer_instance
      have h₃ : P X₃ := P.prop_of_iso (isoSingleHomology X₃ b).symm
        (P.prop_of_iso
          ((singleFunctor C b).mapIso (homologyTruncGEIso X b b le_rfl))
          (hs b (by omega) le_rfl))
      exact P.ext_of_isTriangulatedClosed₂ ((t.triangleLTGE b).obj X)
        (t.triangleLTGE_distinguished b X) h₁ h₃
  by_cases hab : a ≤ b
  · exact aux (b - a).toNat K a b inferInstance inferInstance (by omega) hs
  · exact P.prop_of_isZero (TStructure.t.isZero K b a (by omega))

section Comparison

universe u' v'

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F G : Plus C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated] (τ : F ⟶ G) [τ.CommShift ℤ]

/-- A shift-compatible triangulated comparison is invertible on an object with bounded
homology if it is invertible on that object's original homology singles. -/
theorem isIso_app_of_homology_bounds (K : Plus C) (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hs : ∀ i : ℤ, a ≤ i → i ≤ b →
      IsIso (τ.app ((singleFunctor C i).obj ((homologyFunctor C i).obj K)))) :
    IsIso (τ.app K) := by
  let P : ObjectProperty (Plus C) := fun X => IsIso (τ.app X)
  let : P.IsClosedUnderIsomorphisms :=
    { of_iso := fun e h => (NatTrans.isIso_app_iff_of_iso τ e).mp h }
  let : P.ContainsZero :=
    { exists_zero := ⟨0, isZero_zero _, by
      have hF := F.map_isZero (isZero_zero (Plus C))
      have hG := G.map_isZero (isZero_zero (Plus C))
      exact ⟨⟨0, hF.eq_of_src _ _, hG.eq_of_src _ _⟩⟩⟩ }
  let : P.IsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk' (P := P)
    (fun T hT h₁ h₃ => τ.isIso_app_middle_of_distinguished T hT h₁ h₃)
  exact property_of_homology_bounds P K a b hs

end Comparison

end DerivedCategory.Plus
