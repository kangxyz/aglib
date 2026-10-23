/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.Composition
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure

/-! # The original derived-single and all-degree exchange criteria

The published source/homology/target transport identifies the homology of
the original derived exchange with the original higher-image exchange.
Both actual sides on a source single are nonnegative. Thus invertibility of
all original natural-degree maps is equivalent to invertibility of the same
original derived-single component, without an extra H0 or boundedness premise.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

section TypedTransport

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {J : A ⥤ B} {L M : B ⥤ C} {H : C ⥤ D} {U V : A ⥤ D}

private theorem isIso_middle_of_whiskered_transport
    (s : U ≅ J ⋙ L ⋙ H) (β : L ⟶ M) (t : J ⋙ M ⋙ H ≅ V)
    (δ : U ⟶ V)
    (hδ : δ = s.hom ≫ Functor.whiskerLeft J (Functor.whiskerRight β H) ≫ t.hom)
    (X : A) [IsIso (δ.app X)] : IsIso (H.map (β.app (J.obj X))) := by
  have hi : IsIso (s.hom.app X ≫ H.map (β.app (J.obj X)) ≫ t.hom.app X) := by
    change IsIso ((s.hom ≫ Functor.whiskerLeft J (Functor.whiskerRight β H) ≫
      t.hom).app X)
    rw [← hδ]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp ((isIso_comp_left_iff _ _).mp hi)

end TypedTransport

universe u dX dS dX' dS'

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- The original all-degree sheaf exchange is the complete homology test for
the same original derived exchange on a source single. All four declared
derived-category universes remain independent. -/
theorem derivedBaseChangeMap_single_isIso_iff_higher
    (F : AbelianSheaf.{u, u + 1} X) :
    IsIso ((derivedBaseChangeMap f f' g g' h).app
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)) ↔
      ∀ q : ℕ, IsIso ((higherBaseChangeMap f f' g g' h q).app F) := by
  constructor
  · intro hF q
    have := hF
    exact higherBaseChangeMap_isIso_app_of_derived f f' g g' h F q
  · intro hF
    let K := (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F
    have h₁ : ((derivedDirectImage f).obj K).IsGE 0 :=
      (directImage f).rightDerivedFunctorPlus_isGE K 0
    have h₂ : ((derivedInverseImage g).obj ((derivedDirectImage f).obj K)).IsGE 0 :=
      (inverseImage g).rightDerivedFunctorPlus_isGE _ 0
    have h₃ : ((derivedInverseImage g').obj K).IsGE 0 :=
      (inverseImage g').rightDerivedFunctorPlus_isGE K 0
    have h₄ : ((derivedDirectImage f').obj ((derivedInverseImage g').obj K)).IsGE 0 :=
      (directImage f').rightDerivedFunctorPlus_isGE _ 0
    have : ((derivedDirectImage f ⋙ derivedInverseImage g).obj
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)).IsGE 0 := h₂
    have : ((derivedInverseImage g' ⋙ derivedDirectImage f').obj
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)).IsGE 0 := h₄
    apply (DerivedCategory.Plus.isIso_iff _).mpr
    intro k
    by_cases hk : k < 0
    · exact (DerivedCategory.Plus.isZero_homology_of_isGE _ 0 k hk).isIso
        (DerivedCategory.Plus.isZero_homology_of_isGE _ 0 k hk) _
    · have he : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (by omega)
      rw [← he]
      have := hF k.toNat
      exact isIso_middle_of_whiskered_transport
        (higherBaseChangeSourceIso f g k.toNat) (derivedBaseChangeMap f f' g g' h)
        (higherBaseChangeTargetIso f' g' k.toNat)
        (higherBaseChangeMap f f' g g' h k.toNat)
        (higherBaseChangeMap_eq_transport f f' g g' h k.toNat) F

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
