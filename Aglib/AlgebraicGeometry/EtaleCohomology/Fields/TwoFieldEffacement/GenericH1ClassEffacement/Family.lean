/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.GenericH1ClassEffacement.Generic

/-! # Generic pointed H1 effacement for the original family

The original family supplies its generic cartesian square and smooth fibre
internally. The generic theorem applies to that same fibre and coefficient.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
universe u eX
attribute [local instance] hasSheafifyLarge HasExt.standard
open FiniteEtale

section Family
variable (A B k K : Type u) [CommRing A] [CommRing B] [Field k] [Field K]
  [Algebra A B] [Algebra A k] [Algebra A K] [Algebra B K] [Algebra k K]
  [IsScalarTower A B K] [IsScalarTower A k K]
  {X : Scheme.{u}} (pX : X ⟶ Spec (.of A))
local notation "U" => pullback pX (Spec.algebraMap A k)
local notation "Y" => pullback pX (Spec.algebraMap A B)
local notation "p" => pullback.snd pX (Spec.algebraMap A k)
local notation "e" => pullback.snd pX (Spec.algebraMap A B)

/-- The actual two generic base changes of the original A-family commute. -/
def familyGenericMap : pullback e (Spec.algebraMap B K) ⟶ U :=
  pullback.lift
    (pullback.fst e (Spec.algebraMap B K) ≫ pullback.fst pX (Spec.algebraMap A B))
    (pullback.snd e (Spec.algebraMap B K) ≫ Spec.algebraMap k K) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc, Category.assoc]
      congr 1
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext
        ((IsScalarTower.algebraMap_eq A B K).symm.trans
          (IsScalarTower.algebraMap_eq A k K))))

/-- The family supplies the whole generic cartesian square; it is not a
class-zero or coefficient-presentation certificate. -/
theorem familyGenericSquare :
    IsPullback (familyGenericMap A B k K pX)
      (pullback.snd e (Spec.algebraMap B K)) p (Spec.algebraMap k K) := by
  have ht : Spec.algebraMap k K ≫ Spec.algebraMap A k =
      Spec.algebraMap B K ≫ Spec.algebraMap A B := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext
      ((IsScalarTower.algebraMap_eq A k K).symm.trans
        (IsScalarTower.algebraMap_eq A B K)))
  apply IsPullback.of_right (h₁₂ := pullback.fst pX (Spec.algebraMap A k))
    (h₂₂ := Spec.algebraMap A k)
  · rw [show familyGenericMap A B k K pX ≫ pullback.fst pX (Spec.algebraMap A k) =
      pullback.fst e (Spec.algebraMap B K) ≫ pullback.fst pX (Spec.algebraMap A B) from
        pullback.lift_fst _ _ _, ht]
    exact (IsPullback.of_hasPullback e (Spec.algebraMap B K)).paste_horiz
      (IsPullback.of_hasPullback pX (Spec.algebraMap A B))
  · exact pullback.lift_snd _ _ _
  · exact IsPullback.of_hasPullback pX (Spec.algebraMap A k)

/-- The original A-family instance constructs its generic square internally.
Only the whole generic fibre is assumed affine, not the original family. -/
theorem exists_family_generic_pointed_H1_effacement
    [QuasiCompact pX] [QuasiSeparated pX] [SmoothOfRelativeDimension 1 pX]
    [GeometricallyConnected pX] [IsAffine U]
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} Y)]
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    (M : AbelianSheaf.{u, u + 1} (Spec (.of B)))
    (n : ℕ) (hn : 0 < n) (hM : n • 𝟙 M = 0) (hunit : IsUnit (n : k))
    (c : Sheaf.H.{eX} ((inverseImage e).obj M) 1) :
    GenericPointedH1Effacement B k K e p x hx
      (familyGenericMap A B k K pX) (familyGenericSquare A B k K pX) M n c := by
  let : SmoothOfRelativeDimension 1 p :=
    (@MorphismProperty.IsStableUnderBaseChange.of_isPullback
      Scheme.{u} _ (@SmoothOfRelativeDimension 1)
      (smoothOfRelativeDimension_isStableUnderBaseChange 1))
      (IsPullback.of_hasPullback pX (Spec.algebraMap A k)) inferInstance
  exact exists_generic_pointed_H1_effacement B k K e p x hx
    (familyGenericMap A B k K pX) (familyGenericSquare A B k K pX)
    M n hn hM hunit c

end Family

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
