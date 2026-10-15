/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.HasLimits

/-! # Sequential colimits of original isomorphisms

The actual successor inverses construct a colimiting cocone at stage zero.
The comparison preserves every original colimit inclusion, in independent
object and morphism universes.

Source: `Quillen/CategoryTheory/Limits/SequentialIsoColimit.lean`
from the supplied Quillen archive.
Source SHA-256: `aa10b0d79332868b793bd7a641d1ecb4e2cb55024540ddb9b776647632a0426a`.
All declarations are migrated with their original hypotheses and maps.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
universe u v
namespace CategoryTheory.Limits.SequentialSystem
variable {C : Type u} [Category.{v} C] {X : ℕ → C} (f : ∀ n, X n ⟶ X (n + 1))
  [∀ n, IsIso (f n)]

/-- Transport each stage backward along the transition isomorphisms to stage zero. -/
def toZeroIso : ∀ n, X n ≅ X 0
  | 0 => Iso.refl _
  | n+1 => (asIso (f n)).symm ≪≫ toZeroIso n

/-- The natural transformation from the sequence to its stage-zero constant diagram. -/
def toZero : Functor.ofSequence f ⟶ (Functor.const ℕ).obj (X 0) :=
  NatTrans.ofSequence (fun n ↦ (toZeroIso f n).hom) (by
    intro n
    rw [Functor.ofSequence_map_homOfLE_succ]
    change f n ≫ (inv (f n) ≫ (toZeroIso f n).hom) = (toZeroIso f n).hom ≫ 𝟙 _
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp, Category.comp_id])

/-- The sequence is naturally isomorphic to its stage-zero constant diagram. -/
def constIso : Functor.ofSequence f ≅ (Functor.const ℕ).obj (X 0) :=
  NatIso.ofComponents (fun n ↦ toZeroIso f n) (fun {_ _} a ↦ (toZero f).naturality a)

/-- The cocone on stage zero defined by the inverse transition maps. -/
def cocone : Cocone (Functor.ofSequence f) where
  pt := X 0
  ι := toZero f

/-- The stage-zero cocone is colimiting when every transition is an isomorphism. -/
def isColimit : IsColimit (cocone f) where
  desc s := s.ι.app 0
  fac s n := by
    induction n with
    | zero => change 𝟙 _ ≫ _ = _; rw [Category.id_comp]
    | succ n ih =>
      change (inv (f n) ≫ (toZeroIso f n).hom) ≫ s.ι.app 0 = s.ι.app (n + 1)
      change (toZeroIso f n).hom ≫ s.ι.app 0 = s.ι.app n at ih
      rw [Category.assoc, ih]
      have hn := s.w (homOfLE (Nat.le_succ n))
      rw [Functor.ofSequence_map_homOfLE_succ] at hn
      rw [← hn, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  uniq s m hm := by
    have h := hm 0
    change 𝟙 _ ≫ m = s.ι.app 0 at h
    simpa only [Category.id_comp] using h

/-- The colimit comparison is assembled from the original transition isomorphisms. -/
def colimitIso [HasColimit (Functor.ofSequence f)] : colimit (Functor.ofSequence f) ≅ X 0 :=
  (colimit.isColimit _).coconePointUniqueUpToIso (isColimit f)

@[simp] theorem ι_colimitIso_hom [HasColimit (Functor.ofSequence f)] (n : ℕ) :
    colimit.ι (Functor.ofSequence f) n ≫ (colimitIso f).hom = (toZeroIso f n).hom :=
  colimit.comp_coconePointUniqueUpToIso_hom (isColimit f) n

end CategoryTheory.Limits.SequentialSystem

namespace CategoryTheory.Limits.SequentialSystem
variable {C : Type u} [Category.{v} C] (F : ℕ ⥤ C)

/-- The sequence of actual successor maps recovers the original functor. -/
def reconstructionIso : Functor.ofSequence (fun n ↦ F.map (homOfLE (Nat.le_succ n))) ≅ F := by
  let η : Functor.ofSequence (fun n ↦ F.map (homOfLE (Nat.le_succ n))) ⟶ F :=
    NatTrans.ofSequence (fun _ ↦ 𝟙 _) (by intro n; simp)
  exact NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {_ _} f ↦ η.naturality f)

/-- Explicit original colimit comparison when every actual successor is invertible. -/
def colimitIsoOfSucc [HasColimit F] [∀ n, IsIso (F.map (homOfLE (Nat.le_succ n)))] :
    colimit F ≅ F.obj 0 := by
  letI : HasColimit (Functor.ofSequence (fun n ↦ F.map (homOfLE (Nat.le_succ n)))) :=
    hasColimit_of_iso (reconstructionIso F)
  exact HasColimit.isoOfNatIso (reconstructionIso F).symm ≪≫
    colimitIso (fun n ↦ F.map (homOfLE (Nat.le_succ n)))

@[simp] theorem ι_colimitIsoOfSucc_hom [HasColimit F] [∀ n, IsIso (F.map (homOfLE (Nat.le_succ n)))]
    (n : ℕ) : colimit.ι F n ≫ (colimitIsoOfSucc F).hom =
      (toZeroIso (fun n ↦ F.map (homOfLE (Nat.le_succ n))) n).hom := by
  simp only [colimitIsoOfSucc, Iso.trans_hom, HasColimit.ι_isoOfNatIso_hom_assoc,
    ι_colimitIso_hom]
  exact Category.id_comp _

end CategoryTheory.Limits.SequentialSystem
