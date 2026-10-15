/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Sign correction of sequential stage morphisms

Anti-commuting successor squares give a natural transformation after alternating
the original stage maps. Stage isomorphisms give the corresponding natural
isomorphism, and its hom is the same construction.

Source: `Quillen/CategoryTheory/Limits/SequentialSignCorrection.lean`
from the supplied Quillen archive.
Source SHA-256: `81391b6ac44ed8f3ec8e54375a9cd195f8da1ec16ef1506039507c7cf850c0b3`.
All declarations are migrated with their original hypotheses and maps.

Source: `Quillen/CategoryTheory/Limits/SequentialSignCorrectionHom.lean`
from the supplied Quillen archive.
Source SHA-256: `01d75f2f0f175c7a1ba67ef423f7ba5903aa407b1925e8be63352108ccb9902b`.
All declarations are migrated with their original hypotheses and maps.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Preadditive
universe u v
namespace CategoryTheory.Limits.SequentialSystem
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Successive stages carry successive genuine additive sign inversions. -/
def alternatingIso {X Y : C} (n : ℕ) (e : X ≅ Y) : X ≅ Y :=
  Nat.rec e (fun _ e ↦ -e) n

@[simp] lemma alternatingIso_zero {X Y : C} (e : X ≅ Y) : alternatingIso 0 e = e := rfl
@[simp] lemma alternatingIso_succ {X Y : C} (n : ℕ) (e : X ≅ Y) :
    alternatingIso (n + 1) e = -alternatingIso n e := rfl

lemma alternatingIso_hom {X Y : C} (n : ℕ) (e : X ≅ Y) :
    (alternatingIso n e).hom = (-1 : ℤ)^n • e.hom := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, pow_succ]

/-- An actual anti-commuting successor square becomes a commuting square after
alternating original stage inversions. -/
lemma alternatingIso_naturality {X Y X' Y' : C} (n : ℕ)
    (f : X ⟶ X') (g : Y ⟶ Y') (e : X ≅ Y) (e' : X' ≅ Y')
    (h : f ≫ e'.hom = -(e.hom ≫ g)) :
    f ≫ (alternatingIso (n + 1) e').hom = (alternatingIso n e).hom ≫ g := by
  rw [alternatingIso_hom, alternatingIso_hom, comp_zsmul, zsmul_comp, h]
  simp [pow_succ]

/-- Original level isomorphisms with actual anti-commuting transition squares
induce a natural isomorphism after the displayed sign correction. -/
def signCorrectionIso {F G : ℕ ⥤ C} (e : ∀ n, F.obj n ≅ G.obj n)
    (h : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ (e (n + 1)).hom =
      -((e n).hom ≫ G.map (homOfLE (Nat.le_succ n)))) : F ≅ G := by
  let η : F ⟶ G := NatTrans.ofSequence (fun n ↦ (alternatingIso n (e n)).hom)
    (fun n ↦ alternatingIso_naturality n _ _ _ _ (h n))
  exact NatIso.ofComponents (fun n ↦ alternatingIso n (e n)) (fun {_ _} f ↦ η.naturality f)

@[simp] lemma signCorrectionIso_hom_app {F G : ℕ ⥤ C}
    (e : ∀ n, F.obj n ≅ G.obj n)
    (h : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ (e (n + 1)).hom =
      -((e n).hom ≫ G.map (homOfLE (Nat.le_succ n)))) (n : ℕ) :
    (signCorrectionIso e h).hom.app n = (-1 : ℤ)^n • (e n).hom :=
  alternatingIso_hom n (e n)

/-- Alternating scalar signs correct an actual anti-commuting successor square. -/
theorem alternatingHom_naturality {X Y X' Y' : C} (n : ℕ)
    (f : X ⟶ X') (g : Y ⟶ Y') (a : X ⟶ Y) (b : X' ⟶ Y')
    (h : f ≫ b = -(a ≫ g)) :
    f ≫ ((-1 : ℤ) ^ (n + 1) • b) = ((-1 : ℤ) ^ n • a) ≫ g := by
  rw [comp_zsmul, zsmul_comp, h]
  simp [pow_succ]

/-- Arbitrary original stage morphisms with anti-commuting successor squares
form a natural transformation with alternating components. -/
def signCorrectionHom {F G : ℕ ⥤ C} (a : ∀ n, F.obj n ⟶ G.obj n)
    (h : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ a (n + 1) =
      -(a n ≫ G.map (homOfLE (Nat.le_succ n)))) : F ⟶ G :=
  NatTrans.ofSequence (fun n ↦ (-1 : ℤ) ^ n • a n)
    (fun n ↦ alternatingHom_naturality n _ _ _ _ (h n))

/-- The natural transformation retains the literal alternating original maps. -/
@[simp] theorem signCorrectionHom_app {F G : ℕ ⥤ C}
    (a : ∀ n, F.obj n ⟶ G.obj n)
    (h : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ a (n + 1) =
      -(a n ≫ G.map (homOfLE (Nat.le_succ n)))) (n : ℕ) :
    (signCorrectionHom a h).app n = (-1 : ℤ) ^ n • a n := rfl

/-- On isomorphism inputs this is the original sign-corrected isomorphism's map. -/
theorem signCorrectionHom_eq_iso_hom {F G : ℕ ⥤ C}
    (e : ∀ n, F.obj n ≅ G.obj n)
    (h : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ (e (n + 1)).hom =
      -((e n).hom ≫ G.map (homOfLE (Nat.le_succ n)))) :
    signCorrectionHom (fun n ↦ (e n).hom) h =
      (signCorrectionIso e h).hom := by
  ext n
  simp only [signCorrectionHom_app, signCorrectionIso_hom_app]

end CategoryTheory.Limits.SequentialSystem
