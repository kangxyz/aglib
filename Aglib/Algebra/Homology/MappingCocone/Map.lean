/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# Original mapping-cocone maps and zero-homotopy lifts

The map is the original cone map shifted by minus one. Projection equations
retain its strict chain-level naturality, including the native cocone signs.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

namespace mappingCone

@[reassoc (attr := simp)]
lemma map_f_fst_v {K L K' L' : CochainComplex C ℤ}
    (φ : K ⟶ L) (ψ : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : φ ≫ b = a ≫ ψ) (p q : ℤ) (hpq : p + 1 = q) :
    (map φ ψ a b h).f p ≫ (fst ψ).1.v p q hpq =
      (fst φ).1.v p q hpq ≫ a.f q := by
  apply ext_from φ q p hpq
  · simp [map]
  · simp [map]

@[reassoc (attr := simp)]
lemma map_f_snd_v {K L K' L' : CochainComplex C ℤ}
    (φ : K ⟶ L) (ψ : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : φ ≫ b = a ≫ ψ) (p : ℤ) :
    (map φ ψ a b h).f p ≫ (snd ψ).v p p (add_zero p) =
      (snd φ).v p p (add_zero p) ≫ b.f p := by
  apply ext_from φ (p + 1) p rfl
  · simp [map]
  · simp [map]

end mappingCone

namespace mappingCocone

/-- The original cone-square map, with the native minus-one shift. -/
def map {K L K' L' : CochainComplex C ℤ}
    (φ : K ⟶ L) (ψ : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : φ ≫ b = a ≫ ψ) : mappingCocone φ ⟶ mappingCocone ψ :=
  (mappingCone.map φ ψ a b h)⟦(-1 : ℤ)⟧'

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma map_fst {K L K' L' : CochainComplex C ℤ}
    (φ : K ⟶ L) (ψ : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : φ ≫ b = a ≫ ψ) :
    map φ ψ a b h ≫ fst ψ = fst φ ≫ a := by
  ext n
  simp [map, fst, HomComplex.Cocycle.leftShift, HomComplex.Cocycle.homOf,
    HomComplex.Cochain.leftShift, shiftFunctorObjXIso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma map_f_snd_v {K L K' L' : CochainComplex C ℤ}
    (φ : K ⟶ L) (ψ : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : φ ≫ b = a ≫ ψ) (n : ℤ) :
    (map φ ψ a b h).f n ≫ (snd ψ).v n (n + -1) rfl =
      (snd φ).v n (n + -1) rfl ≫ b.f (n + -1) := by
  simp [map, snd, HomComplex.Cochain.leftShift, shiftFunctorObjXIso]

/-- The two original cocone projections determine an actual component map. -/
lemma ext_to_term {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ) {A : C}
    {a b : A ⟶ (mappingCocone φ).X n}
    (hf : a ≫ (fst φ).f n = b ≫ (fst φ).f n)
    (hs : a ≫ (snd φ).v n (n + -1) rfl = b ≫ (snd φ).v n (n + -1) rfl) :
    a = b := by
  calc
    a = a ≫ ((fst φ).f n ≫ (inl φ).v n n (add_zero n) +
        (snd φ).v n (n + -1) rfl ≫ (inr φ).1.v (n + -1) n (by lia)) := by
      rw [id_X]; simp
    _ = b ≫ ((fst φ).f n ≫ (inl φ).v n n (add_zero n) +
        (snd φ).v n (n + -1) rfl ≫ (inr φ).1.v (n + -1) n (by lia)) := by
      simp only [Preadditive.comp_add, ← Category.assoc, hf, hs]
    _ = b := by rw [id_X]; simp

/-- Strict naturality of the original zero-homotopy cocone lift. -/
lemma lift_zero_naturality {M K L M' K' L' : CochainComplex C ℤ}
    (φ : K ⟶ L) (ψ : K' ⟶ L') (u : M ⟶ K) (u' : M' ⟶ K')
    (hu : u ≫ φ = 0) (hu' : u' ≫ ψ = 0)
    (m : M ⟶ M') (a : K ⟶ K') (b : L ⟶ L')
    (h : φ ≫ b = a ≫ ψ) (hm : m ≫ u' = u ≫ a) :
    m ≫ lift ψ u' 0 (by simp [hu']) =
      lift φ u 0 (by simp [hu]) ≫ map φ ψ a b h := by
  ext n
  apply ext_to_term ψ n
  · have hn := congrArg (fun f => f.f n) (map_fst φ ψ a b h)
    simp only [HomologicalComplex.comp_f] at hn
    simpa [Category.assoc, hn, ← HomologicalComplex.comp_f] using
      congrArg (fun f => f.f n) hm
  · simp [Category.assoc]

end mappingCocone
end CochainComplex
