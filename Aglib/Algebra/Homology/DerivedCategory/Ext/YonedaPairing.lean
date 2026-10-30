/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Yoneda pairings through an exact functor

For an exact additive functor `L : C ⥤ D` between abelian categories and `A : D`,
the pairing sends `(c, e)` to `c.comp (e.mapExactFunctor L)`. It is biadditive,
natural in both coefficients, and respects the original connecting extension classes.
The contravariant connecting map `Ext.δ` has sign `(-1)^(s+1)` on degree `s`;
the total-degree dual square has sign `(-1)^(d-r)`. Both curried directions and
all three squares use this same pairing. The Ext universes are independent.

Sources: Mathlib `Ext/Map.lean`, `mapExactFunctor_comp` and `mapExactFunctor_extClass`;
`Ext/ExactSequences.lean`, `Ext.δ`. These are the categorical arguments previously
specialized in the etale `Duality/YonedaPairing` and `Duality/PairingTranspose` leaves.
No injective presentation, derived-category choice, or linear-category instance is required.
-/

@[expose] public noncomputable section

universe w w' u v u' v'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] (A : D)

/-- The Yoneda pairing `Ext^r(A, L F) × Ext^s(F, G) → Ext^t(A, L G)` for `r + s = t`: the
composite of `c` with `L e`, first `c`, then `L e`. -/
def extPairing {F G : C} {r s t : ℕ}
    (c : Ext.{w'} A (L.obj F) r) (e : Ext.{w} F G s)
    (h : r + s = t) : Ext.{w'} A (L.obj G) t :=
  c.comp (e.mapExactFunctor L) h

theorem extPairing_def {F G : C} {r s t : ℕ}
    (c : Ext.{w'} A (L.obj F) r) (e : Ext.{w} F G s)
    (h : r + s = t) :
    extPairing L A c e h =
      c.comp (L.mapExtAddHom F G s e) h :=
  rfl

/-- The pairing as a biadditive map. -/
def extPairingHom (F G : C) (r s t : ℕ) (h : r + s = t) :
    Ext.{w'} A (L.obj F) r →+
      Ext.{w} F G s →+ Ext.{w'} A (L.obj G) t :=
  (Ext.bilinearComp A (L.obj F)
    (L.obj G) r s t h).compl₂ (L.mapExtAddHom F G s)

@[simp]
theorem extPairingHom_apply_apply (F G : C) (r s t : ℕ)
    (h : r + s = t) (c : Ext.{w'} A (L.obj F) r)
    (e : Ext.{w} F G s) :
    extPairingHom L A F G r s t h c e = extPairing L A c e h :=
  rfl

variable {L A}

section Biadditive

variable {F G : C} {r s t : ℕ}

@[simp]
theorem extPairing_add_left
    (c₁ c₂ : Ext.{w'} A (L.obj F) r) (e : Ext.{w} F G s)
    (h : r + s = t) :
    extPairing L A (c₁ + c₂) e h =
      extPairing L A c₁ e h + extPairing L A c₂ e h :=
  Ext.add_comp _ _ _ h

@[simp]
theorem extPairing_add_right
    (c : Ext.{w'} A (L.obj F) r) (e₁ e₂ : Ext.{w} F G s)
    (h : r + s = t) :
    extPairing L A c (e₁ + e₂) h =
      extPairing L A c e₁ h + extPairing L A c e₂ h :=
  _root_.map_add (extPairingHom L A F G r s t h c) e₁ e₂

@[simp]
theorem extPairing_zero_left (e : Ext.{w} F G s) (h : r + s = t) :
    extPairing L A
      (0 : Ext.{w'} A (L.obj F) r) e h = 0 :=
  Ext.zero_comp _ _ _ _ h

@[simp]
theorem extPairing_zero_right
    (c : Ext.{w'} A (L.obj F) r) (h : r + s = t) :
    extPairing L A c (0 : Ext.{w} F G s) h = 0 :=
  _root_.map_zero (extPairingHom L A F G r s t h c)

@[simp]
theorem extPairing_neg_left
    (c : Ext.{w'} A (L.obj F) r) (e : Ext.{w} F G s)
    (h : r + s = t) :
    extPairing L A (-c) e h = -extPairing L A c e h :=
  Ext.neg_comp _ _ h

@[simp]
theorem extPairing_neg_right
    (c : Ext.{w'} A (L.obj F) r) (e : Ext.{w} F G s)
    (h : r + s = t) :
    extPairing L A c (-e) h = -extPairing L A c e h :=
  _root_.map_neg (extPairingHom L A F G r s t h c) e

theorem extPairing_zsmul_right
    (c : Ext.{w'} A (L.obj F) r) (m : ℤ)
    (e : Ext.{w} F G s) (h : r + s = t) :
    extPairing L A c (m • e) h = m • extPairing L A c e h :=
  _root_.map_zsmul (extPairingHom L A F G r s t h c) m e

end Biadditive

/-- Naturality in the first variable: for `u : F ⟶ F'`, `φ(u_* c, e') = φ(c, u^* e')`, where
`u_* c` is postcomposition with `L u` and `u^* e'` is precomposition with `u`. -/
theorem extPairing_naturality {F F' G : C} (u : F ⟶ F')
    {r s t : ℕ} (c : Ext.{w'} A (L.obj F) r)
    (e' : Ext.{w} F' G s) (h : r + s = t) :
    extPairing L A
        (c.comp (Ext.mk₀ (L.map u)) (add_zero r)) e' h =
      extPairing L A c ((Ext.mk₀ u).comp e' (zero_add s)) h := by
  rw [extPairing, extPairing, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.comp_assoc c _ _ (add_zero r) (zero_add s) (by lia)]

/-- Naturality in the second variable: for `v : G ⟶ G'`, `φ(c, v_* e) = (L v)_* φ(c, e)`. -/
theorem extPairing_comp_mk₀ {F G G' : C} (v : G ⟶ G')
    {r s t : ℕ} (c : Ext.{w'} A (L.obj F) r)
    (e : Ext.{w} F G s) (h : r + s = t) :
    extPairing L A c (e.comp (Ext.mk₀ v) (add_zero s)) h =
      (extPairing L A c e h).comp
        (Ext.mk₀ (L.map v)) (add_zero t) := by
  rw [extPairing, extPairing, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.comp_assoc c _ _ h (add_zero s) (by lia)]

/-- Compatibility with connecting maps, with sign `+1`. For a short exact sequence `S` in `C`,
the connecting map of `Ext(A, L(-))` is postcomposition with the extension class of `L S`, and the
connecting map of `Ext(-, G)` is precomposition with the extension class of `S`:
`φ(δ c'', e') = φ(c'', δ e')`. -/
theorem extPairing_extClass {S : ShortComplex (C)}
    (hS : S.ShortExact) {G : C} {r r' s s' t : ℕ}
    (c : Ext.{w'} A (L.obj S.X₃) r)
    (e : Ext.{w} S.X₁ G s) (hr : r + 1 = r') (hs : 1 + s = s') (h : r' + s = t)
    (h' : r + s' = t) :
    extPairing L A (c.comp (hS.map_of_exact L).extClass hr) e h =
      extPairing L A c (hS.extClass.comp e hs) h' := by
  rw [extPairing, extPairing, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass, Ext.comp_assoc c _ _ hr hs (by lia)]

/-- Compatibility with Mathlib's signed connecting map `Ext.δ`, which is
`(-1)^s'` times the precomposition with the extension class on `Ext^s → Ext^s'`, `s + 1 = s'`:
`φ(c'', Ext.δ e') = (-1)^s' φ(δ c'', e')`, so `ε = (-1)^(s+1)`. -/
theorem extPairing_δ {S : ShortComplex (C)}
    (hS : S.ShortExact) {G : C} {r r' s s' t : ℕ}
    (c : Ext.{w'} A (L.obj S.X₃) r)
    (e : Ext.{w} S.X₁ G s) (hr : r + 1 = r') (hs : s + 1 = s') (h : r' + s = t)
    (h' : r + s' = t) :
    extPairing L A c (Ext.δ hS s s' hs e) h' =
      (s' : ℤ).negOnePow •
        extPairing L A (c.comp (hS.map_of_exact L).extClass hr)
          e h := by
  rw [extPairing_extClass hS c e hr (by lia) h h', Ext.δ_apply, Units.smul_def,
    Units.smul_def, extPairing_zsmul_right]

section DualHom

variable (L A)

/-- The pairing into total degree `d`, as the homomorphism
`Ext^r(A, L F) → Hom(Ext^{d-r}(F, G), Ext^d(A, L G))`, for `r ≤ d`. -/
def extPairingDualHom (F G : C) (d r : ℕ) (hr : r ≤ d) :
    Ext.{w'} A (L.obj F) r →+
      Ext.{w} F G (d - r) →+ Ext.{w'} A (L.obj G) d :=
  extPairingHom L A F G r (d - r) d (by lia)

@[simp]
theorem extPairingDualHom_apply_apply (F G : C) (d r : ℕ)
    (hr : r ≤ d) (c : Ext.{w'} A (L.obj F) r)
    (e : Ext.{w} F G (d - r)) :
    extPairingDualHom L A F G d r hr c e =
      extPairing L A c e (by lia) :=
  rfl

variable {L A}

/-- The square of the dual homomorphism against a coefficient map `u : F ⟶ F'`:
`φ_{F'} ∘ u_* = (-) ∘ u^*` on `Ext^r(A, L F)`. -/
theorem extPairingDualHom_naturality {F F' G : C} (u : F ⟶ F')
    (d r : ℕ) (hr : r ≤ d) (c : Ext.{w'} A (L.obj F) r) :
    extPairingDualHom L A F' G d r hr
        (c.comp (Ext.mk₀ (L.map u)) (add_zero r)) =
      (extPairingDualHom L A F G d r hr c).comp
        ((Ext.mk₀ u).precomp G (zero_add (d - r))) := by
  ext e'
  exact extPairing_naturality u c e' (by lia)

/-- The square of the dual homomorphism against the connecting maps, sign `+1`: for a short
exact sequence `S` in `C` and `r + 1 ≤ d`, `φ_{S.X₁}(δ c'') = φ_{S.X₃}(c'') ∘ δ`, with `δ` on
`Ext(-, G)` the precomposition with the extension class of `S`. -/
theorem extPairingDualHom_extClass {S : ShortComplex (C)}
    (hS : S.ShortExact) (G : C) (d r : ℕ) (hr : r + 1 ≤ d)
    (c : Ext.{w'} A (L.obj S.X₃) r) :
    extPairingDualHom L A S.X₁ G d (r + 1) hr
        (c.comp (hS.map_of_exact L).extClass rfl) =
      (extPairingDualHom L A S.X₃ G d r (by lia) c).comp
        (hS.extClass.precomp G (show 1 + (d - (r + 1)) = d - r by lia)) := by
  ext e'
  exact extPairing_extClass hS c e' rfl (by lia) (by lia) (by lia)

/-- The square of the dual homomorphism against Mathlib's signed connecting map `Ext.δ`:
`φ_{S.X₃}(c'') ∘ Ext.δ = (-1)^(d-r) φ_{S.X₁}(δ c'')`, for `r + 1 ≤ d`. -/
theorem extPairingDualHom_δ {S : ShortComplex (C)}
    (hS : S.ShortExact) (G : C) (d r : ℕ) (hr : r + 1 ≤ d)
    (c : Ext.{w'} A (L.obj S.X₃) r) :
    (extPairingDualHom L A S.X₃ G d r (by lia) c).comp
        (Ext.δ hS (d - (r + 1)) (d - r) (by lia)) =
      ((d - r : ℕ) : ℤ).negOnePow •
        extPairingDualHom L A S.X₁ G d (r + 1) hr
          (c.comp (hS.map_of_exact L).extClass rfl) := by
  ext e'
  exact extPairing_δ hS c e' rfl (by lia) (by lia) (by lia)

end DualHom


variable (L A)

/-- The transposed pairing into total degree `d`:
`Ext^s(F, G) → Hom(Ext^{d-s}(A, L F), Ext^d(A, L G))`, `e ↦ (c ↦ φ(c, e))`, for `s ≤ d`. -/
def extPairingTransposeHom (F G : C) (d s : ℕ) (hs : s ≤ d) :
    Ext.{w} F G s →+
      Ext.{w'} A (L.obj F) (d - s) →+
        Ext.{w'} A (L.obj G) d :=
  (extPairingHom L A F G (d - s) s d (by lia)).flip

@[simp]
theorem extPairingTransposeHom_apply_apply (F G : C) (d s : ℕ)
    (hs : s ≤ d) (e : Ext.{w} F G s)
    (c : Ext.{w'} A (L.obj F) (d - s)) :
    extPairingTransposeHom L A F G d s hs e c =
      extPairing L A c e (by lia) :=
  rfl

variable {L A}

/-- The square of the transposed map against a coefficient map `u : F ⟶ F'`:
`ψ_F(u^* e') = ψ_{F'}(e') ∘ u_*`, where `u^*` is precomposition with `u` and `u_*` is
postcomposition with `L u`. -/
theorem extPairingTransposeHom_naturality {F F' G : C} (u : F ⟶ F')
    (d s : ℕ) (hs : s ≤ d) (e' : Ext.{w} F' G s) :
    extPairingTransposeHom L A F G d s hs ((Ext.mk₀ u).comp e' (zero_add s)) =
      (extPairingTransposeHom L A F' G d s hs e').comp
        ((Ext.mk₀ (L.map u)).postcomp A
          (add_zero (d - s))) := by
  ext c
  exact (extPairing_naturality u c e' (by lia)).symm

/-- The square of the transposed map against the connecting maps, sign `+1`: for a short exact
sequence `S` in `C` and `s + 1 ≤ d`, `ψ_{S.X₃}(δ e') = ψ_{S.X₁}(e') ∘ δ`,
with `δ e'` the
precomposition with the extension class of `S` and `δ` on `Ext(A, L(-))` the postcomposition with
the
extension class of `L S`. -/
theorem extPairingTransposeHom_extClass {S : ShortComplex (C)}
    (hS : S.ShortExact) (G : C) (d s : ℕ) (hs : s + 1 ≤ d)
    (e' : Ext.{w} S.X₁ G s) :
    extPairingTransposeHom L A S.X₃ G d (s + 1) hs
        (hS.extClass.comp e' (add_comm 1 s)) =
      (extPairingTransposeHom L A S.X₁ G d s (by lia) e').comp
        ((hS.map_of_exact L).extClass.postcomp A
          (show d - (s + 1) + 1 = d - s by lia)) := by
  ext c
  exact (extPairing_extClass hS c e' (by lia) (add_comm 1 s) (by lia)
    (by lia)).symm

/-- The square of the transposed map against Mathlib's signed connecting map `Ext.δ`:
`ψ_{S.X₃}(Ext.δ e') = (-1)^(s+1) ψ_{S.X₁}(e') ∘ δ`, for `s + 1 ≤ d`. -/
theorem extPairingTransposeHom_δ {S : ShortComplex (C)}
    (hS : S.ShortExact) (G : C) (d s : ℕ) (hs : s + 1 ≤ d)
    (e' : Ext.{w} S.X₁ G s) :
    extPairingTransposeHom L A S.X₃ G d (s + 1) hs (Ext.δ hS s (s + 1) rfl e') =
      ((s + 1 : ℕ) : ℤ).negOnePow •
        (extPairingTransposeHom L A S.X₁ G d s (by lia) e').comp
          ((hS.map_of_exact L).extClass.postcomp A
            (show d - (s + 1) + 1 = d - s by lia)) := by
  ext c
  exact extPairing_δ hS c e' (by lia) rfl (by lia) (by lia)


end CategoryTheory.Functor
