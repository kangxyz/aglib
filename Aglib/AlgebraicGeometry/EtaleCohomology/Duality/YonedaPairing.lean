/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.LowerShriekExt
public import Aglib.AlgebraicGeometry.EtaleCohomology.Coefficients.ModuleCohomology
public import Aglib.Algebra.Homology.DerivedCategory.Ext.YonedaPairing

/-!
# The Yoneda pairing of compactly supported cohomology with Ext

Let `j : U ⟶ X` be an étale morphism of schemes, for example the open immersion of a curve into
its complete model, and `Λ` a ring. For sheaves `F`, `G` of modules over the constant ring sheaf
`Λ_U`, write `H^r_c(U, F) = Ext^r(Λ_X, j_! F)`, computed among `Λ_X`-modules with the module
extension by zero `j_! = moduleLowerShriek j Λ`. The pairing
`H^r_c(U, F) × Ext^s(F, G) → H^{r+s}_c(U, G)` sends `(c, e)` to the Yoneda composite of `c`
with `j_! e`, in Mathlib's diagrammatic order: `c.comp (e.mapExactFunctor j_!)`, first `c`, then
`j_! e`. This is the pairing of Milne, *Lectures on Étale Cohomology* (v2.21), p. 103: an
`s`-extension of `F` by `G` is sent by `j_!` to an extension of `j_! F` by `j_! G`, which
defines the iterated boundary map `H^r(X, j_! F) → H^{r+s}(X, j_! G)`. Here Ext is Mathlib's
derived-category `Abelian.Ext` and the product is its Yoneda composition `Ext.comp`; no model of
Ext by classes of `s`-fold extensions is used. For `G = μ_n`, `Λ = ℤ/n` and `r + s = 2` it is
the pairing of Poincaré duality for curves (Milne LEC Thm 14.7, p. 93, and Thm 14.20, p. 101).
Milne omits the compatibilities proved here.

For a short exact sequence `S` on `U`, the long exact sequence of `H_c` is Mathlib's
`Ext.covariantSequence (moduleUnit X Λ) (shortExact_moduleLowerShriek j Λ hS)`, with connecting
map the postcomposition with the extension class of `j_! S`; the long exact sequence of
`Ext(-, G)` is `Ext.contravariantSequence hS G`, with connecting map the precomposition with the
extension class of `S`. `moduleLowerShriekCohomologyAddEquiv` identifies `H^r_c(U, F)` and these
connecting maps with `Sheaf.H` of the abelian extension by zero.

* `moduleLowerShriekPairingHom` is the pairing as a biadditive map.
* `moduleLowerShriekPairing_naturality`: for `u : F ⟶ F'`, `φ(u_* c, e') = φ(c, u^* e')`.
* `moduleLowerShriekPairing_extClass`: for a short exact sequence `0 → F' → F → F'' → 0` on `U`,
  `φ(δ c'', e') = φ(c'', δ e')`, sign `+1`, where `δ c''` is postcomposition with the
  extension class of `j_!` of the sequence (the connecting map of `H_c`) and `δ e'` is
  precomposition with the extension class of the sequence (the connecting map of Mathlib's
  `Ext.contravariantSequence`).
* `moduleLowerShriekPairing_δ`: against Mathlib's signed connecting map `Ext.δ`, normalized by
  `(-1)^(s+1)` on `Ext^s → Ext^(s+1)`, the sign is `ε = (-1)^(s+1)`:
  `φ(c'', Ext.δ e') = (-1)^(s+1) φ(δ c'', e')`.
* `moduleLowerShriekPairingDualHom` is the induced map `H^r_c(U, F) → Hom(Ext^{d-r}(F, G),
  H^d_c(U, G))` for `r ≤ d` (`d = 2` for curves); its squares against the long exact sequences
  are `moduleLowerShriekPairingDualHom_naturality`, `_extClass` (sign `+1`) and `_δ` (sign
  `(-1)^(d-r)`).

No condition on `j`, `X` or `Λ` beyond étaleness of `j` is used; `HasExt` is a size hypothesis
and the Ext universes on `U` and `X` are independent. The groups carry no `Λ`-module structure
from Mathlib here (the module-sheaf categories have no `Linear` instance), so bilinearity is
biadditivity.
-/

@[expose] public noncomputable section

universe w w' u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] (Λ : Type (u + 1)) [Ring Λ]
  [HasExt.{w} (ModuleSheaf U Λ)] [HasExt.{w'} (ModuleSheaf X Λ)]

/-- The Yoneda pairing `H^r_c(U, F) × Ext^s(F, G) → H^t_c(U, G)` for `r + s = t`: the
composite of `c` with `j_! e`, first `c`, then `j_! e`. -/
def moduleLowerShriekPairing {F G : ModuleSheaf U Λ} {r s t : ℕ}
    (c : Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) r) (e : Ext.{w} F G s)
    (h : r + s = t) : Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj G) t :=
  Functor.extPairing (moduleLowerShriek j Λ) (moduleUnit X Λ) c e h

theorem moduleLowerShriekPairing_def {F G : ModuleSheaf U Λ} {r s t : ℕ}
    (c : Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) r) (e : Ext.{w} F G s)
    (h : r + s = t) :
    moduleLowerShriekPairing j Λ c e h =
      c.comp (moduleLowerShriekExt j Λ F G s e) h :=
  rfl

/-- The pairing as a biadditive map. -/
def moduleLowerShriekPairingHom (F G : ModuleSheaf U Λ) (r s t : ℕ) (h : r + s = t) :
    Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) r →+
      Ext.{w} F G s →+ Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj G) t :=
  Functor.extPairingHom (moduleLowerShriek j Λ) (moduleUnit X Λ) F G r s t h

@[simp]
theorem moduleLowerShriekPairingHom_apply_apply (F G : ModuleSheaf U Λ) (r s t : ℕ)
    (h : r + s = t) (c : Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) r)
    (e : Ext.{w} F G s) :
    moduleLowerShriekPairingHom j Λ F G r s t h c e = moduleLowerShriekPairing j Λ c e h :=
  rfl

variable {j Λ}

section Biadditive

variable {F G : ModuleSheaf U Λ} {r s t : ℕ}

@[simp]
theorem moduleLowerShriekPairing_add_left
    (c₁ c₂ : Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) r) (e : Ext.{w} F G s)
    (h : r + s = t) :
    moduleLowerShriekPairing j Λ (c₁ + c₂) e h =
      moduleLowerShriekPairing j Λ c₁ e h + moduleLowerShriekPairing j Λ c₂ e h :=
  Functor.extPairing_add_left
    (L := moduleLowerShriek j Λ) (A := moduleUnit X Λ) c₁ c₂ e h

@[simp]
theorem moduleLowerShriekPairing_add_right
    (c : Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) r) (e₁ e₂ : Ext.{w} F G s)
    (h : r + s = t) :
    moduleLowerShriekPairing j Λ c (e₁ + e₂) h =
      moduleLowerShriekPairing j Λ c e₁ h + moduleLowerShriekPairing j Λ c e₂ h :=
  Functor.extPairing_add_right
    (L := moduleLowerShriek j Λ) (A := moduleUnit X Λ) c e₁ e₂ h

@[simp]
theorem moduleLowerShriekPairing_zero_left (e : Ext.{w} F G s) (h : r + s = t) :
    moduleLowerShriekPairing j Λ
      (0 : Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) r) e h = 0 :=
  Functor.extPairing_zero_left
    (L := moduleLowerShriek j Λ) (A := moduleUnit X Λ) e h

@[simp]
theorem moduleLowerShriekPairing_zero_right
    (c : Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) r) (h : r + s = t) :
    moduleLowerShriekPairing j Λ c (0 : Ext.{w} F G s) h = 0 :=
  Functor.extPairing_zero_right
    (L := moduleLowerShriek j Λ) (A := moduleUnit X Λ) c h

@[simp]
theorem moduleLowerShriekPairing_neg_left
    (c : Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) r) (e : Ext.{w} F G s)
    (h : r + s = t) :
    moduleLowerShriekPairing j Λ (-c) e h = -moduleLowerShriekPairing j Λ c e h :=
  Functor.extPairing_neg_left
    (L := moduleLowerShriek j Λ) (A := moduleUnit X Λ) c e h

@[simp]
theorem moduleLowerShriekPairing_neg_right
    (c : Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) r) (e : Ext.{w} F G s)
    (h : r + s = t) :
    moduleLowerShriekPairing j Λ c (-e) h = -moduleLowerShriekPairing j Λ c e h :=
  Functor.extPairing_neg_right
    (L := moduleLowerShriek j Λ) (A := moduleUnit X Λ) c e h

theorem moduleLowerShriekPairing_zsmul_right
    (c : Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) r) (m : ℤ)
    (e : Ext.{w} F G s) (h : r + s = t) :
    moduleLowerShriekPairing j Λ c (m • e) h = m • moduleLowerShriekPairing j Λ c e h :=
  Functor.extPairing_zsmul_right
    (L := moduleLowerShriek j Λ) (A := moduleUnit X Λ) c m e h

end Biadditive

/-- Naturality in the first variable: for `u : F ⟶ F'`, `φ(u_* c, e') = φ(c, u^* e')`, where
`u_* c` is postcomposition with `j_! u` and `u^* e'` is precomposition with `u`. -/
theorem moduleLowerShriekPairing_naturality {F F' G : ModuleSheaf U Λ} (u : F ⟶ F')
    {r s t : ℕ} (c : Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) r)
    (e' : Ext.{w} F' G s) (h : r + s = t) :
    moduleLowerShriekPairing j Λ
        (c.comp (Ext.mk₀ ((moduleLowerShriek j Λ).map u)) (add_zero r)) e' h =
      moduleLowerShriekPairing j Λ c ((Ext.mk₀ u).comp e' (zero_add s)) h :=
  Functor.extPairing_naturality
    (L := moduleLowerShriek j Λ) (A := moduleUnit X Λ) u c e' h

/-- Naturality in the second variable: for `v : G ⟶ G'`, `φ(c, v_* e) = (j_! v)_* φ(c, e)`. -/
theorem moduleLowerShriekPairing_comp_mk₀ {F G G' : ModuleSheaf U Λ} (v : G ⟶ G')
    {r s t : ℕ} (c : Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) r)
    (e : Ext.{w} F G s) (h : r + s = t) :
    moduleLowerShriekPairing j Λ c (e.comp (Ext.mk₀ v) (add_zero s)) h =
      (moduleLowerShriekPairing j Λ c e h).comp
        (Ext.mk₀ ((moduleLowerShriek j Λ).map v)) (add_zero t) :=
  Functor.extPairing_comp_mk₀
    (L := moduleLowerShriek j Λ) (A := moduleUnit X Λ) v c e h

/-- Compatibility with connecting maps, with sign `+1`. For a short exact sequence `S` on `U`,
the connecting map of `H_c` is postcomposition with the extension class of `j_! S`, and the
connecting map of `Ext(-, G)` is precomposition with the extension class of `S`:
`φ(δ c'', e') = φ(c'', δ e')`. -/
theorem moduleLowerShriekPairing_extClass {S : ShortComplex (ModuleSheaf U Λ)}
    (hS : S.ShortExact) {G : ModuleSheaf U Λ} {r r' s s' t : ℕ}
    (c : Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj S.X₃) r)
    (e : Ext.{w} S.X₁ G s) (hr : r + 1 = r') (hs : 1 + s = s') (h : r' + s = t)
    (h' : r + s' = t) :
    moduleLowerShriekPairing j Λ (c.comp (shortExact_moduleLowerShriek j Λ hS).extClass hr) e h =
      moduleLowerShriekPairing j Λ c (hS.extClass.comp e hs) h' :=
  Functor.extPairing_extClass
    (L := moduleLowerShriek j Λ) (A := moduleUnit X Λ) hS c e hr hs h h'

/-- Compatibility with Mathlib's signed connecting map `Ext.δ`, which is
`(-1)^s'` times the precomposition with the extension class on `Ext^s → Ext^s'`, `s + 1 = s'`:
`φ(c'', Ext.δ e') = (-1)^s' φ(δ c'', e')`, so `ε = (-1)^(s+1)`. -/
theorem moduleLowerShriekPairing_δ {S : ShortComplex (ModuleSheaf U Λ)}
    (hS : S.ShortExact) {G : ModuleSheaf U Λ} {r r' s s' t : ℕ}
    (c : Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj S.X₃) r)
    (e : Ext.{w} S.X₁ G s) (hr : r + 1 = r') (hs : s + 1 = s') (h : r' + s = t)
    (h' : r + s' = t) :
    moduleLowerShriekPairing j Λ c (Ext.δ hS s s' hs e) h' =
      (s' : ℤ).negOnePow •
        moduleLowerShriekPairing j Λ (c.comp (shortExact_moduleLowerShriek j Λ hS).extClass hr)
          e h :=
  Functor.extPairing_δ
    (L := moduleLowerShriek j Λ) (A := moduleUnit X Λ) hS c e hr hs h h'

section DualHom

variable (j Λ)

/-- The pairing into total degree `d`, as the homomorphism
`H^r_c(U, F) → Hom(Ext^{d-r}(F, G), H^d_c(U, G))`, for `r ≤ d`. -/
def moduleLowerShriekPairingDualHom (F G : ModuleSheaf U Λ) (d r : ℕ) (hr : r ≤ d) :
    Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) r →+
      Ext.{w} F G (d - r) →+ Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj G) d :=
  Functor.extPairingDualHom (moduleLowerShriek j Λ) (moduleUnit X Λ) F G d r hr

@[simp]
theorem moduleLowerShriekPairingDualHom_apply_apply (F G : ModuleSheaf U Λ) (d r : ℕ)
    (hr : r ≤ d) (c : Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) r)
    (e : Ext.{w} F G (d - r)) :
    moduleLowerShriekPairingDualHom j Λ F G d r hr c e =
      moduleLowerShriekPairing j Λ c e (by lia) :=
  rfl

variable {j Λ}

/-- The square of the dual homomorphism against a coefficient map `u : F ⟶ F'`:
`φ_{F'} ∘ u_* = (-) ∘ u^*` on `H^r_c(U, F)`. -/
theorem moduleLowerShriekPairingDualHom_naturality {F F' G : ModuleSheaf U Λ} (u : F ⟶ F')
    (d r : ℕ) (hr : r ≤ d) (c : Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) r) :
    moduleLowerShriekPairingDualHom j Λ F' G d r hr
        (c.comp (Ext.mk₀ ((moduleLowerShriek j Λ).map u)) (add_zero r)) =
      (moduleLowerShriekPairingDualHom j Λ F G d r hr c).comp
        ((Ext.mk₀ u).precomp G (zero_add (d - r))) :=
  Functor.extPairingDualHom_naturality
    (L := moduleLowerShriek j Λ) (A := moduleUnit X Λ) u d r hr c

/-- The square of the dual homomorphism against the connecting maps, sign `+1`: for a short
exact sequence `S` on `U` and `r + 1 ≤ d`, `φ_{S.X₁}(δ c'') = φ_{S.X₃}(c'') ∘ δ`, with `δ` on
`Ext(-, G)` the precomposition with the extension class of `S`. -/
theorem moduleLowerShriekPairingDualHom_extClass {S : ShortComplex (ModuleSheaf U Λ)}
    (hS : S.ShortExact) (G : ModuleSheaf U Λ) (d r : ℕ) (hr : r + 1 ≤ d)
    (c : Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj S.X₃) r) :
    moduleLowerShriekPairingDualHom j Λ S.X₁ G d (r + 1) hr
        (c.comp (shortExact_moduleLowerShriek j Λ hS).extClass rfl) =
      (moduleLowerShriekPairingDualHom j Λ S.X₃ G d r (by lia) c).comp
        (hS.extClass.precomp G (show 1 + (d - (r + 1)) = d - r by lia)) :=
  Functor.extPairingDualHom_extClass
    (L := moduleLowerShriek j Λ) (A := moduleUnit X Λ) hS G d r hr c

/-- The square of the dual homomorphism against Mathlib's signed connecting map `Ext.δ`:
`φ_{S.X₃}(c'') ∘ Ext.δ = (-1)^(d-r) φ_{S.X₁}(δ c'')`, for `r + 1 ≤ d`. -/
theorem moduleLowerShriekPairingDualHom_δ {S : ShortComplex (ModuleSheaf U Λ)}
    (hS : S.ShortExact) (G : ModuleSheaf U Λ) (d r : ℕ) (hr : r + 1 ≤ d)
    (c : Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj S.X₃) r) :
    (moduleLowerShriekPairingDualHom j Λ S.X₃ G d r (by lia) c).comp
        (Ext.δ hS (d - (r + 1)) (d - r) (by lia)) =
      ((d - r : ℕ) : ℤ).negOnePow •
        moduleLowerShriekPairingDualHom j Λ S.X₁ G d (r + 1) hr
          (c.comp (shortExact_moduleLowerShriek j Λ hS).extClass rfl) :=
  Functor.extPairingDualHom_δ
    (L := moduleLowerShriek j Λ) (A := moduleUnit X Λ) hS G d r hr c

end DualHom

end AlgebraicGeometry.Scheme.EtaleCohomology
