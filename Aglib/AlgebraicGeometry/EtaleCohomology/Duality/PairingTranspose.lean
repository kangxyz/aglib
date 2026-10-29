/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.YonedaPairing

/-!
# The transposed duality map

Let `j : U ⟶ X` be an étale morphism of schemes and `Λ` a ring, and write
`H^r_c(U, F) = Ext^r(Λ_X, j_! F)` as in `Duality/YonedaPairing`. For `s ≤ d`, the pairing
`H^{d-s}_c(U, F) × Ext^s(F, G) → H^d_c(U, G)` induces

`moduleLowerShriekPairingTransposeHom : Ext^s(F, G) → Hom(H^{d-s}_c(U, F), H^d_c(U, G))`,

`e ↦ (c ↦ φ(c, e))`. For `G = μ_n`, `Λ = ℤ/n` and `d = 2`, followed by the trace
`H^2_c(U, μ_n) ≅ ℤ/n` (not constructed here), this is the direction of Milne's map
`ψ^r(U, F) : H^r(U, F) → T^r(U, F) = H^{2-r}_c(U, F^∨(1))^∨` (Milne, *Lectures on Étale
Cohomology* v2.21, Thm. 14.7, proof, p. 94), written for the coefficient `F' = F^∨(1)` with
`Ext^r(F', μ_n)` in place of `H^r(U, F)` (for locally constant `F'`, Lemma 14.21, p. 102).

Its squares against the long exact sequences of `Ext(-, G)` and of `H_c`, for a short exact
sequence `0 → F' → F → F'' → 0` on `U`, are:

* `moduleLowerShriekPairingTransposeHom_naturality`: for `u : F ⟶ F'`,
  `ψ_F(u^* e') = ψ_{F'}(e') ∘ u_*`;
* `moduleLowerShriekPairingTransposeHom_extClass`, sign `+1`: `ψ_{F''}(δ e') = ψ_{F'}(e') ∘ δ`,
  where `δ e'` is the precomposition with the extension class of the sequence (the connecting
  map of Mathlib's `Ext.contravariantSequence`) and `δ` on `H_c` is the postcomposition with the
  extension class of its extension by zero;
* `moduleLowerShriekPairingTransposeHom_δ`, against Mathlib's signed `Ext.δ`:
  `ψ_{F''}(Ext.δ e') = (-1)^(s+1) ψ_{F'}(e') ∘ δ` for `e' ∈ Ext^s(F', G)`.

No condition on `j`, `X` or `Λ` beyond étaleness of `j` is used; `HasExt` is a size hypothesis.
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

/-- The transposed pairing into total degree `d`:
`Ext^s(F, G) → Hom(H^{d-s}_c(U, F), H^d_c(U, G))`, `e ↦ (c ↦ φ(c, e))`, for `s ≤ d`. -/
def moduleLowerShriekPairingTransposeHom (F G : ModuleSheaf U Λ) (d s : ℕ) (hs : s ≤ d) :
    Ext.{w} F G s →+
      Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) (d - s) →+
        Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj G) d :=
  (moduleLowerShriekPairingHom j Λ F G (d - s) s d (by lia)).flip

@[simp]
theorem moduleLowerShriekPairingTransposeHom_apply_apply (F G : ModuleSheaf U Λ) (d s : ℕ)
    (hs : s ≤ d) (e : Ext.{w} F G s)
    (c : Ext.{w'} (moduleUnit X Λ) ((moduleLowerShriek j Λ).obj F) (d - s)) :
    moduleLowerShriekPairingTransposeHom j Λ F G d s hs e c =
      moduleLowerShriekPairing j Λ c e (by lia) :=
  rfl

variable {j Λ}

/-- The square of the transposed map against a coefficient map `u : F ⟶ F'`:
`ψ_F(u^* e') = ψ_{F'}(e') ∘ u_*`, where `u^*` is precomposition with `u` and `u_*` is
postcomposition with `j_! u`. -/
theorem moduleLowerShriekPairingTransposeHom_naturality {F F' G : ModuleSheaf U Λ} (u : F ⟶ F')
    (d s : ℕ) (hs : s ≤ d) (e' : Ext.{w} F' G s) :
    moduleLowerShriekPairingTransposeHom j Λ F G d s hs ((Ext.mk₀ u).comp e' (zero_add s)) =
      (moduleLowerShriekPairingTransposeHom j Λ F' G d s hs e').comp
        ((Ext.mk₀ ((moduleLowerShriek j Λ).map u)).postcomp (moduleUnit X Λ)
          (add_zero (d - s))) := by
  ext c
  exact (moduleLowerShriekPairing_naturality u c e' (by lia)).symm

/-- The square of the transposed map against the connecting maps, sign `+1`: for a short exact
sequence `S` on `U` and `s + 1 ≤ d`, `ψ_{S.X₃}(δ e') = ψ_{S.X₁}(e') ∘ δ`, with `δ e'` the
precomposition with the extension class of `S` and `δ` on `H_c` the postcomposition with the
extension class of `j_! S`. -/
theorem moduleLowerShriekPairingTransposeHom_extClass {S : ShortComplex (ModuleSheaf U Λ)}
    (hS : S.ShortExact) (G : ModuleSheaf U Λ) (d s : ℕ) (hs : s + 1 ≤ d)
    (e' : Ext.{w} S.X₁ G s) :
    moduleLowerShriekPairingTransposeHom j Λ S.X₃ G d (s + 1) hs
        (hS.extClass.comp e' (add_comm 1 s)) =
      (moduleLowerShriekPairingTransposeHom j Λ S.X₁ G d s (by lia) e').comp
        ((shortExact_moduleLowerShriek j Λ hS).extClass.postcomp (moduleUnit X Λ)
          (show d - (s + 1) + 1 = d - s by lia)) := by
  ext c
  exact (moduleLowerShriekPairing_extClass hS c e' (by lia) (add_comm 1 s) (by lia)
    (by lia)).symm

/-- The square of the transposed map against Mathlib's signed connecting map `Ext.δ`:
`ψ_{S.X₃}(Ext.δ e') = (-1)^(s+1) ψ_{S.X₁}(e') ∘ δ`, for `s + 1 ≤ d`. -/
theorem moduleLowerShriekPairingTransposeHom_δ {S : ShortComplex (ModuleSheaf U Λ)}
    (hS : S.ShortExact) (G : ModuleSheaf U Λ) (d s : ℕ) (hs : s + 1 ≤ d)
    (e' : Ext.{w} S.X₁ G s) :
    moduleLowerShriekPairingTransposeHom j Λ S.X₃ G d (s + 1) hs (Ext.δ hS s (s + 1) rfl e') =
      ((s + 1 : ℕ) : ℤ).negOnePow •
        (moduleLowerShriekPairingTransposeHom j Λ S.X₁ G d s (by lia) e').comp
          ((shortExact_moduleLowerShriek j Λ hS).extClass.postcomp (moduleUnit X Λ)
            (show d - (s + 1) + 1 = d - s by lia)) := by
  ext c
  exact moduleLowerShriekPairing_δ hS c e' (by lia) rfl (by lia) (by lia)

end AlgebraicGeometry.Scheme.EtaleCohomology
