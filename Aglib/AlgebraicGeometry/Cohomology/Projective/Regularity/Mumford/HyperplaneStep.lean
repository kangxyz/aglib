/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Surjectivity
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Basic

/-!
# Mumford's hyperplane step

Let `0 → S.X₁ → F → F_H → 0` be a short exact sequence of coherent modules on projective
`n`-space over a field `k`, with `S.X₁ ≅ O(-1) ⊗ F`. In the application the first map is
multiplication by a linear form `h` that is a nonzerodivisor on `F`, and `F_H` is the hyperplane
section of `F`, kept on `P^n` (it is the pushforward of the restriction of `F` to `H = V(h)`).
If `F_H` is `m₀`-regular, then `F` is `(m₀ + h¹(F(m₀ - 1)))`-regular, and
`h¹(F(m₀ - 1)) = h⁰(F(m₀ - 1)) - χ(F(m₀ - 1))`; together, `F` is
`(m₀ + h⁰(F(m₀ - 1)) - χ(F(m₀ - 1)))`-regular (`IsProjectiveRegular.of_hyperplane_euler`).
This is the inductive step of Nitsure, arXiv:math/0504590v1, proof of Thm 2.3, pp. 12-13
(after Mumford, *Lectures on curves on an algebraic surface*). Here `F(r)` is the native tensor
twist `O(r) ⊗ F` and `hⁱ` is `projectiveCohomologyDim`.

The steps, all from the long exact sequences of the twisted sequences
`0 → O(r - 1) ⊗ F → O(r) ⊗ F → O(r) ⊗ F_H → 0`:
* `hyperplane_subsingleton_ge_two`: `Hⁱ(F(r)) = 0` for `i ≥ 2` and `r ≥ m₀ - i`, by descending
  from Serre vanishing through the isomorphisms `Hⁱ(F(r - 1)) ≅ Hⁱ(F(r))`;
* `hyperplane_dim_le`: for `r ≥ m₀ - 2` the map `H¹(F(r)) → H¹(F(r + 1))` is onto, and the
  dimensions agree exactly when `ν_{r+1} : H⁰(F(r + 1)) → H⁰(F_H(r + 1))` is onto; with Nitsure's
  Remark 2.2 (`TwistSectionsOnto.succ`, p. 11) this gives
* `hyperplane_dim_lt_or_eq_zero`: `h¹(F(r))` strictly decreases for `r ≥ m₀ - 1` until it
  vanishes, and `hyperplane_dim_sub_le` gives `h¹(F(m₀ - 1 + t)) ≤ h¹(F(m₀ - 1)) - t`.

The dimension steps are proved once for an arbitrary short exact sequence `T` of coherent
modules (`projectiveCohomologyDim_zero_le_of_shortExact`,
`projectiveCohomologyDim_one_le_of_shortExact`) and then instantiated at the twisted hyperplane
sequences. `IsProjectiveRegular.of_hyperplane_restrict` is the converse direction used for the
ambient modules (Nitsure, p. 10): if `F` is `m`-regular, so is `F_H`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-! ### Vanishing along hyperplane sequences -/

section Ring

variable {R : Type u} [CommRing R] {ι : Type u}

/-! ### Hyperplane sequences -/

variable (S : ShortComplex (ProjectiveSpace R ι).Modules)
  (φ : S.X₁ ≅ (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (-1))).obj S.X₂)

include φ in
/-- `Hᵠ(O(c) ⊗ S.X₁)` vanishes when `Hᵠ(O(c + -1) ⊗ S.X₂)` does. -/
theorem hyperplane_subsingleton_X₁ (c : ℤ) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (c + -1))).obj S.X₂))
        q)) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι c)).obj S.X₁)) q) :=
  moduleCohomology_subsingleton_of_iso
    ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι c)).mapIso φ).symm q
    (twistCohomology_subsingleton_comp R ι rfl h)

include φ in
/-- `Hᵠ(O(c + -1) ⊗ S.X₂)` vanishes when `Hᵠ(O(c) ⊗ S.X₁)` does. -/
theorem hyperplane_subsingleton_of_X₁ (c : ℤ) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι c)).obj S.X₁)) q)) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (c + -1))).obj S.X₂))
        q) :=
  twistCohomology_subsingleton_of_comp R ι rfl (moduleCohomology_subsingleton_of_iso
    ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι c)).mapIso φ) q h)

include φ in
/-- **Restriction keeps regularity** (Nitsure, arXiv:math/0504590v1, p. 10): in a hyperplane
sequence `0 → O(-1) ⊗ F → F → F_H → 0`, if `F` is `m`-regular then so is `F_H`. -/
theorem IsProjectiveRegular.of_hyperplane_restrict (hS : S.ShortExact) {m : ℤ}
    (hF : IsProjectiveRegular R ι S.X₂ m) : IsProjectiveRegular R ι S.X₃ m := by
  intro q hq
  have hT := tensor_shortExact_finiteLocallyFree (twistingSheaf R ι (m - q)) S hS
  apply moduleCohomology_subsingleton_X₃ _ hT q (hF q hq)
  have h := twistCohomology_subsingleton_congr R ι
    (show m - ((q + 1 : ℕ) : ℤ) = m - q + -1 by push_cast; ring) (hF (q + 1) (by omega))
  exact hyperplane_subsingleton_X₁ S φ (m - q) (q + 1) h

include φ in
/-- One step down: if `F_H` is `m₀`-regular and `H^{q+2}(F(r + 1)) = 0` with `r ≥ m₀ - (q + 2)`,
then `H^{q+2}(F(r)) = 0`. -/
theorem hyperplane_subsingleton_of_succ (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hS : S.ShortExact) (h₃ : affineLocallyFiniteType (ProjectiveSpace R ι) S.X₃) {m₀ : ℤ}
    (hreg : IsProjectiveRegular R ι S.X₃ m₀) (q : ℕ) (r : ℤ) (hr : m₀ ≤ r + ((q : ℤ) + 2))
    (h : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (r + 1))).obj S.X₂))
        (q + 2))) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι r)).obj S.X₂))
        (q + 2)) := by
  have hT := tensor_shortExact_finiteLocallyFree (twistingSheaf R ι (r + 1)) S hS
  have h3 := IsProjectiveRegular.subsingleton_of_le_add n e h₃ (s := r + 1) (q := q + 1) hreg
    (by omega) (by push_cast; omega)
  have h1 := moduleCohomology_subsingleton_X₁ _ hT (q + 1) h3 h
  have h1' := hyperplane_subsingleton_of_X₁ S φ (r + 1) (q + 2) h1
  exact twistCohomology_subsingleton_congr R ι (by ring) h1'

include φ in
/-- **Higher vanishing** (Nitsure, arXiv:math/0504590v1, p. 12): in a hyperplane sequence with
`F` affine-locally of finite type and `F_H` `m₀`-regular, `Hⁱ(F(r)) = 0` for every `i ≥ 2` and
`r ≥ m₀ - i`. -/
theorem hyperplane_subsingleton_ge_two [IsNoetherianRing R] (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hS : S.ShortExact) (h₂ : affineLocallyFiniteType (ProjectiveSpace R ι) S.X₂)
    (h₃ : affineLocallyFiniteType (ProjectiveSpace R ι) S.X₃) {m₀ : ℤ}
    (hreg : IsProjectiveRegular R ι S.X₃ m₀) (q : ℕ) (r : ℤ) (hr : m₀ ≤ r + ((q : ℤ) + 2)) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι r)).obj S.X₂))
        (q + 2)) := by
  obtain ⟨B, hB⟩ := projectiveSerreVanishing R ι n e S.X₂ h₂
  suffices H : ∀ t : ℕ, ∀ r : ℤ, m₀ ≤ r + ((q : ℤ) + 2) → (B : ℤ) ≤ r + t →
      Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι r)).obj S.X₂))
          (q + 2)) from H (B - r).toNat r hr (by omega)
  intro t
  induction t with
  | zero =>
    intro r _ hrB
    exact hB r (by simpa using hrB) (q + 2) (by omega)
  | succ t ih =>
    intro r hr hrB
    exact hyperplane_subsingleton_of_succ S φ n e hS h₃ hreg q r hr
      (ih (r + 1) (by omega) (by push_cast at hrB ⊢; omega))

end Ring

/-! ### Dimension counting over a field -/

section Field

variable {k : Type u} [Field k] {ι : Type u}

/-- In a short exact sequence `T` with `H¹(T.X₁) = 0` and coherent `T.X₂`, the map
`H⁰(T.X₂) → H⁰(T.X₃)` is onto, so `h⁰(T.X₃) ≤ h⁰(T.X₂)`. -/
theorem projectiveCohomologyDim_zero_le_of_shortExact (n : ℕ) (e : ι ≃ Fin (n + 1))
    (T : ShortComplex (ProjectiveSpace k ι).Modules) (hT : T.ShortExact)
    (h₂ : affineLocallyFiniteType (ProjectiveSpace k ι) T.X₂)
    (h1 : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace k ι) T.X₁) (0 + 1))) :
    projectiveCohomologyDim k ι T.X₃ 0 ≤ projectiveCohomologyDim k ι T.X₂ 0 := by
  let X := ProjectiveSpace k ι
  let α := projectiveConstants k ι
  let := moduleCohomologyModuleOfHom X α T.X₂ 0
  let := moduleCohomologyModuleOfHom X α T.X₃ 0
  let := moduleCohomologyModuleOfHom X α T.X₁ (0 + 1)
  have hex := moduleCohomologyConnectingOfHom_exact_left X α T hT 0
  have hsurj : Function.Surjective (moduleCohomologyMapOfHom X α T.g 0) := fun z =>
    (hex z).mp (Subsingleton.elim _ _)
  exact projectiveCohomologyDim_le_of_surjective n e T.g 0 h₂ hsurj

/-- In a short exact sequence `T` of coherent modules with `H¹(T.X₃) = 0`, the map
`H¹(T.X₁) → H¹(T.X₂)` is onto, so `h¹(T.X₂) ≤ h¹(T.X₁)`, with equality exactly when `T.g` is
surjective on global sections. -/
theorem projectiveCohomologyDim_one_le_of_shortExact (n : ℕ) (e : ι ≃ Fin (n + 1))
    (T : ShortComplex (ProjectiveSpace k ι).Modules) (hT : T.ShortExact)
    (h₁ : affineLocallyFiniteType (ProjectiveSpace k ι) T.X₁)
    (h₂ : affineLocallyFiniteType (ProjectiveSpace k ι) T.X₂)
    (h3 : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace k ι) T.X₃) 1)) :
    projectiveCohomologyDim k ι T.X₂ 1 ≤ projectiveCohomologyDim k ι T.X₁ 1 ∧
      (projectiveCohomologyDim k ι T.X₂ 1 = projectiveCohomologyDim k ι T.X₁ 1 ↔
        Function.Surjective (T.g.val.app (op ⊤))) := by
  let X := ProjectiveSpace k ι
  let α := projectiveConstants k ι
  let := moduleCohomologyModuleOfHom X α T.X₁ 1
  let := moduleCohomologyModuleOfHom X α T.X₂ 1
  let := moduleCohomologyModuleOfHom X α T.X₃ 1
  have hex := moduleCohomologyMapOfHom_exact X α T hT 1
  have hsurj : Function.Surjective (moduleCohomologyMapOfHom X α T.f 1) := fun z =>
    (hex z).mp (Subsingleton.elim _ _)
  refine ⟨projectiveCohomologyDim_le_of_surjective n e T.f 1 h₁ hsurj, ?_⟩
  exact (projectiveCohomologyDim_eq_iff_injective n e T.f 1 h₁ h₂ hsurj).trans
    ((moduleCohomologyConnectingOfHom_eq_zero_iff_injective α T hT 0).symm.trans
      ⟨surjective_of_moduleCohomologyConnectingOfHom_zero_eq_zero α T hT,
        moduleCohomologyConnectingOfHom_zero_eq_zero_of_surjective α T hT⟩)

variable (S : ShortComplex (ProjectiveSpace k ι).Modules)
  (φ : S.X₁ ≅ (moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (-1))).obj S.X₂)

include φ in
/-- `hᵠ(O(c) ⊗ S.X₁) = hᵠ(O(c + -1) ⊗ S.X₂)`. -/
theorem hyperplane_dim_X₁ (c : ℤ) (q : ℕ) :
    projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι c)).obj S.X₁) q =
      projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (c + -1))).obj S.X₂)
          q := by
  rw [projectiveCohomologyDim_congr k ι
    ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι c)).mapIso φ) q]
  have h := projectiveCohomologyDim_congr k ι ((twistingTensorCompIso k ι c (-1)).app S.X₂) q
  simpa only [Functor.comp_obj] using h

include φ in
/-- If `H¹(F(r - 1)) = 0`, the restriction `H⁰(F(r)) → H⁰(F_H(r))` is onto, so
`h⁰(F_H(r)) ≤ h⁰(F(r))`. -/
theorem hyperplane_dim_zero_le (n : ℕ) (e : ι ≃ Fin (n + 1)) (hS : S.ShortExact)
    (h₂ : affineLocallyFiniteType (ProjectiveSpace k ι) S.X₂) (r : ℤ)
    (h1 : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace k ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (r + -1))).obj S.X₂))
        1)) :
    projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι r)).obj S.X₃) 0 ≤
      projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι r)).obj S.X₂) 0 := by
  have : Finite ι := Finite.of_equiv _ e.symm
  exact projectiveCohomologyDim_zero_le_of_shortExact n e
    (S.map (moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι r)))
    (tensor_shortExact_finiteLocallyFree (twistingSheaf k ι r) S hS)
    (twistingTensor_affineLocallyFiniteType k ι r S.X₂ h₂)
    (hyperplane_subsingleton_X₁ S φ r 1 h1)

variable (n : ℕ) (e : ι ≃ Fin (n + 1)) (hS : S.ShortExact)
  (h₂ : affineLocallyFiniteType (ProjectiveSpace k ι) S.X₂)
  (h₃ : affineLocallyFiniteType (ProjectiveSpace k ι) S.X₃)
  {m₀ : ℤ} (hreg : IsProjectiveRegular k ι S.X₃ m₀)

include φ n e hS h₂ h₃ hreg in
/-- For `r ≥ m₀ - 2` the map `H¹(F(r)) → H¹(F(r + 1))` is onto, so
`h¹(F(r + 1)) ≤ h¹(F(r))`, with equality exactly when `O(r + 1) ⊗ S.g` is surjective on global
sections (Nitsure, arXiv:math/0504590v1, p. 12). -/
theorem hyperplane_dim_le (c : ℤ) (hc : m₀ ≤ c + 2) :
    projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (c + 1))).obj S.X₂) 1 ≤
      projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι c)).obj S.X₂) 1 ∧
    (projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (c + 1))).obj S.X₂) 1 =
      projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι c)).obj S.X₂) 1 ↔
      TwistSectionsOnto k ι S.g (c + 1)) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have h₁ : affineLocallyFiniteType (ProjectiveSpace k ι) S.X₁ :=
    (affineLocallyFiniteType (ProjectiveSpace k ι)).prop_of_iso φ.symm
      (twistingTensor_affineLocallyFiniteType k ι (-1) S.X₂ h₂)
  have hcore : projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (c + 1))).obj S.X₂) 1 ≤
      projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (c + 1))).obj S.X₁) 1 ∧
    (projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (c + 1))).obj S.X₂) 1 =
      projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (c + 1))).obj S.X₁) 1 ↔
      TwistSectionsOnto k ι S.g (c + 1)) :=
    projectiveCohomologyDim_one_le_of_shortExact n e
      (S.map (moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (c + 1))))
      (tensor_shortExact_finiteLocallyFree (twistingSheaf k ι (c + 1)) S hS)
      (twistingTensor_affineLocallyFiniteType k ι (c + 1) S.X₁ h₁)
      (twistingTensor_affineLocallyFiniteType k ι (c + 1) S.X₂ h₂)
      (IsProjectiveRegular.subsingleton_of_le_add n e h₃ (s := c + 1) (q := 1) hreg one_pos
        (by push_cast; omega))
  have hd₁ := hyperplane_dim_X₁ S φ (c + 1) 1
  rw [show c + 1 + -1 = c by ring] at hd₁
  rwa [hd₁] at hcore

include φ n e hS h₂ h₃ hreg in
/-- **Strict decrease** (Nitsure, arXiv:math/0504590v1, p. 12): for `r ≥ m₀ - 1`, either
`h¹(F(r + 1)) < h¹(F(r))` or `h¹(F(r)) = 0`. If the dimensions agree, `ν_{r+1}` is onto, hence
every `ν_j`, `j ≥ r + 1`, is onto (Remark 2.2), so `h¹(F(j))` is constant for `j ≥ r` and
vanishes by Serre vanishing. -/
theorem hyperplane_dim_lt_or_eq_zero (c : ℤ) (hc : m₀ ≤ c + 1) :
    projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (c + 1))).obj S.X₂) 1 <
      projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι c)).obj S.X₂) 1 ∨
    projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι c)).obj S.X₂) 1 = 0 := by
  let := Fintype.ofEquiv (Fin (n + 1)) e.symm
  have : S.X₃.IsQuasicoherent := quasicoherent_of_affineCharts _ (fun A j _ => (h₃ A j).1)
  obtain ⟨B, hB⟩ := projectiveSerreVanishing k ι n e S.X₂ h₂
  rcases (hyperplane_dim_le S φ n e hS h₂ h₃ hreg c (by omega)).1.lt_or_eq with hlt | heq
  · exact Or.inl hlt
  · right
    have hon : TwistSectionsOnto k ι S.g (c + 1) :=
      ((hyperplane_dim_le S φ n e hS h₂ h₃ hreg c (by omega)).2).mp heq
    have hall (t : ℕ) : TwistSectionsOnto k ι S.g (c + 1 + t) := by
      induction t with
      | zero => exact hon.congr (by simp)
      | succ t ih =>
        exact (TwistSectionsOnto.succ n e S.g hreg (by omega) ih).congr (by push_cast; ring)
    have hconst (t : ℕ) : projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (c + t))).obj S.X₂) 1 =
        projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι c)).obj S.X₂) 1 := by
      induction t with
      | zero => simp
      | succ t ih =>
        have h := ((hyperplane_dim_le S φ n e hS h₂ h₃ hreg (c + t) (by omega)).2).mpr
          ((hall t).congr (by ring))
        rw [show c + ((t + 1 : ℕ) : ℤ) = c + t + 1 by push_cast; ring, h, ih]
    rw [← hconst (B - c).toNat]
    exact projectiveCohomologyDim_eq_zero_of_subsingleton (hB _ (by omega) 1 one_ne_zero)

include φ n e hS h₂ h₃ hreg in
/-- `h¹(F(m₀ - 1 + t)) ≤ h¹(F(m₀ - 1)) - t` for every `t : ℕ`. -/
theorem hyperplane_dim_sub_le (t : ℕ) :
    projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (m₀ - 1 + t))).obj
          S.X₂) 1 ≤
      projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (m₀ - 1))).obj
          S.X₂) 1 - t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show m₀ - 1 + ((t + 1 : ℕ) : ℤ) = m₀ - 1 + t + 1 by push_cast; ring]
    have h := hyperplane_dim_lt_or_eq_zero S φ n e hS h₂ h₃ hreg (m₀ - 1 + t) (by omega)
    have hle := (hyperplane_dim_le S φ n e hS h₂ h₃ hreg (m₀ - 1 + t) (by omega)).1
    omega

include φ n e hS h₂ h₃ hreg in
/-- **Mumford's step** (Nitsure, arXiv:math/0504590v1, proof of Thm 2.3, pp. 12-13): in a
hyperplane sequence `0 → O(-1) ⊗ F → F → F_H → 0` of coherent modules over a field, if `F_H`
is `m₀`-regular then `F` is `(m₀ + h¹(F(m₀ - 1)))`-regular. -/
theorem IsProjectiveRegular.of_hyperplane :
    IsProjectiveRegular k ι S.X₂ (m₀ + projectiveCohomologyDim k ι
      ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (m₀ - 1))).obj S.X₂)
        1) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  intro q hq
  obtain ⟨q, rfl⟩ | rfl : (∃ q' : ℕ, q = q' + 2) ∨ q = 1 := by
    rcases q with _ | _ | q
    · omega
    · exact Or.inr rfl
    · exact Or.inl ⟨q, rfl⟩
  · exact hyperplane_subsingleton_ge_two S φ n e hS h₂ h₃ hreg q _ (by push_cast; omega)
  · set d := projectiveCohomologyDim k ι
      ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (m₀ - 1))).obj S.X₂) 1
    have h := hyperplane_dim_sub_le S φ n e hS h₂ h₃ hreg d
    rw [Nat.sub_self, Nat.le_zero] at h
    have hs := subsingleton_of_projectiveCohomologyDim_eq_zero n e
      (twistingTensor_affineLocallyFiniteType k ι _ S.X₂ h₂) h
    exact twistCohomology_subsingleton_congr k ι (by push_cast; ring) hs

include φ n e hS h₂ h₃ hreg in
/-- `h¹(F(m₀ - 1)) = h⁰(F(m₀ - 1)) - χ(F(m₀ - 1))`, since `Hⁱ(F(m₀ - 1)) = 0` for `i ≥ 2`
(Nitsure, arXiv:math/0504590v1, p. 13). -/
theorem hyperplane_dim_one_eq :
    (projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (m₀ - 1))).obj S.X₂)
          1 : ℤ) =
      projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (m₀ - 1))).obj S.X₂)
          0 - projectiveHilbertFunction k ι S.X₂ (m₀ - 1) := by
  have hsupp : (Function.support fun q : ℕ => (-1 : ℤ) ^ q * (projectiveCohomologyDim k ι
      ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (m₀ - 1))).obj S.X₂)
        q : ℤ)) ⊆ (Finset.range 2 : Set ℕ) := by
    intro q hq
    by_contra hq2
    apply hq
    obtain ⟨q, rfl⟩ : ∃ q' : ℕ, q = q' + 2 := ⟨q - 2, by
      simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hq2
      omega⟩
    dsimp only
    rw [projectiveCohomologyDim_eq_zero_of_subsingleton
      (hyperplane_subsingleton_ge_two S φ n e hS h₂ h₃ hreg q (m₀ - 1) (by omega)),
      Nat.cast_zero, mul_zero]
  unfold projectiveHilbertFunction projectiveEulerChar
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_range_succ, Finset.sum_range_one]
  ring

include φ n e hS h₂ h₃ hreg in
/-- **Mumford's step with the Euler characteristic** (Nitsure, arXiv:math/0504590v1, proof of
Thm 2.3, pp. 12-13): in a hyperplane sequence of coherent modules over a field, if `F_H` is
`m₀`-regular then `F` is `(m₀ + h⁰(F(m₀ - 1)) - χ(F(m₀ - 1)))`-regular. -/
theorem IsProjectiveRegular.of_hyperplane_euler :
    IsProjectiveRegular k ι S.X₂ (m₀ + projectiveCohomologyDim k ι
      ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (m₀ - 1))).obj S.X₂)
        0 - projectiveHilbertFunction k ι S.X₂ (m₀ - 1)) := by
  have h := IsProjectiveRegular.of_hyperplane S φ n e hS h₂ h₃ hreg
  have he := hyperplane_dim_one_eq S φ n e hS h₂ h₃ hreg
  rwa [he, ← add_sub_assoc] at h

end Field

end AlgebraicGeometry.Scheme.Cohomology
