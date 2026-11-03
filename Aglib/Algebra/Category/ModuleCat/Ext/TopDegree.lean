/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.MinimalFiniteFreeResolution
public import Aglib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.Nakayama

/-!
# Top Ext detects finite projective dimension over a local ring

For a finite module with projective dimension at most `n + 1`, vanishing of
its original Ext in degree `n + 1` against any finite nonzero coefficient
lowers the bound to `n`. The bounded minimal finite free resolution is
constructed from the native projective-dimension bound. Nakayama's lemma
and the original resolution cocycle criterion detect a nonzero top term.

Consequently a finite module of finite projective dimension with vanishing
positive self-Ext is projective. Finite projective dimension is essential
input here; neither it nor canonical-module freeness is inferred from a
name or a supplied duality equivalence.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing

universe u w

namespace ModuleCat

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [HasExt.{w} (ModuleCat.{u} R)]

/-- Vanishing of the top possible Ext against a finite nonzero module lowers
an actual finite projective-dimension bound over a Noetherian local ring. -/
theorem hasProjectiveDimensionLE_of_top_ext_subsingleton
    (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N] [Nontrivial N]
    (n : ℕ) [HasProjectiveDimensionLE M (n + 1)]
    (hExt : Subsingleton (Ext.{w} M N (n + 1))) : HasProjectiveDimensionLE M n := by
  classical
  obtain ⟨P, _hfinite, hfree, hzero, hminimal⟩ :=
    exists_minimal_finite_free_resolution M (n + 1)
  have htop : IsZero (P.complex.X (n + 1)) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    by_contra h
    let : Nontrivial (P.complex.X (n + 1)) := not_subsingleton_iff_nontrivial.mp h
    let : Module.Free R (P.complex.X (n + 1)) := hfree (n + 1)
    let b := Module.Free.chooseBasis R (P.complex.X (n + 1))
    obtain ⟨i⟩ := b.index_nonempty
    have hproper : (⊤ : Submodule R N) ≠ maximalIdeal R • ⊤ :=
      Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (maximalIdeal_le_jacobson _)
    obtain ⟨x, hx⟩ := SetLike.exists_not_mem_of_ne_top
      (maximalIdeal R • (⊤ : Submodule R N)) (Ne.symm hproper)
    let f : P.complex.X (n + 1) ⟶ N := ModuleCat.ofHom (b.constr R (fun _ => x))
    have hf : P.complex.d (n + 1 + 1) (n + 1) ≫ f = 0 :=
      (hzero (n + 1 + 1) (by omega)).eq_of_src _ _
    have he : P.extMk f (n + 1 + 1) rfl hf = (0 : Ext.{w} M N (n + 1)) :=
      hExt.elim _ _
    obtain ⟨g, hg⟩ := (P.extMk_eq_zero_iff f (n + 1 + 1) rfl hf n rfl).mp he
    have hd : P.complex.d (n + 1) n (b i) ∈
        maximalIdeal R • (⊤ : Submodule R (P.complex.X n)) :=
      hminimal n ⟨b i, rfl⟩
    have hmem : g (P.complex.d (n + 1) n (b i)) ∈
        maximalIdeal R • (⊤ : Submodule R N) :=
      Submodule.smul_top_le_comap_smul_top (maximalIdeal R) g.hom hd
    have hvalue : g (P.complex.d (n + 1) n (b i)) = x := by
      have hgi := ConcreteCategory.congr_hom hg (b i)
      change g (P.complex.d (n + 1) n (b i)) = (b.constr R (fun _ => x)) (b i) at hgi
      exact hgi.trans (b.constr_basis R (fun _ => x) i)
    exact hx (hvalue ▸ hmem)
  apply P.hasProjectiveDimensionLE_of_isZero_X n
  intro i hi
  by_cases h : i = n + 1
  · simpa only [h] using htop
  · exact hzero i (by omega)

/-- Positive self-Ext vanishing forces a finite module of finite projective
dimension over a Noetherian local ring to be projective. The zero module is
allowed; the finite dimension bound remains an explicit native hypothesis. -/
theorem projective_of_self_ext_subsingleton
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) [HasProjectiveDimensionLE M n]
    (hExt : ∀ i : ℕ, 0 < i → Subsingleton (Ext.{w} M M i)) : Projective M := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · exact (ModuleCat.isZero_iff_subsingleton.mpr hM).projective
  · let : Nontrivial M := hM
    have hbound : ∀ m : ℕ, HasProjectiveDimensionLE M m → Projective M := by
      intro m
      induction m with
      | zero =>
        intro hm
        exact projective_iff_hasProjectiveDimensionLT_one.mpr hm
      | succ m ih =>
        intro hm
        let : HasProjectiveDimensionLE M (m + 1) := hm
        exact ih (hasProjectiveDimensionLE_of_top_ext_subsingleton M M m
          (hExt (m + 1) (by omega)))
    exact hbound n inferInstance

end ModuleCat
