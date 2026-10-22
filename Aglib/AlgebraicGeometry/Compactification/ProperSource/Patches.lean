/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Basic
public import Aglib.AlgebraicGeometry.Compactification.ProperSource.FiniteCover
public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence.LocalLift
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.CommonEnlargement.Finite

/-!
# Compactification from an actual finite patch family

The separated patches are enlarged by recorded sequences. Their maps from an
open cover of a proper scheme lift through these sequences and glue after an
actual common refinement. The resulting proper surjective source proves the
common enlargement proper, without changing the original scheme.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Compactification

/-- An actual finite patch family with a proper covering model compactifies the
original scheme. Density in the original scheme is topological; schematic
density is required only for the original source in the proper covering model. -/
theorem exists_compactification_of_patch_family
    {X S P : Scheme.{u}} [IsNoetherian P]
    (p : X ⟶ S) (U : X.Opens) (hU : Dense (U : Set X))
    (pP : P ⟶ S) [IsProper pP] (c : U.toScheme ⟶ P)
    [IsOpenImmersion c] [IsSchemeTheoreticallyDominant c]
    (n : ℕ) (O : Fin (n + 1) → P.Opens) (hO : iSup O = ⊤)
    (M : Fin (n + 1) → Scheme.{u}) (pM : ∀ i, M i ⟶ S)
    (x : ∀ i, X ⟶ M i)
    [∀ i, IsNoetherian (M i)] [∀ i, IsSeparated (pM i)]
    [∀ i, QuasiCompact (pM i)] [∀ i, LocallyOfFiniteType (pM i)]
    [∀ i, IsOpenImmersion (x i)] [∀ i, IsSchemeTheoreticallyDominant (x i)]
    (hx : ∀ i, x i ≫ pM i = p)
    (k : ∀ i, (O i).toScheme ⟶ M i)
    (hk : ∀ i, k i ≫ pM i = (O i).ι ≫ pP)
    (a : ∀ i, U.toScheme ⟶ (O i).toScheme)
    (ha : ∀ i, a i ≫ (O i).ι = c)
    (hak : ∀ i, a i ≫ k i = U.ι ≫ x i) :
    Nonempty (p.Compactification) := by
  classical
  obtain ⟨E⟩ := QuasiDomination.exists_finite_common_enlargement n M pM p x hx
  let : IsSeparated E.pM := E.separated
  let : LocallyOfFiniteType E.pM := E.locallyOfFiniteType
  let : IsOpenImmersion E.common := E.common_open
  let : IsSchemeTheoreticallyDominant E.common := E.common_dense
  let : IsNoetherian E.M := E.noetherian
  let V := c.opensRange
  let : IsSchemeTheoreticallyDominant V.ι := by
    rw [← c.isoOpensRange_inv_comp]
    infer_instance
  let g : V.toScheme ⟶ E.M := c.isoOpensRange.inv ≫ U.ι ≫ E.common
  have hdU : DenseRange U.ι := by
    simpa only [DenseRange, Opens.range_ι] using hU
  have hdg : DenseRange g := by
    change DenseRange (E.common ∘ U.ι ∘ c.isoOpensRange.inv)
    exact E.common.denseRange.comp
      (hdU.comp c.isoOpensRange.inv.denseRange U.ι.continuous) E.common.continuous
  let C := P.openCoverOfIsOpenCover O (.mk hO)
  let : Finite C.I₀ := inferInstanceAs (Finite (Fin (n + 1)))
  let s : ∀ i, ((O i).ι ⁻¹ᵁ V).toScheme ⟶ U.toScheme := fun i ↦
    ((O i).ι ∣_ V) ≫ c.isoOpensRange.inv
  have hs : ∀ i, s i ≫ a i = ((O i).ι ⁻¹ᵁ V).ι := by
    intro i
    apply (cancel_mono (O i).ι).mp
    rw [Category.assoc, ha]
    dsimp only [s, V]
    rw [Category.assoc, c.isoOpensRange_inv_comp, morphismRestrict_ι]
  let gi : ∀ i, ((O i).ι ⁻¹ᵁ V).toScheme ⟶ X := fun i ↦ s i ≫ U.ι
  have hgi : ∀ i, gi i ≫ x i = ((O i).ι ⁻¹ᵁ V).ι ≫ k i := by
    intro i
    dsimp only [gi]
    rw [Category.assoc, ← hak, ← Category.assoc, hs]
  have hlift := fun i ↦ Blowup.AdmissibleSequence.exists_local_lift (x i)
    (E.sequence i) (k i) ((O i).ι ⁻¹ᵁ V) (gi i) (hgi i)
    (E.original i) (E.original_base i) (E.chart i) E.common (E.original_common i)
  choose B γ b hγ hb hagree using hlift
  let F : ∀ i, B i ⟶ E.M := fun i ↦ b i ≫ E.chart i
  have hbase : ∀ i, F i ≫ E.pM = γ i ≫ (O i).ι ≫ pP := by
    intro i
    dsimp only [F]
    rw [Category.assoc, E.chart_over, ← Category.assoc (b i), hb,
      Category.assoc, hk]
  have hprotected : ∀ i, (γ i ⁻¹ᵁ (O i).ι ⁻¹ᵁ V).ι ≫ F i =
      (γ i ∣_ (O i).ι ⁻¹ᵁ V) ≫ ((O i).ι ∣_ V) ≫ g := by
    intro i
    change (γ i ⁻¹ᵁ (O i).ι ⁻¹ᵁ V).ι ≫ (b i ≫ E.chart i) = _
    rw [hagree i]
    simp only [gi, s, g, Category.assoc]
  obtain ⟨_, _, _, _, _, _, _, _, _, hpE, _, _, _⟩ :=
    exists_proper_surjective_of_finite_local_sequences C V pP E.pM g hdg
      B γ hγ F hbase hprotected
  exact ⟨{
    Xbar := E.M
    j := E.common
    p := E.pM
    isOpenImmersion_j := E.common_open
    isProper_p := hpE
    fac := E.common_over }⟩

end AlgebraicGeometry.Scheme.Compactification
