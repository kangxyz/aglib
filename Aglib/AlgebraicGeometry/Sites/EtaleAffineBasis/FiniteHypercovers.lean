/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.Sites.Hypercover.IsSheaf

/-!
# Finite generating hypercovers of the affine étale site

Compactness of an affine target gives finite subfamilies inside every covering
sieve. Pullbacks in the original affine étale category then provide singleton
relation covers. Thus finite one-hypercovers generate the original induced
topology, without imposing compactness on the entire small étale site.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

/-- A sieve on the affine étale site covers exactly when the corresponding
family of underlying scheme maps is jointly surjective. -/
theorem affine_ofArrows_mem_iff {S : Scheme.{u}} {U : S.AffineEtale}
    {ι : Type*} {V : ι → S.AffineEtale} (f : ∀ i, V i ⟶ U) :
    Sieve.ofArrows V f ∈ Scheme.AffineEtale.topology S U ↔
      ⋃ i, Set.range ((Scheme.AffineEtale.Spec S).map (f i)).left = Set.univ := by
  change Sieve.ofArrows V f ∈
    (Scheme.AffineEtale.Spec S).inducedTopology S.smallEtaleTopology U ↔ _
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense,
    Sieve.functorPushforward_ofArrows]
  exact Scheme.ofArrows_mem_smallEtaleTopology_iff _

/-- Every covering sieve of the native affine étale site contains a finite
covering family of its own arrows. -/
theorem exists_finite_affine_site_family {S : Scheme.{u}} (U : S.AffineEtale)
    (R : Sieve U) (hR : R ∈ Scheme.AffineEtale.topology S U) :
    ∃ (ι : Type (u + 1)) (_ : Finite ι) (V : ι → S.AffineEtale)
      (f : ∀ i, V i ⟶ U), (∀ i, R (f i)) ∧
        Sieve.ofArrows V f ∈ Scheme.AffineEtale.topology S U := by
  classical
  obtain ⟨I, V, f, hRf⟩ := R.exists_eq_ofArrows
  have : CompactSpace ((Scheme.AffineEtale.Spec S).obj U).left := by
    change CompactSpace (Spec U.left.unop)
    infer_instance
  have hcov := (affine_ofArrows_mem_iff f).mp (hRf ▸ hR)
  let g (i : I) := ((Scheme.AffineEtale.Spec S).map (f i)).left
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i ↦ Set.range (g i)) (fun i ↦ (g i).isOpenMap.isOpen_range)
    (show Set.univ ⊆ ⋃ i, Set.range (g i) by rw [hcov])
  refine ⟨t, inferInstance, fun i ↦ V i, fun i ↦ f i, ?_, ?_⟩
  · intro i
    rw [hRf]
    exact Sieve.ofArrows_mk V f i
  · apply (affine_ofArrows_mem_iff _).mpr
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩

/-- The family of one-hypercovers with finite object and relation index types. -/
def finiteOneHypercoverFamily (S : Scheme.{u}) :
    (Scheme.AffineEtale.topology S).OneHypercoverFamily.{u + 1} :=
  fun {_} E ↦ Finite E.I₀ ∧ ∀ i j, Finite (E.I₁ i j)

/-- Finite one-hypercovers generate the original affine étale topology. -/
instance finiteOneHypercoverFamily_isGenerating (S : Scheme.{u}) :
    (finiteOneHypercoverFamily S).IsGenerating where
  le {U} R hR := by
    obtain ⟨ι, hfin, V, f, hf, hcov⟩ := exists_finite_affine_site_family U R hR
    let E : (Scheme.AffineEtale.topology S).OneHypercover.{u + 1} U :=
      { I₀ := ι
        X := V
        f := f
        I₁ := fun _ _ ↦ PUnit
        Y := fun {i j} _ ↦ pullback (f i) (f j)
        p₁ := fun {i j} _ ↦ pullback.fst (f i) (f j)
        p₂ := fun {i j} _ ↦ pullback.snd (f i) (f j)
        w := fun {_ _} _ ↦ pullback.condition
        mem₀ := hcov
        mem₁ := by
          intro i j W p₁ p₂ hw
          apply (Scheme.AffineEtale.topology S).superset_covering
            (S := ⊤) ?_ ((Scheme.AffineEtale.topology S).top_mem W)
          intro Z g _
          exact ⟨PUnit.unit, g ≫ pullback.lift p₁ p₂ hw,
            by simp only [Category.assoc, pullback.lift_fst],
            by simp only [Category.assoc, pullback.lift_snd]⟩ }
    refine ⟨E, ⟨hfin, fun _ _ ↦ inferInstance⟩, ?_⟩
    intro W g hg
    obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff V f g).mp hg
    exact R.downward_closed (hf i) a

end AlgebraicGeometry.Scheme.EtaleAffineBasis
