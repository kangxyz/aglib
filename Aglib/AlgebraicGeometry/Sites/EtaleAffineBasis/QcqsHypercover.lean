/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.FiniteRefinement
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Sites.Hypercover.One

/-!
# Finite affine one-hypercovers of qcqs étale objects

This is the finite diagram needed to recover sections over a non-affine qcqs
scheme from affine evaluations. The target remains an object of the original
small étale site, rather than being identified with an affine-site object.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

/-- Fibre products of compact étale objects over a quasi-separated target
have compact underlying schemes. -/
theorem compactSpace_etale_pullback {S : Scheme.{u}} {U V W : S.Etale}
    [CompactSpace V.left] [CompactSpace W.left] [QuasiSeparatedSpace U.left]
    (f : V ⟶ U) (g : W ⟶ U) : CompactSpace (pullback f g).left := by
  let : Category (MorphismProperty.Over
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ AlgebraicGeometry.Etale f) ⊤ S) :=
    inferInstanceAs (Category S.Etale)
  let F₀ : S.Etale ⥤ Over S := MorphismProperty.Over.forget
    (fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ AlgebraicGeometry.Etale f) ⊤ S
  let : PreservesFiniteLimits F₀ :=
    MorphismProperty.Over.instPreservesFiniteLimitsTopOverForget
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ AlgebraicGeometry.Etale f) S
  let F : S.Etale ⥤ Scheme.{u} := F₀ ⋙ Over.forget S
  have : PreservesLimit (cospan f g) F := by
    dsimp only [F]
    infer_instance
  let e : (pullback f g).left ≅ pullback f.left g.left :=
    PreservesPullback.iso F f g
  exact e.hom.homeomorph.symm.compactSpace

/-- Every covering sieve of a qcqs small étale object contains a finite
one-hypercover whose object and relation components are affine. -/
theorem exists_finite_affine_oneHypercover {S : Scheme.{u}} (U : S.Etale)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (R : Sieve U) (hR : R ∈ S.smallEtaleTopology U) :
    ∃ (E : S.smallEtaleTopology.OneHypercover.{u} U),
      Finite E.I₀ ∧ (∀ i j, Finite (E.I₁ i j)) ∧
      (∀ i, IsAffine (E.X i).left) ∧
      (∀ i j (k : E.I₁ i j), IsAffine (E.Y k).left) ∧ E.sieve₀ ≤ R := by
  classical
  obtain ⟨ι, hfin, V, f, hV, hf, hcov⟩ := exists_finite_affine_family U R hR
  have (i : ι) : IsAffine (V i).left := hV i
  have (i j : ι) : CompactSpace (pullback (f i) (f j)).left :=
    compactSpace_etale_pullback (f i) (f j)
  choose I hI W g hW hg hcover using fun i j ↦
    exists_finite_affine_family (pullback (f i) (f j)) ⊤
      (S.smallEtaleTopology.top_mem _)
  let E : PreOneHypercover.{u} U :=
    { I₀ := ι
      X := V
      f := f
      I₁ := I
      Y := fun {i j} k ↦ W i j k
      p₁ := fun {i j} k ↦ g i j k ≫ pullback.fst (f i) (f j)
      p₂ := fun {i j} k ↦ g i j k ≫ pullback.snd (f i) (f j)
      w := fun {_ _} _ ↦ by simp only [Category.assoc, pullback.condition] }
  have hrel (i j : ι) : E.sieve₁' i j ∈ S.smallEtaleTopology _ := by
    have heq : E.sieve₁' i j = Sieve.ofArrows (W i j) (g i j) := by
      unfold PreOneHypercover.sieve₁'
      congr 1
      funext k
      apply pullback.hom_ext
      · exact E.toPullback_fst k
      · exact E.toPullback_snd k
    rw [heq]
    exact hcover i j
  refine ⟨GrothendieckTopology.OneHypercover.mk' E hcov hrel,
    hfin, hI, hV, hW, ?_⟩
  intro W a ha
  obtain ⟨i, b, rfl⟩ := (Sieve.mem_ofArrows_iff V f a).mp ha
  exact R.downward_closed (hf i) b

end AlgebraicGeometry.Scheme.EtaleAffineBasis
