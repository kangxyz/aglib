/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Projectivity.Graph

/-! # Dimension of an actual projective-line rational graph

The native graph image of a rational map from an integral Noetherian scheme
to the projective line has dimension at most that of its source. On every
original polynomial product chart, the actual graph has a nonzero
cleared-denominator relation. The dimension drop for this relation cancels
the one polynomial variable. No dimension-one hypothesis is used.

The existing `Curves.Projectivity.Graph` leaf owns the canonical product
charts and graph maps used here. Those declarations have general scheme
statements; this extension reuses them without introducing alternate maps
or consuming the dimension-one graph conclusion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Polynomial

namespace AlgebraicGeometry.Scheme

open OverField OverField.Curve.Projectivity ProjectiveLine.TwoChart

universe u

/-- The actual scheme-theoretic graph of a rational map to the projective line
does not increase dimension. The source may have any finite or infinite
Krull dimension, and the original open domain may be empty. -/
theorem rationalGraphImage_topologicalKrullDim_le
    {k : Type u} [Field k] (X : FScheme k)
    [IsIntegral X.left] [IsNoetherian X.left]
    (U : X.left.Opens) (r : U.toScheme ⟶ twoChartLine (.of k))
    (hr : U.ι ≫ X.hom = r ≫ projection (.of k)) :
    topologicalKrullDim (rationalGraphImage X (Over.mk (projection (.of k))) U r hr).left ≤
      topologicalKrullDim X.left := by
  let P : FScheme k := Over.mk (projection (.of k))
  let g := rationalGraph X P U r hr
  let I := {V : X.left.affineOpens // Nonempty V.1} × Bool
  let W : I → g.image.Opens := fun i =>
    g.imageι ⁻¹ᵁ (graphProductChart X i.1.val i.2 ''ᵁ ⊤)
  have hcover : iSup W = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨V, b, z, hz⟩ := graphProductChart_cover X (g.imageι y)
    have hV : Nonempty V.1 :=
      ⟨V.2.isoSpec.inv ((Spec.map (CommRingCat.ofHom
        (C : Γ(X.left, V.1) →+* Γ(X.left, V.1)[X]))) z)⟩
    apply Opens.mem_iSup.mpr
    exact ⟨(⟨V, hV⟩, b), z, by trivial, hz⟩
  let 𝒰 := g.image.openCoverOfIsOpenCover W hcover
  apply topologicalKrullDim_le_of_openCover 𝒰 (topologicalKrullDim X.left)
  rintro ⟨⟨V, hV⟩, b⟩
  let : Nonempty V.1 := hV
  let A := Γ(X.left, V.1)
  let : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian V
  let j := graphProductChart X V b
  obtain ⟨a, ha, hga⟩ := graphChart_exists_nonzero_relation V.1 V.2 U.ι g
    (pullback.fst X.hom (projection (.of k)))
    (rationalGraph_fst X P U r hr) j (graphProductChart_fst X V b)
  have hR : ringKrullDim Γ(g.image, g.imageι ⁻¹ᵁ (j ''ᵁ ⊤)) ≤ ringKrullDim A := by
    apply ENat.WithBot.add_le_add_one_right_iff.mp
    calc
      _ ≤ ringKrullDim A[X] := ringKrullDim_succ_le_of_surjective
        (Modules.Coherent.Pushforward.Finite.chartSectionRingMap g.imageι (.of A[X]) j)
        (graphImage_chartSectionRingMap_surjective g A j)
        (mem_nonZeroDivisors_iff_ne_zero.mpr ha)
        (graphImage_chartSectionRingMap_eq_zero g A j hga)
      _ = ringKrullDim A + 1 := Polynomial.ringKrullDim_of_isNoetherianRing
  have hj : IsAffineOpen (j ''ᵁ ⊤) := by
    simpa only [Scheme.Hom.image_top_eq_opensRange] using isAffineOpen_opensRange j
  have hW : IsAffineOpen (g.imageι ⁻¹ᵁ (j ''ᵁ ⊤)) := hj.preimage g.imageι
  change topologicalKrullDim (g.imageι ⁻¹ᵁ (j ''ᵁ ⊤)).toScheme ≤ _
  calc
    _ = topologicalKrullDim (Spec Γ(g.image, g.imageι ⁻¹ᵁ (j ''ᵁ ⊤))) :=
      IsHomeomorph.topologicalKrullDim_eq _ hW.isoSpec.hom.homeomorph.isHomeomorph
    _ = ringKrullDim Γ(g.image, g.imageι ⁻¹ᵁ (j ''ᵁ ⊤)) :=
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    _ ≤ ringKrullDim A := hR
    _ = topologicalKrullDim (Spec (.of A)) :=
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).symm
    _ = topologicalKrullDim V.1.toScheme :=
      (IsHomeomorph.topologicalKrullDim_eq _ V.2.isoSpec.hom.homeomorph.isHomeomorph).symm
    _ ≤ topologicalKrullDim X.left :=
      V.1.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le

end AlgebraicGeometry.Scheme
