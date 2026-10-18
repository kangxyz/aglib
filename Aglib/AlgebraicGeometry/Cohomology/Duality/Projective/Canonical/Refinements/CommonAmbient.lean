/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.CommonBase
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Cartesian

/-!
# Actual common ambient and source charts

Principal neighborhoods of the same original ambient point give an actual
ambient ring isomorphism. The two original Cartesian closed squares then
identify their source opens through an actual source ring isomorphism.
The original base and closed-arrow equations give the corresponding ring
squares, before any canonical-map or determinant comparison.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.Modules.Differentials
namespace SmoothClosedImmersionLocalChart

attribute [local instance] SmoothClosedImmersionLocalChart.openX
  SmoothClosedImmersionLocalChart.openP SmoothClosedImmersionLocalChart.openY

variable {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ} {x : X}

/-- The retained source point maps to the same original ambient point. -/
theorem ambientPoint_eq (C : SmoothClosedImmersionLocalChart i p n d x) :
    C.jP ((Spec.map C.σ) C.point) = i x :=
  (congrArg (fun f => f C.point) C.closedSquare).trans (congrArg i C.point_eq)

private theorem ambientPrincipalCondition (C : SmoothClosedImmersionLocalChart i p n d x)
    (a : C.A) (z : Spec (CommRingCat.of (Localization.Away a)))
    (hz : (Spec.map (CommRingCat.ofHom (algebraMap C.A (Localization.Away a))) ≫ C.jP) z =
      i x) : C.σ a ∉ C.point.asIdeal := by
  let loc := Spec.map (CommRingCat.ofHom (algebraMap C.A (Localization.Away a)))
  have hpoint : loc z = (Spec.map C.σ) C.point :=
    C.jP.isOpenEmbedding.injective (hz.trans C.ambientPoint_eq.symm)
  have hmem : (Spec.map C.σ) C.point ∈ loc.opensRange := by
    rw [← hpoint]
    exact ⟨z, rfl⟩
  rw [Scheme.Hom.opensRange_localizationAway] at hmem
  exact hmem

/-- Ambient principal refinements at the retained point have the same actual ambient open. -/
theorem exists_commonAmbientPrincipalCharts
    (C D : SmoothClosedImmersionLocalChart i p n d x) :
    ∃ (a : C.A) (b : D.A)
      (ha : C.σ a ∉ C.point.asIdeal) (hb : D.σ b ∉ D.point.asIdeal)
      (e : CommRingCat.of (Localization.Away b) ≅ CommRingCat.of (Localization.Away a)),
      Spec.map e.hom ≫ (D.principalChart b hb).jP = (C.principalChart a ha).jP := by
  have hC : i x ∈ C.jP.opensRange := ⟨_, C.ambientPoint_eq⟩
  have hD : i x ∈ D.jP.opensRange := ⟨_, D.ambientPoint_eq⟩
  obtain ⟨a, b, e, z, he, hz⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_canonicalCommonPrincipalNeighborhood
      C.jP D.jP (i x) hC hD
  have ha := ambientPrincipalCondition C a z hz
  have hzD : (Spec.map (CommRingCat.ofHom (algebraMap D.A (Localization.Away b))) ≫ D.jP)
      ((Spec.map e.hom) z) = i x :=
    (congrArg (fun f => f z) he).trans hz
  have hb := ambientPrincipalCondition D b ((Spec.map e.hom) z) hzD
  exact ⟨a, b, ha, hb, e, he⟩

/-- Equality of original base and ambient chart arrows gives the actual ring base square. -/
theorem commonAmbientRingSquare (C D : SmoothClosedImmersionLocalChart i p n d x)
    (eR : D.R ≅ C.R) (eA : D.A ≅ C.A)
    (hY : Spec.map eR.hom ≫ D.jY = C.jY) (hP : Spec.map eA.hom ≫ D.jP = C.jP) :
    eR.hom ≫ C.α = D.α ≫ eA.hom := by
  apply Spec.map_injective
  apply (cancel_mono D.jY).mp
  rw [Spec.map_comp, Spec.map_comp, Category.assoc, hY, C.ambientSquare,
    Category.assoc, D.ambientSquare, ← Category.assoc, hP]

/-- The two original Cartesian closed squares induce an actual source-ring isomorphism,
with both its original chart equation and original closed-arrow ring square. -/
theorem exists_commonSourceRingIso (C D : SmoothClosedImmersionLocalChart i p n d x)
    (eA : D.A ≅ C.A) (hP : Spec.map eA.hom ≫ D.jP = C.jP) :
    ∃ eB : D.B ≅ C.B, Spec.map eB.hom ≫ D.jX = C.jX ∧
      eA.hom ≫ C.σ = D.σ ≫ eB.hom := by
  have hRangeP : C.jP.opensRange = D.jP.opensRange := by
    apply TopologicalSpace.Opens.ext
    exact (congrArg (fun f : Spec C.A ⟶ P => Set.range f) hP.symm).trans
      (TopologicalSpace.Opens.ext_iff.mp
        (Scheme.Hom.opensRange_comp_of_isIso (Spec.map eA.hom) D.jP))
  have hRangeX : C.jX.opensRange = D.jX.opensRange :=
    (AlgebraicGeometry.Scheme.Modules.opensRange_of_isPullback
      C.jX (Spec.map C.σ) i C.jP C.cartesian).trans
        ((congrArg (fun U => i ⁻¹ᵁ U) hRangeP).trans
          (AlgebraicGeometry.Scheme.Modules.opensRange_of_isPullback
            D.jX (Spec.map D.σ) i D.jP D.cartesian).symm)
  let E := IsOpenImmersion.isoOfRangeEq C.jX D.jX
    (TopologicalSpace.Opens.ext_iff.mp hRangeX)
  let eB := AlgebraicGeometry.Scheme.Modules.canonicalSpectralRingIso E
  have hX : Spec.map eB.hom ≫ D.jX = C.jX :=
    (congrArg (fun f => f ≫ D.jX)
      (AlgebraicGeometry.Scheme.Modules.canonicalSpectralRingIso_spec_hom E)).trans
        (IsOpenImmersion.isoOfRangeEq_hom_fac C.jX D.jX
          (TopologicalSpace.Opens.ext_iff.mp hRangeX))
  refine ⟨eB, hX, ?_⟩
  apply Spec.map_injective
  apply (cancel_mono D.jP).mp
  rw [Spec.map_comp, Spec.map_comp, Category.assoc, hP, C.closedSquare,
    Category.assoc, D.closedSquare, ← Category.assoc, hX]

end SmoothClosedImmersionLocalChart
end AlgebraicGeometry.Scheme.Modules.Differentials
