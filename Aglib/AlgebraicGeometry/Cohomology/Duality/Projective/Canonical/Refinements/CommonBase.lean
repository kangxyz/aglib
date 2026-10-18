/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.BaseChart
public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.PrincipalNeighborhood

/-!
# An actual common principal base for two smooth closed charts

The retained source point determines the same original base point in both
charts. A common native principal neighborhood of that point lifts to the
actual base refinements. Its spectral ring isomorphism satisfies the exact
original base-chart equation.
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

/-- The retained chart point maps to the original source's actual base point. -/
theorem basePoint_eq (C : SmoothClosedImmersionLocalChart i p n d x) :
    C.jY ((Spec.map (C.α ≫ C.σ)) C.point) = (i ≫ p) x := by
  have h : Spec.map (C.α ≫ C.σ) ≫ C.jY = C.jX ≫ (i ≫ p) := by
    rw [Spec.map_comp, Category.assoc, C.ambientSquare, ← Category.assoc, C.closedSquare,
      Category.assoc]
  exact (congrArg (fun f => f C.point) h).trans (congrArg (i ≫ p) C.point_eq)

private theorem basePrincipalCondition (C : SmoothClosedImmersionLocalChart i p n d x)
    (r : C.R) (z : Spec (CommRingCat.of (Localization.Away r)))
    (hz : (Spec.map (CommRingCat.ofHom (algebraMap C.R (Localization.Away r))) ≫ C.jY) z =
      (i ≫ p) x) : C.σ (C.α r) ∉ C.point.asIdeal := by
  let loc := Spec.map (CommRingCat.ofHom (algebraMap C.R (Localization.Away r)))
  have hpoint : loc z = (Spec.map (C.α ≫ C.σ)) C.point :=
    C.jY.isOpenEmbedding.injective (hz.trans C.basePoint_eq.symm)
  have hmem : (Spec.map (C.α ≫ C.σ)) C.point ∈ loc.opensRange := by
    rw [← hpoint]
    exact ⟨z, rfl⟩
  rw [Scheme.Hom.opensRange_localizationAway] at hmem
  exact hmem

/-- The two actual base refinements have the same base open through an actual ring isomorphism. -/
theorem exists_commonBasePrincipalCharts
    (C D : SmoothClosedImmersionLocalChart i p n d x) :
    ∃ (r : C.R) (s : D.R)
      (hr : C.σ (C.α r) ∉ C.point.asIdeal)
      (hs : D.σ (D.α s) ∉ D.point.asIdeal)
      (e : CommRingCat.of (Localization.Away s) ≅ CommRingCat.of (Localization.Away r)),
      Spec.map e.hom ≫ (D.basePrincipalChart s hs).jY = (C.basePrincipalChart r hr).jY := by
  have hC : (i ≫ p) x ∈ C.jY.opensRange := ⟨_, C.basePoint_eq⟩
  have hD : (i ≫ p) x ∈ D.jY.opensRange := ⟨_, D.basePoint_eq⟩
  obtain ⟨r, s, e, z, he, hz⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_canonicalCommonPrincipalNeighborhood
      C.jY D.jY ((i ≫ p) x) hC hD
  have hr := basePrincipalCondition C r z hz
  have hzD : (Spec.map (CommRingCat.ofHom (algebraMap D.R (Localization.Away s))) ≫ D.jY)
      ((Spec.map e.hom) z) = (i ≫ p) x :=
    (congrArg (fun f => f z) he).trans hz
  have hs := basePrincipalCondition D s ((Spec.map e.hom) z) hzD
  exact ⟨r, s, hr, hs, e, he⟩

end SmoothClosedImmersionLocalChart
end AlgebraicGeometry.Scheme.Modules.Differentials
