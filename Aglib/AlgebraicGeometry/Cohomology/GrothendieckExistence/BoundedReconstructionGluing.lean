/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ReconstructionChartOverlap
public import Aglib.AlgebraicGeometry.Modules.Coherent.FiniteCoverGluing

/-! # Actual global coherent subobject for bounded reconstruction

The compatible chart subobjects are constructed, not assumed. The ambient is
the original reconstruction pullback and need not be quasicoherent. The native
finite-cover kernel construction produces the actual coherent global object.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {ι : Type u} [Finite ι] (B : ι → CommRingCat.{u}) [∀ i, IsNoetherianRing (B i)]
  (p : ∀ i, Spec (B i) ⟶ X) [∀ i, IsOpenImmersion (p i)]
  (hcover : ∀ x : X, ∃ (i : ι) (y : Spec (B i)), p i y = x)
  {K : X.IdealSheafData} {F : AdicSystem X K} {H : X.CoherentSheaf}
  (α : F ⟶ (completionFunctor X K).obj H)
  (t : ℕ) (h : AdicSystem.DefectsKilled K t α)

include hcover in
/-- Genuine bounded affine reconstruction charts glue as coherent subobjects
of the original global pullback, with their original inclusion equations. -/
theorem exists_boundedReconstructionSubobject_on_cover :
    ∃ (G : X.CoherentSheaf) (s : G.obj ⟶ reconstructionPullback α), Mono s ∧
      ∃ (c : ∀ i, (coherentPullback (p i)).obj G ≅ reconstructionChart (p i) α t h),
        ∀ i, (pullback (p i)).map s = (c i).hom.hom ≫
          reconstructionChartLift (p i) α t h := by
  obtain ⟨G, s, hs, c, hc⟩ :=
    exists_coherent_glued_subobject_of_finite_openImmersionCover
      (fun i => Spec (B i)) p
      (fun x => by obtain ⟨i, y, rfl⟩ := hcover x; exact ⟨i, ⟨y, rfl⟩⟩)
      (reconstructionPullback α) (fun i => (reconstructionChart (p i) α t h).obj)
      (fun i => (reconstructionChart (p i) α t h).property)
      (fun i => reconstructionChartInclusion (p i) α t h)
      (fun i k => (reconstructionChartOverlap (p i) (p k) α t h).val)
      (fun i k => (reconstructionChartOverlap (p i) (p k) α t h).property)
  let d (i : ι) : (coherentPullback (p i)).obj G ≅ reconstructionChart (p i) α t h :=
    ObjectProperty.isoMk _ (((restrictFunctorIsoPullback (p i)).app G.obj).symm ≪≫ c i)
  refine ⟨G, s, hs, d, ?_⟩
  intro i
  apply (cancel_mono ((restrictFunctorIsoPullback (p i)).inv.app
    (reconstructionPullback α))).mp
  rw [(restrictFunctorIsoPullback (p i)).inv.naturality s]
  change (restrictFunctorIsoPullback (p i)).inv.app G.obj ≫
      (restrictFunctor (p i)).map s =
    ((restrictFunctorIsoPullback (p i)).inv.app G.obj ≫ (c i).hom) ≫
      reconstructionChartLift (p i) α t h ≫
        (restrictFunctorIsoPullback (p i)).inv.app (reconstructionPullback α)
  rw [hc i]
  simp only [reconstructionChartInclusion, Category.assoc]

end AlgebraicGeometry.Scheme.Modules.Coherent
