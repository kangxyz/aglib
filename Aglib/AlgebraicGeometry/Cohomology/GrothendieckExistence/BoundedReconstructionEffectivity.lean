/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BoundedReconstructionGluing
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ReconstructionLocalComparison
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.OpenAnnihilationDetection

/-! # Original completion and same-ideal bounds of the actual glued coefficient -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {ι : Type u} (B : ι → CommRingCat.{u}) [∀ i, IsNoetherianRing (B i)]
  (p : ∀ i, Spec (B i) ⟶ X) [∀ i, IsOpenImmersion (p i)]
  (hcover : ∀ x : X, ∃ (i : ι) (y : Spec (B i)), p i y = x)
  {K : X.IdealSheafData} {F : AdicSystem X K} {H G : X.CoherentSheaf}
  (α : F ⟶ (completionFunctor X K).obj H)
  (t : ℕ) (h : AdicSystem.DefectsKilled K t α)
  (s : G.obj ⟶ reconstructionPullback α)
  (c : ∀ i, (coherentPullback (p i)).obj G ≅ reconstructionChart (p i) α t h)
  (hc : ∀ i, (pullback (p i)).map s =
    (c i).hom.hom ≫ reconstructionChartLift (p i) α t h)

include hcover hc in
/-- The canonical completion map of the actual glued coherent subobject is
invertible, detected on every original finite stage of the actual open cover. -/
theorem reconstructionSubobjectCompletionMap_isIso_of_cover :
    IsIso (reconstructionSubobjectCompletionMap α s) := by
  have (n : ℕᵒᵖ) : IsIso ((reconstructionSubobjectCompletionMap α s).hom.app n) := by
    apply isIso_of_restrict_openCover (fun i => Spec (B i)) p hcover
    intro i
    have hi := reconstructionSubobjectCompletionMap_chart_isIso (p i) α t h s (c i) (hc i) n
    exact (NatIso.isIso_map_iff (restrictFunctorIsoPullback (p i)) _).mpr hi
  exact (ObjectProperty.isIso_hom_iff _).mp
    (NatIso.isIso_of_isIso_app (reconstructionSubobjectCompletionMap α s).hom)

include hc in
/-- The glued algebraic target is the original local target on every chart. -/
theorem reconstructionSubobjectTarget_chart (i : ι) :
    (pullback (p i)).map (reconstructionSubobjectTarget α s).hom =
      (c i).hom.hom ≫ (reconstructionChartTarget (p i) α t h).hom := by
  change (pullback (p i)).map (s ≫ reconstructionToTarget α) = _
  rw [Functor.map_comp, hc i, Category.assoc, reconstructionChartLift_toTarget]

include hcover hc in
/-- The actual ordinary defects of the global algebraic target retain exactly
the same original ideal power as the bounded formal comparison. -/
theorem reconstructionSubobjectTarget_bounds_of_cover :
    killedByIdealSheaf (K ^ t) (kernel (reconstructionSubobjectTarget α s).hom) ∧
      killedByIdealSheaf (K ^ t) (cokernel (reconstructionSubobjectTarget α s).hom) := by
  let a := (reconstructionSubobjectTarget α s).hom
  let : G.obj.IsQuasicoherent := QuasiCoherent.quasicoherent_of_affineCharts _
    (fun R j _ => (G.property R j).1)
  let : H.obj.IsQuasicoherent := QuasiCoherent.quasicoherent_of_affineCharts _
    (fun R j _ => (H.property R j).1)
  let : (kernel a).IsQuasicoherent := QuasiCoherent.quasicoherent_kernel a
  let : (cokernel a).IsQuasicoherent := QuasiCoherent.quasicoherent_cokernel a
  have hb (i : ι) : killedByIdealSheaf (K.comap (p i) ^ t)
      ((pullback (p i)).obj (kernel a)) ∧
      killedByIdealSheaf (K.comap (p i) ^ t)
        ((pullback (p i)).obj (cokernel a)) := by
    let : PreservesLimitsOfShape WalkingParallelPair (pullback (p i)) :=
      preservesLimitsOfShape_of_natIso (restrictFunctorIsoPullback (p i))
    let e := (QuasiCoherent.finiteTypeSheavesToModules (Spec (B i))).mapIso (c i)
    have he : (pullback (p i)).map a ≫ (Iso.refl _).hom =
        e.hom ≫ (reconstructionChartTarget (p i) α t h).hom := by
      rw [Iso.refl_hom, Category.comp_id]
      change (pullback (p i)).map (reconstructionSubobjectTarget α s).hom =
        (c i).hom.hom ≫ (reconstructionChartTarget (p i) α t h).hom
      exact reconstructionSubobjectTarget_chart B p α t h s c hc i
    let ek := PreservesKernel.iso (pullback (p i)) a ≪≫
      kernel.mapIso _ _ e (Iso.refl _) he
    let ec := PreservesCokernel.iso (pullback (p i)) a ≪≫
      cokernel.mapIso _ _ e (Iso.refl _) he
    have hi := affineReconstructionSheafMap_bounds (openReconstructionComparison (p i) α) t
      (openReconstructionComparison_defectsKilled (p i) α K t h)
    exact ⟨killedByIdealSheaf_of_iso _ ek.symm hi.1,
      killedByIdealSheaf_of_iso _ ec.symm hi.2⟩
  constructor
  · apply killedByIdealSheaf_of_pullback_openCover (fun i => Spec (B i)) p hcover
    intro i
    rw [IdealSheafData.comap_pow_of_isOpenImmersion]
    exact (hb i).1
  · apply killedByIdealSheaf_of_pullback_openCover (fun i => Spec (B i)) p hcover
    intro i
    rw [IdealSheafData.comap_pow_of_isOpenImmersion]
    exact (hb i).2

include h hcover in
/-- Actual bounded coherent reconstruction on a finite affine open cover.
Neither a global realization nor a gluing comparison is an input. -/
theorem exists_boundedCoherentReconstruction_on_cover [Finite ι] :
    ∃ (G : X.CoherentSheaf) (a : G ⟶ H)
      (β : (completionFunctor X K).obj G ≅ F),
      β.hom ≫ α = (completionFunctor X K).map a ∧
        killedByIdealSheaf (K ^ t) (kernel a.hom) ∧
          killedByIdealSheaf (K ^ t) (cokernel a.hom) := by
  obtain ⟨G, s, _, c, hc⟩ :=
    exists_boundedReconstructionSubobject_on_cover B p hcover α t h
  have : IsIso (reconstructionSubobjectCompletionMap α s) :=
    reconstructionSubobjectCompletionMap_isIso_of_cover B p hcover α t h s c hc
  refine ⟨G, reconstructionSubobjectTarget α s,
    asIso (reconstructionSubobjectCompletionMap α s),
    reconstructionSubobjectCompletionMap_comp α s, ?_⟩
  exact reconstructionSubobjectTarget_bounds_of_cover B p hcover α t h s c hc

end AlgebraicGeometry.Scheme.Modules.Coherent
