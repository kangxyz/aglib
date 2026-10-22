/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineCompletionDefectReflection
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineScalarDefectRestriction
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineIdealBaseChange
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineDefectSections

/-! # Reflecting the actual geometric exceptional bound from completion

Finite defining-ideal-torsion coefficients are unchanged by the original
completion unit. The exceptional ideal is independent of that defining ideal,
and reflection does not change its exponent or assume faithful flatness.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B] (I : Ideal B)
  {M N : (Spec B).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
  [Module.Finite B (moduleSpecΓFunctor.obj M)]
  [Module.Finite B (moduleSpecΓFunctor.obj N)]
  (q : M ⟶ N) (m n : ℕ)
  (hM : I ^ m • (⊤ : Submodule B (moduleSpecΓFunctor.obj M)) = ⊥)
  (hN : I ^ n • (⊤ : Submodule B (moduleSpecΓFunctor.obj N)) = ⊥)

include m n hM hN in
/-- The original finite-stage geometric map inherits the same exceptional
power as its actual pullback to the completed affine base. -/
theorem completionPullback_geometric_defects_reflect
    (K : (Spec B).IdealSheafData) (t : ℕ)
    (hk : let w := Spec.map (CommRingCat.ofHom (algebraMap B (AdicCompletion I B)))
      killedByIdealSheaf (K.comap w ^ t) (kernel ((pullback w).map q)))
    (hc : let w := Spec.map (CommRingCat.ofHom (algebraMap B (AdicCompletion I B)))
      killedByIdealSheaf (K.comap w ^ t) (cokernel ((pullback w).map q))) :
    killedByIdealSheaf (K ^ t) (kernel q) ∧
      killedByIdealSheaf (K ^ t) (cokernel q) := by
  let φ := CommRingCat.ofHom (algebraMap B (AdicCompletion I B))
  let w := Spec.map φ
  have hk' := affineSections_kernel_bound ((pullback w).map q) (K.comap w) t hk
  have hc' := affineSections_cokernel_bound ((pullback w).map q) (K.comap w) t hc
  rw [affineIdeal_comap_specMap, ← Ideal.map_pow] at hk' hc'
  have hp := affinePushforward_sections_defectBounds φ ((pullback w).map q)
    (affineIdeal B K ^ t) hk' hc'
  have hr := completionPullback_defectBounds_reflect I q m n hM hN
    (affineIdeal B K ^ t) hp.1 hp.2
  exact ⟨killed_kernel_of_affineSections_bound q K t hr.1,
    killed_cokernel_of_affineSections_bound q K t hr.2⟩

/-- Every original formal coefficient has the bounded-torsion property needed
for reflection; no completed scalar structure is added to that coefficient. -/
theorem affineFormalStage_pow_smul_eq_bot
    (F : AdicSystem (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) I)) (r : ℕ) :
    I ^ r • (⊤ : Submodule B (moduleSpecΓFunctor.obj (F.obj.obj (op r)))) = ⊥ := by
  have h := affineIdeal_pow_le_annihilator_of_killed B
    (idealThickeningIdealSheaf (𝟙 (Spec B)) I) (F.obj.obj (op r)) r
    (F.property.annihilated r)
  rw [affineIdeal_idealThickeningIdealSheaf] at h
  apply le_bot_iff.mp
  apply Submodule.smul_le.mpr
  intro a ha x _
  exact (Module.mem_annihilator.mp (h ha)) x

/-- Uniform bounds on all actual pulled finite stages reflect uniformly to
the original formal map, with precisely the same exceptional exponent. -/
theorem completionPullback_formal_defects_reflect
    {F G : AdicSystem (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) I)}
    (α : F ⟶ G) (K : (Spec B).IdealSheafData) (t : ℕ)
    (h : let w := Spec.map (CommRingCat.ofHom (algebraMap B (AdicCompletion I B)))
      ∀ r : ℕ,
        killedByIdealSheaf (K.comap w ^ t)
          (kernel ((pullback w).map (α.hom.app (op r)))) ∧
        killedByIdealSheaf (K.comap w ^ t)
          (cokernel ((pullback w).map (α.hom.app (op r))))) :
    AdicSystem.DefectsKilled K t α := by
  intro r
  let : (F.obj.obj (op r)).IsQuasicoherent :=
    ((QuasiCoherent.affineLocallyFiniteType_spec_iff B _).mp (F.property.coherent r)).1
  let : (G.obj.obj (op r)).IsQuasicoherent :=
    ((QuasiCoherent.affineLocallyFiniteType_spec_iff B _).mp (G.property.coherent r)).1
  let : Module.Finite B (moduleSpecΓFunctor.obj (F.obj.obj (op r))) :=
    ((QuasiCoherent.affineLocallyFiniteType_spec_iff B _).mp (F.property.coherent r)).2
  let : Module.Finite B (moduleSpecΓFunctor.obj (G.obj.obj (op r))) :=
    ((QuasiCoherent.affineLocallyFiniteType_spec_iff B _).mp (G.property.coherent r)).2
  exact completionPullback_geometric_defects_reflect I (α.hom.app (op r)) r r
    (affineFormalStage_pow_smul_eq_bot I F r) (affineFormalStage_pow_smul_eq_bot I G r)
    K t (h r).1 (h r).2

end AlgebraicGeometry.Scheme.Modules.Coherent
