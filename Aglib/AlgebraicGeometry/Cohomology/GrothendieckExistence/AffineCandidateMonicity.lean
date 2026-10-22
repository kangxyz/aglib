/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineCompletionSections
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineDefectSections
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineJointMonicity

/-! # Finite-stage monicity for an actual bounded affine candidate

Only the ordinary algebraic kernel bound and the specified formal isomorphism
are needed. Neither a formal target comparison nor a cokernel bound is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {K : (Spec B).IdealSheafData} {F : AdicSystem (Spec B) K}
  {G H : (Spec B).CoherentSheaf}

/-- An actual bounded candidate is detected by its algebraic target map and
one finite original formal-stage projection. -/
theorem affineCandidateStages_jointly_monic (a : G ⟶ H)
    (β : (completionFunctor (Spec B) K).obj G ≅ F) (t : ℕ)
    (hk : killedByIdealSheaf (K ^ t) (kernel a.hom)) :
    ∃ n : ℕ, Mono (prod.lift a.hom
      ((idealSheafQuotientUnit (Spec B) (K ^ n)).app G.obj ≫
        β.hom.hom.app (op n))) := by
  let : G.obj.IsQuasicoherent :=
    ((QuasiCoherent.affineLocallyFiniteType_spec_iff B G.obj).mp G.property).1
  let : H.obj.IsQuasicoherent :=
    ((QuasiCoherent.affineLocallyFiniteType_spec_iff B H.obj).mp H.property).1
  let : Module.Finite B (moduleSpecΓFunctor.obj G.obj) :=
    ((QuasiCoherent.affineLocallyFiniteType_spec_iff B G.obj).mp G.property).2
  obtain ⟨n, hn⟩ := Submodule.exists_pow_smul_top_inf_eq_bot_of_pow_smul_eq_bot
    (affineIdeal B K) (moduleSpecΓFunctor.map a.hom).hom.ker t
    (affineSections_kernel_bound a.hom K t hk)
  let : (F.obj.obj (op n)).IsQuasicoherent :=
    ((QuasiCoherent.affineLocallyFiniteType_spec_iff B _).mp (F.property.coherent n)).1
  have hi : Function.Injective (moduleSpecΓFunctor.map (β.hom.hom.app (op n))) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hs : (moduleSpecΓFunctor.map
      ((idealSheafQuotientUnit (Spec B) (K ^ n)).app G.obj ≫
        β.hom.hom.app (op n))).hom.ker =
      affineIdeal B K ^ n • (⊤ : Submodule B (moduleSpecΓFunctor.obj G.obj)) := by
    rw [← affineCompletionUnit_ker B K G n]
    ext x
    change moduleSpecΓFunctor.map
      ((idealSheafQuotientUnit (Spec B) (K ^ n)).app G.obj ≫
        β.hom.hom.app (op n)) x = 0 ↔ affineCompletionUnit B K G n x = 0
    rw [Functor.map_comp, ConcreteCategory.comp_apply]
    change (moduleSpecΓFunctor.map (β.hom.hom.app (op n))).hom
      (affineCompletionUnit B K G n x) = 0 ↔ affineCompletionUnit B K G n x = 0
    exact LinearMap.map_eq_zero_iff _ hi
  refine ⟨n, mono_prod_lift_of_sections_ker_inf_eq_bot B a.hom _ ?_⟩
  rw [hs, inf_comm]
  exact hn

end AlgebraicGeometry.Scheme.Modules.Coherent
