/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.Semilinear.KernelRepresentation.GenericFinite
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.Semilinear.LocalLifting.Restricted
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteCoefficientPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleRestrictionComposition

/-!
# A common principal shrink for two original semilinear operators

Retain the first operator's genuine finite-kernel localization. Plain generic
freeness for the second actual tensor module supplies one further localization.
Native cancellation preserves both original modules, and native localization
composition identifies the unchanged final ring with a nonzero principal
localization of the original base. Kernel finiteness is pulled along the actual
open immersion; surjectivity of both differences comes independently from
inhomogeneous root covers.
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

private theorem exists_free_tensor_away
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ a : A, a ≠ 0 ∧ Module.Free (Localization.Away a) ((Localization.Away a) ⊗[A] M) := by
  obtain ⟨a, ha, hfree⟩ :=
    Module.Finite.exists_free_localizedModule_away_of_isNoetherianRing (A := A) M
  let := hfree
  exact ⟨a, ha, Module.free_of_isLocalizedModule_of_free_isLocalizedModule
    (Submonoid.powers a) (Localization.Away a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
    (TensorProduct.mk A (Localization.Away a) M 1)⟩

/-- One genuine principal localization simultaneously makes the first original
kernel finite locally constant and both original differences epimorphisms.
The finite-free witnesses refer to the actual localized original modules. -/
theorem exists_common_restrictedKernel_finiteLocallyConstant_and_epi
    (A : CommRingCat.{u}) [IsDomain A] [IsNoetherianRing A]
    (F G : (Spec A).Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    [Module.Finite A (moduleSpecΓFunctor.obj F)]
    [Module.Finite A (moduleSpecΓFunctor.obj G)]
    (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    (Φ : moduleSpecΓFunctor.obj F →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA]
      moduleSpecΓFunctor.obj F)
    (Ψ : moduleSpecΓFunctor.obj G →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA]
      moduleSpecΓFunctor.obj G) :
    ∃ (r : A), r ≠ 0 ∧
      ∃ (R : Type u) (_ : CommRing R) (_ : Algebra A R) (_ : IsLocalization.Away r R)
        (_ : Etale (Spec.map (CommRingCat.ofHom (algebraMap A R)))),
        Module.Free R (R ⊗[A] moduleSpecΓFunctor.obj F) ∧
        Module.Free R (R ⊗[A] moduleSpecΓFunctor.obj G) ∧
        IsFiniteLocallyConstant
          ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap A R)))).obj
            (kernel (affineFrobenius A F p hp hA Φ -
              𝟙 (additiveCoefficient (Spec A) F)))) ∧
        Epi ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap A R)))).map
          (affineFrobenius A F p hp hA Φ - 𝟙 (additiveCoefficient (Spec A) F))) ∧
        Epi ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap A R)))).map
          (affineFrobenius A G p hp hA Ψ - 𝟙 (additiveCoefficient (Spec A) G))) := by
  obtain ⟨a, ha, R₀, hR₀, hAR₀, hloc₀, hEt₀, C, hC, hR₀C, hfinite, hetale,
      hfree₀, _, hL₀⟩ := exists_finite_etale_restrictedKernel_and_free A F p hp hA Φ
  let : IsDomain R₀ := IsLocalization.Away.isDomain (S := R₀) ha
  let : IsNoetherianRing R₀ :=
    IsLocalization.isNoetherianRing (Submonoid.powers a) R₀ inferInstance
  let := hfree₀
  let N := R₀ ⊗[A] moduleSpecΓFunctor.obj G
  obtain ⟨b, hb, hfreeN⟩ := exists_free_tensor_away R₀ N
  let R := Localization.Away b
  let := hfreeN
  let : Module.Free R (R ⊗[A] moduleSpecΓFunctor.obj G) :=
    Module.Free.of_equiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A R₀ R R (moduleSpecΓFunctor.obj G))
  let : Module.Free R (R ⊗[A] moduleSpecΓFunctor.obj F) :=
    Module.Free.of_equiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A R₀ R R (moduleSpecΓFunctor.obj F))
  let c := (IsLocalization.Away.sec a b).1
  have hassoc : Associated (algebraMap A R₀ c) b :=
    IsLocalization.Away.associated_sec_fst a b
  have hc : c ≠ 0 := by
    intro h
    exact hb (hassoc.eq_zero_iff.mp (by rw [h, map_zero]))
  let : IsLocalization.Away (a * c) R :=
    IsLocalization.Away.mul_of_associated a c b hassoc
  let j₀ := Spec.map (CommRingCat.ofHom (algebraMap A R₀))
  let k := Spec.map (CommRingCat.ofHom (algebraMap R₀ R))
  let j := Spec.map (CommRingCat.ofHom (algebraMap A R))
  let : IsOpenImmersion k := IsOpenImmersion.of_isLocalization b
  let : IsOpenImmersion j := IsOpenImmersion.of_isLocalization (a * c)
  have hcomp : k ≫ j₀ = j := by
    rw [← Spec.map_comp]
    congr 1
  let K := kernel (affineFrobenius A F p hp hA Φ - 𝟙 (additiveCoefficient (Spec A) F))
  have hL : IsFiniteLocallyConstant ((etaleRestriction (k ≫ j₀)).obj K) :=
    (isFiniteLocallyConstant_iff_of_iso ((etaleRestrictionComp j₀ k).app K)).mpr
      ((isFiniteLocallyConstant_iff_of_iso ((inverseImageEtaleIso k).app
        ((etaleRestriction j₀).obj K))).mp (isFiniteLocallyConstant_pullback k hL₀))
  refine ⟨a * c, mul_ne_zero ha hc, R, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ?_,
    restricted_affineFrobenius_epi A F p hp hA Φ R,
    restricted_affineFrobenius_epi A G p hp hA Ψ R⟩
  simpa only [hcomp] using hL

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
