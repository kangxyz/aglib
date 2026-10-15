/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Affine.GlobalSectionsExactness
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Sections
public import Aglib.AlgebraicGeometry.Cohomology.Flasque.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
/-!
# Actual right-derived affine global sections

The first right-derived functor of the original `moduleSpecΓFunctor` vanishes
on quasicoherent module sheaves over an arbitrary commutative ring. The proof
uses the actual injective resolution in all module sheaves and the established
section-lifting theorem with quasicoherent kernel.

For flasque module sheaves, every positive right-derived global-section module
vanishes, by the proved flasqueness of successive injective-resolution kernels.
These coefficients are otherwise unrestricted.

The quasicoherent conclusion here is degree one only. Higher quasicoherent
vanishing still requires the Cech-to-derived comparison; quasicoherent sheaves
are not assumed flasque, and injective resolution terms are not assumed
quasicoherent. No derived affine equivalence or strictification is asserted.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.ExactCategory

namespace AlgebraicGeometry.Scheme.Modules.AffineDerived

open AffineCech

/-- Applying the original affine global-sections functor to any injective
resolution of a quasicoherent sheaf is exact in degree one. The resolution is
in all module sheaves; its terms need not be quasicoherent. -/
lemma globalSections_injectiveResolution_exact_one {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] (I : InjectiveResolution M) :
    ((moduleSpecΓFunctor.mapHomologicalComplex _).obj I.cocomplex).ExactAt 1 := by
  let C := I.cocomplex
  let k := kernel.lift (C.d 1 2) (C.d 0 1) (C.d_comp_d 0 1 2)
  have hk : Epi k := (I.exact_succ 0).epi_kernelLift
  let S := ShortComplex.mk (I.ι.f 0) k (by
    apply (cancel_mono (kernel.ι (C.d 1 2))).mp
    simp only [Category.assoc, k, kernel.lift_ι, zero_comp]
    exact I.ι_f_zero_comp_complex_d)
  let φ : S ⟶ ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι (C.d 1 2)
      comm₂₃ := by simp [S, k, C] }
  have hS : S.ShortExact :=
    { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr I.exact₀ }
  let : S.X₁.IsQuasicoherent := by
    change (((CochainComplex.single₀ (Spec R).Modules).obj M).X 0).IsQuasicoherent
    simpa using (inferInstance : M.IsQuasicoherent)
  have hΓS := shortExact_globalSections_of_quasicoherent_kernel hS
  let K := ShortComplex.mk (kernel.ι (C.d 1 2)) (C.d 1 2) (kernel.condition _)
  have hΓK : (K.map moduleSpecΓFunctor).Exact := by
    exact ShortComplex.exact_of_f_is_kernel _
      (KernelFork.mapIsLimit _ (kernelIsKernel (C.d 1 2)) moduleSpecΓFunctor)
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro z hz
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp hΓK z hz
  obtain ⟨x, hx⟩ := hΓS.moduleCat_surjective_g y
  refine ⟨x, ?_⟩
  change moduleSpecΓFunctor.map (C.d 0 1) x = z
  rw [← kernel.lift_ι (C.d 1 2) (C.d 0 1) (C.d_comp_d 0 1 2), Functor.map_comp]
  change moduleSpecΓFunctor.map (kernel.ι (C.d 1 2)) (moduleSpecΓFunctor.map k x) = z
  change moduleSpecΓFunctor.map k x = y at hx
  exact (congrArg (fun t => moduleSpecΓFunctor.map (kernel.ι (C.d 1 2)) t) hx).trans hy

/-- Actual first right-derived global sections vanish for quasicoherent
coefficients over an arbitrary commutative ring. -/
lemma isZero_rightDerived_globalSections_one {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    IsZero ((moduleSpecΓFunctor.rightDerived 1).obj M) := by
  let I := injectiveResolution M
  exact (globalSections_injectiveResolution_exact_one M I).isZero_homology.of_iso
    (I.isoRightDerivedObj moduleSpecΓFunctor 1)

/-- Global sections of any actual injective resolution of a flasque module
sheaf are exact in every positive degree. No quasicoherence is required. -/
lemma globalSections_injectiveResolution_exact_succ_of_flasque {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [TopCat.Presheaf.IsFlasque M.presheaf]
    (I : CategoryTheory.InjectiveResolution M) (n : ℕ) :
    ((moduleSpecΓFunctor.mapHomologicalComplex _).obj I.cocomplex).ExactAt (n + 1) := by
  let C := I.cocomplex
  let k := kernel.lift (C.d (n + 1) (n + 2)) (C.d n (n + 1))
    (C.d_comp_d n (n + 1) (n + 2))
  have hk : Function.Surjective (moduleSpecΓFunctor.map k) := by
    cases n with
    | zero =>
      let : TopCat.Presheaf.IsFlasque
          (CategoryTheory.InjectiveResolution.initialSequence I).X₁.presheaf :=
        inferInstanceAs (TopCat.Presheaf.IsFlasque M.presheaf)
      exact sections_surjective_of_flasque_kernel
        (CategoryTheory.InjectiveResolution.initialSequence_shortExact I) ⊤
    | succ n =>
      let : TopCat.Presheaf.IsFlasque
          (CategoryTheory.InjectiveResolution.kernelSequence I (n + 1)).X₁.presheaf :=
        injectiveResolution_kernel_isFlasque M I n
      exact sections_surjective_of_flasque_kernel
        (CategoryTheory.InjectiveResolution.kernelSequence_shortExact I (n + 1)) ⊤
  let K := ShortComplex.mk (kernel.ι (C.d (n + 1) (n + 2)))
    (C.d (n + 1) (n + 2)) (kernel.condition _)
  have hΓK : (K.map moduleSpecΓFunctor).Exact :=
    ShortComplex.exact_of_f_is_kernel _
      (KernelFork.mapIsLimit _ (kernelIsKernel (C.d (n + 1) (n + 2))) moduleSpecΓFunctor)
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro z hz
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp hΓK z hz
  obtain ⟨x, hx⟩ := hk y
  refine ⟨x, ?_⟩
  change moduleSpecΓFunctor.map (C.d n (n + 1)) x = z
  rw [← kernel.lift_ι (C.d (n + 1) (n + 2)) (C.d n (n + 1))
    (C.d_comp_d n (n + 1) (n + 2)), Functor.map_comp]
  change moduleSpecΓFunctor.map (kernel.ι (C.d (n + 1) (n + 2)))
    (moduleSpecΓFunctor.map k x) = z
  exact (congrArg (fun t => moduleSpecΓFunctor.map (kernel.ι (C.d (n + 1) (n + 2))) t) hx).trans hy

/-- Flasque module sheaves have zero actual right-derived global sections
in every positive degree. -/
lemma isZero_rightDerived_globalSections_succ_of_flasque {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [TopCat.Presheaf.IsFlasque M.presheaf] (n : ℕ) :
    IsZero ((moduleSpecΓFunctor.rightDerived (n + 1)).obj M) := by
  let I := injectiveResolution M
  exact (globalSections_injectiveResolution_exact_succ_of_flasque M I n).isZero_homology.of_iso
    (I.isoRightDerivedObj moduleSpecΓFunctor (n + 1))

end AlgebraicGeometry.Scheme.Modules.AffineDerived
