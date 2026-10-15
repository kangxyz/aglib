/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Flasque.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
/-!
# Original direct-image acyclicity of flasque module sheaves

For an arbitrary scheme morphism, the actual pushforward of any given
injective resolution of a flasque module sheaf is exact in positive degrees.
The proof uses the original differential kernel lifts and section surjectivity
of the proved flasque successive kernels. Actual right-derived direct images
therefore vanish in positive degrees. No affine or quasicoherence premise is used.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
namespace AlgebraicGeometry.Scheme.Modules
/-- Original direct image preserves the actual flasqueness of module sheaves. -/
instance pushforward_isFlasque {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules)
    [TopCat.Presheaf.IsFlasque M.presheaf] :
    TopCat.Presheaf.IsFlasque ((Scheme.Modules.pushforward f).obj M).presheaf :=
  inferInstanceAs (TopCat.Presheaf.IsFlasque (f.base _* M.presheaf))
/-- Direct image of any given injective resolution of a flasque sheaf
is exact in positive degrees. -/
theorem pushforward_injectiveResolution_exact_succ_of_flasque {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : X.Modules) [TopCat.Presheaf.IsFlasque M.presheaf]
    (I : InjectiveResolution M) (n : ℕ) :
    (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).ExactAt
      (n + 1) := by
  let F := Scheme.Modules.pushforward f
  let C := I.cocomplex
  let k := kernel.lift (C.d (n + 1) (n + 2)) (C.d n (n + 1))
    (C.d_comp_d n (n + 1) (n + 2))
  have hk (U : X.Opens) : Function.Surjective (k.app U) := by
    cases n with
    | zero =>
      let : TopCat.Presheaf.IsFlasque
          (CategoryTheory.InjectiveResolution.initialSequence I).X₁.presheaf :=
        inferInstanceAs (TopCat.Presheaf.IsFlasque M.presheaf)
      exact sections_surjective_of_flasque_kernel
        (CategoryTheory.InjectiveResolution.initialSequence_shortExact I) U
    | succ n =>
      let : TopCat.Presheaf.IsFlasque
          (CategoryTheory.InjectiveResolution.kernelSequence I (n + 1)).X₁.presheaf :=
        injectiveResolution_kernel_isFlasque M I n
      exact sections_surjective_of_flasque_kernel
        (CategoryTheory.InjectiveResolution.kernelSequence_shortExact I (n + 1)) U
  have he : Epi (F.map k) := by
    constructor
    intro N g h eq
    ext U m
    obtain ⟨x, hx⟩ := hk (f ⁻¹ᵁ U) m
    have hc := congrArg (fun q => q.app U x) eq
    change g.app U (k.app (f ⁻¹ᵁ U) x) = h.app U (k.app (f ⁻¹ᵁ U) x) at hc
    simpa only [hx] using hc
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.exact_iff_epi_kernel_lift]
  have h : kernel.lift (F.map (C.d (n + 1) (n + 2))) (F.map (C.d n (n + 1)))
      (by rw [← F.map_comp, C.d_comp_d, F.map_zero]) =
      F.map k ≫ kernelComparison (C.d (n + 1) (n + 2)) F := by
    apply (cancel_mono (kernel.ι (F.map (C.d (n + 1) (n + 2))))).mp
    simp only [kernel.lift_ι, Category.assoc, kernelComparison_comp_ι,
      ← F.map_comp]
    rw [kernel.lift_ι]
  change Epi (kernel.lift (F.map (C.d (n + 1) (n + 2))) (F.map (C.d n (n + 1))) _)
  rw [h]
  infer_instance
/-- Every higher original direct image of an actual flasque module sheaf vanishes. -/
theorem isZero_rightDerived_pushforward_succ_of_flasque {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : X.Modules) [TopCat.Presheaf.IsFlasque M.presheaf] (n : ℕ) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived (n + 1)).obj M) := by
  let I := injectiveResolution M
  have h := pushforward_injectiveResolution_exact_succ_of_flasque f M I n
  exact h.isZero_homology.of_iso (I.isoRightDerivedObj (Scheme.Modules.pushforward f) (n + 1))
end AlgebraicGeometry.Scheme.Modules
