/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Vanishing
public import Aglib.AlgebraicGeometry.Cohomology.Exact.Modules
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Functor
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Right exactness of original top projective cohomology

The original affine-cover bound kills the cohomology of a quasicoherent kernel above
the projective dimension. The original long exact sequence therefore makes the actual
top cohomology map of an epimorphism surjective. A native kernel-lift ladder then proves
right exactness on every actual right-exact quasicoherent short complex. The base ring
is arbitrary; Noetherianity and finite type are not needed here.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The actual top cohomology map of an epimorphism between quasicoherent modules on
projective `n`-space is surjective, by the original kernel sequence and cover bound. -/
theorem projectiveTopCohomologyMap_surjective_of_epi (n : ℕ) (e : ι ≃ Fin (n + 1))
    {M N : (ProjectiveSpace R ι).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] :
    Function.Surjective (moduleCohomologyMapOfHom (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) f n) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let S := ShortComplex.kernelSequence f
  let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α S.X₂ n
  let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α S.X₃ n
  let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α S.X₁ (n + 1)
  let : (kernel f).IsQuasicoherent := quasicoherent_kernel f
  let : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) S.X₁) (n + 1)) :=
    projectiveCohomology_subsingleton_of_gt R ι n e (kernel f) (n + 1) (Nat.lt_succ_self n)
  have hS : S.ShortExact :=
    { exact := ShortComplex.kernelSequence_exact f, epi_g := inferInstanceAs (Epi f) }
  exact (LinearMap.surjective_iff_eq_zero_of_exact
    (moduleCohomologyConnectingOfHom_exact_left (ProjectiveSpace R ι) α S hS n)).mpr
      (Subsingleton.elim _ _)

/-- The same original top map is an epimorphism in the native structural module category. -/
theorem projectiveTopCohomologyMap_epi_of_epi (n : ℕ) (e : ι ≃ Fin (n + 1))
    {M N : (ProjectiveSpace R ι).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] :
    Epi ((moduleCohomologyFunctorOfHom (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) n).map f) :=
  (ModuleCat.epi_iff_surjective _).mpr (projectiveTopCohomologyMap_surjective_of_epi R ι n e f)

/-- Original top cohomology sends every right-exact quasicoherent short complex to an
actual exact short complex of structural modules. Its right arrow remains the original
coefficient cohomology map, whose epimorphism is given separately above. -/
theorem projectiveTopCohomology_exact (n : ℕ) (e : ι ≃ Fin (n + 1))
    (S : ShortComplex (ProjectiveSpace R ι).Modules) (hS : S.Exact) [Epi S.g]
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (S.map (moduleCohomologyFunctorOfHom (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) n)).Exact := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let H := moduleCohomologyFunctorOfHom (ProjectiveSpace R ι) α n
  let K := ShortComplex.kernelSequence S.g
  let κ := kernel.lift S.g S.f S.zero
  let : Epi κ := hS.epi_kernelLift
  let : (kernel S.g).IsQuasicoherent := quasicoherent_kernel S.g
  let : Epi (H.map κ) := projectiveTopCohomologyMap_epi_of_epi R ι n e κ
  have hK : K.ShortExact :=
    { exact := ShortComplex.kernelSequence_exact S.g, epi_g := inferInstanceAs (Epi S.g) }
  have hHK : (K.map H).Exact := by
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    exact moduleCohomologyMapOfHom_exact (ProjectiveSpace R ι) α K hK n
  let φ : S.map H ⟶ K.map H := {
    τ₁ := H.map κ
    τ₂ := 𝟙 _
    τ₃ := 𝟙 _
    comm₁₂ := by
      change H.map κ ≫ H.map (kernel.ι S.g) = H.map S.f ≫ 𝟙 _
      rw [Category.comp_id, ← H.map_comp]
      exact congrArg H.map (kernel.lift_ι S.g S.f S.zero)
    comm₂₃ := by
      change 𝟙 _ ≫ H.map S.g = H.map S.g ≫ 𝟙 _
      simp }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hHK

end AlgebraicGeometry.Scheme.Cohomology
