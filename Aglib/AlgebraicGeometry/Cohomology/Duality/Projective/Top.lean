/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Presentation
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Coproduct
public import Aglib.AlgebraicGeometry.ProjectiveSpace.TwistPresentation.Coherent
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Finiteness

/-!
# Coherent top Serre duality on polynomial projective space

An actual coherent module over a Noetherian base has a proved two-step presentation by
sufficiently negative finite twist sums. The canonical top map is bijective on those
sums, and the native exact diagram transfers this to the actual module. Thus original
structure-linear morphisms to `O(-n-1)` identify with the linear dual of unchanged top
cohomology, with the original trace after each actual coefficient map as the forward map.
Over a field, finite cohomology also makes this canonical pairing perfect in both inputs.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u) [Fintype ι]

/-- Coherent top Serre duality over a Noetherian ring: the original canonical map from
actual morphisms into the residue twist to the dual of original top cohomology is bijective. -/
theorem projectiveTopSerreMap_bijective (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) :
    Function.Bijective (projectiveTopSerreMap R ι n e M) := by
  obtain ⟨N, hN, L, hL, I, hI, J, hJ, d, π, hd, hS, hπ⟩ :=
    exists_uniformNegativeTwistTwoStepPresentation R ι M hM (Fintype.card ι)
  let := hI
  let := hJ
  let S := ShortComplex.mk d π hd
  let : Epi S.g := hπ
  let : S.X₁.IsQuasicoherent :=
    twistingCoproduct_isQuasicoherent R ι (fun _ : J => -(L : ℤ))
  let : S.X₂.IsQuasicoherent :=
    twistingCoproduct_isQuasicoherent R ι (fun _ : I => -(N : ℤ))
  let : S.X₃.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  exact projectiveTopSerreMap_bijective_of_presentation R ι n e S hS
    (projectiveTopSerreMap_uniformNegativeCoproduct_bijective (I := I) R ι n e N hN)
    (projectiveTopSerreMap_uniformNegativeCoproduct_bijective (I := J) R ι n e L hL)

/-- The actual top Serre duality equivalence for a coherent module over a Noetherian base,
with the existing canonical map as its forward linear map. -/
def projectiveTopSerreDuality (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α M n
    (M ⟶ twistingSheaf R ι (-(Fintype.card ι : ℤ))) ≃ₗ[R]
      Module.Dual R (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) M) n) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α M n
  exact LinearEquiv.ofBijective (projectiveTopSerreMap R ι n e M)
    (projectiveTopSerreMap_bijective R ι n e M hM)

/-- The coherent duality equivalence is exactly trace after the original coefficient
cohomology map; its construction does not choose a replacement pairing. -/
theorem projectiveTopSerreDuality_apply (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M)
    (f : M ⟶ twistingSheaf R ι (-(Fintype.card ι : ℤ)))
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) M) n) :
    projectiveTopSerreDuality R ι n e M hM f x =
      projectiveTrace R ι n e
        (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map f) n x) :=
  projectiveTopSerreMap_apply R ι n e M f x

/-- Coherent top duality is natural in the original coefficient morphisms. -/
theorem projectiveTopSerreDuality_naturality (n : ℕ) (e : ι ≃ Fin (n + 1))
    {M N : (ProjectiveSpace R ι).Modules}
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M)
    (hN : affineLocallyFiniteType (ProjectiveSpace R ι) N)
    (f : M ⟶ N) (g : N ⟶ twistingSheaf R ι (-(Fintype.card ι : ℤ)))
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) M) n) :
    projectiveTopSerreDuality R ι n e M hM (f ≫ g) x =
      projectiveTopSerreDuality R ι n e N hN g
        (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map f) n x) :=
  projectiveTopSerreMap_naturality R ι n e f g x

/-- Over a field, the same original coherent top Serre pairing is perfect in both inputs.
The stronger conclusion uses finiteness and reflexivity of the original cohomology module. -/
theorem projectiveTopSerreMap_isPerfPair {K : Type u} [Field K]
    (κ : Type u) [Fintype κ] (n : ℕ) (e : κ ≃ Fin (n + 1))
    (M : (ProjectiveSpace K κ).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace K κ) M) :
    let α : K →+* Γ(ProjectiveSpace K κ, ⊤) :=
      (toSpec K κ).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
    letI := moduleCategoryLinearOfHom (ProjectiveSpace K κ) α
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace K κ) α M n
    (projectiveTopSerreMap K κ n e M).IsPerfPair := by
  let α : K →+* Γ(ProjectiveSpace K κ, ⊤) :=
    (toSpec K κ).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let := moduleCategoryLinearOfHom (ProjectiveSpace K κ) α
  let := moduleCohomologyModuleOfHom (ProjectiveSpace K κ) α M n
  let : Module.Finite K (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace K κ) M) n) :=
    projectiveCohomology_finite K κ n e M hM n
  exact LinearMap.IsPerfPair.of_bijective _ (projectiveTopSerreMap_bijective K κ n e M hM)

end AlgebraicGeometry.Scheme.Cohomology
