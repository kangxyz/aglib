/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Top
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.HigherStep
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Effacement

/-!
# Coherent Serre duality in every complementary degree on projective space

For every field and every projective dimension, the original Yoneda/trace pairing
identifies Ext into the actual dualizing twist with the linear dual of original sheaf
cohomology. The proof uses the actual uniform negative-twist coherent presentations and
native exact sequences. Every degree, including dimension zero, is retained.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (K : Type u) [Field K] (ι : Type u) [Fintype ι]

/-- The canonical Yoneda/trace Serre pairing is bijective in every pair of complementary
degrees for every coherent coefficient on the actual polynomial projective space. -/
theorem projectiveSerrePairing_bijective (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace K ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace K ι) M)
    (i j : ℕ) (hij : i + j = n) :
    Function.Bijective (projectiveSerrePairing K ι n e M i j hij) := by
  induction j generalizing M i with
  | zero =>
    have hi : i = n := by omega
    subst i
    let α : K →+* Γ(ProjectiveSpace K ι, ⊤) :=
      (toSpec K ι).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
    let := moduleCategoryLinearOfHom (ProjectiveSpace K ι) α
    let := moduleCohomologyModuleOfHom (ProjectiveSpace K ι) α M n
    let E : Ext.{u + 1} (C := (ProjectiveSpace K ι).Modules)
        M (twistingSheaf K ι (-(Fintype.card ι : ℤ))) 0 ≃ₗ[K]
          (M ⟶ twistingSheaf K ι (-(Fintype.card ι : ℤ))) :=
      Ext.linearEquiv₀ (R := K) (C := (ProjectiveSpace K ι).Modules)
    have htop := projectiveTopSerreMap_bijective K ι n e M hM
    have heq (y : Ext.{u + 1} (C := (ProjectiveSpace K ι).Modules)
        M (twistingSheaf K ι (-(Fintype.card ι : ℤ))) 0) :
        projectiveTopSerreMap K ι n e M (E y) =
          projectiveSerrePairing K ι n e M n 0 hij y := by
      change projectiveSerrePairing K ι n e M n 0 hij (E.symm (E y)) = _
      rw [E.symm_apply_apply]
    constructor
    · intro x y hxy
      apply E.injective
      apply htop.injective
      rw [heq, heq]
      exact hxy
    · intro x
      obtain ⟨f, hf⟩ := htop.surjective x
      refine ⟨E.symm f, ?_⟩
      rw [← heq (E.symm f), E.apply_symm_apply]
      exact hf
  | succ j ih =>
    obtain ⟨N, hN, I, hI, π, hS, hKer⟩ :=
      exists_uniformNegativeTwistCoherentPresentation K ι M hM (Fintype.card ι)
    let := hI
    have hcard : Fintype.card ι = n + 1 :=
      (Fintype.card_congr e).trans (Fintype.card_fin _)
    have hN0 : 0 < N := by omega
    have hdN : -(N : ℤ) < 0 := by omega
    apply projectiveSerrePairing_bijective_of_shortExact K ι n e
      (ShortComplex.kernelSequence π) hS i j (by omega)
    · exact twistingCoproductCohomology_subsingleton_of_neg_degree K ι n e
        (fun _ : I => -(N : ℤ)) (fun _ => hdN) i (by omega)
    · exact negativeTwistCoproductExt_dualizing_subsingleton K ι n e
        (fun _ : I => N) (fun _ => hN) (j + 1) (by omega)
    · exact ih _ (twistingCoproduct_affineLocallyFiniteType K ι
        (fun _ : I => -(N : ℤ))) (i + 1) (by omega)
    · exact ih _ hKer (i + 1) (by omega)

/-- Over a field the original coherent Serre pairing is perfect in both inputs in every
pair of complementary degrees. Finiteness is the proved finiteness of original cohomology. -/
theorem projectiveSerrePairing_isPerfPair (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace K ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace K ι) M)
    (i j : ℕ) (hij : i + j = n) :
    let α : K →+* Γ(ProjectiveSpace K ι, ⊤) :=
      (toSpec K ι).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
    letI := moduleCategoryLinearOfHom (ProjectiveSpace K ι) α
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace K ι) α M i
    (projectiveSerrePairing K ι n e M i j hij).IsPerfPair := by
  let α : K →+* Γ(ProjectiveSpace K ι, ⊤) :=
    (toSpec K ι).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let := moduleCategoryLinearOfHom (ProjectiveSpace K ι) α
  let := moduleCohomologyModuleOfHom (ProjectiveSpace K ι) α M i
  let : Module.Finite K (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace K ι) M) i) :=
    projectiveCohomology_finite K ι n e M hM i
  exact LinearMap.IsPerfPair.of_bijective _
    (projectiveSerrePairing_bijective K ι n e M hM i j hij)

/-- Native Ext into the actual dualizing twist is the linear dual of the unchanged original
cohomology in the complementary degree, by the original Yoneda/trace map. -/
def projectiveSerreDuality (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace K ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace K ι) M)
    (i j : ℕ) (hij : i + j = n) :
    let α : K →+* Γ(ProjectiveSpace K ι, ⊤) :=
      (toSpec K ι).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
    letI := moduleCategoryLinearOfHom (ProjectiveSpace K ι) α
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace K ι) α M i
    Ext.{u + 1} (C := (ProjectiveSpace K ι).Modules)
      M (twistingSheaf K ι (-(Fintype.card ι : ℤ))) j ≃ₗ[K]
        Module.Dual K (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace K ι) M) i) := by
  let α : K →+* Γ(ProjectiveSpace K ι, ⊤) :=
    (toSpec K ι).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  letI := moduleCategoryLinearOfHom (ProjectiveSpace K ι) α
  letI := moduleCohomologyModuleOfHom (ProjectiveSpace K ι) α M i
  exact LinearEquiv.ofBijective (projectiveSerrePairing K ι n e M i j hij)
    (projectiveSerrePairing_bijective K ι n e M hM i j hij)

/-- The actual coherent duality retains literal Yoneda composition and the original trace. -/
theorem projectiveSerreDuality_apply (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace K ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace K ι) M)
    (i j : ℕ) (hij : i + j = n)
    (y : Ext.{u + 1} (C := (ProjectiveSpace K ι).Modules)
      M (twistingSheaf K ι (-(Fintype.card ι : ℤ))) j)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace K ι) M) i) :
    projectiveSerreDuality K ι n e M hM i j hij y x =
      projectiveTrace K ι n e (moduleExtCohomologyMap (ProjectiveSpace K ι)
        (twistingSheaf K ι (-(Fintype.card ι : ℤ))) n
          (((moduleExtCohomologyAddEquiv (ProjectiveSpace K ι) M i).symm x).comp y hij)) :=
  projectiveSerrePairing_apply K ι n e M i j hij y x

/-- Coherent Serre duality keeps the original coefficient map on cohomology and native
precomposition on Ext. -/
theorem projectiveSerreDuality_naturality (n : ℕ) (e : ι ≃ Fin (n + 1))
    {M N : (ProjectiveSpace K ι).Modules}
    (hM : affineLocallyFiniteType (ProjectiveSpace K ι) M)
    (hN : affineLocallyFiniteType (ProjectiveSpace K ι) N)
    (f : M ⟶ N) (i j : ℕ) (hij : i + j = n)
    (y : Ext.{u + 1} (C := (ProjectiveSpace K ι).Modules)
      N (twistingSheaf K ι (-(Fintype.card ι : ℤ))) j)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace K ι) M) i) :
    projectiveSerreDuality K ι n e M hM i j hij
        ((Ext.mk₀ (C := (ProjectiveSpace K ι).Modules) f).comp y (Nat.zero_add j)) x =
      projectiveSerreDuality K ι n e N hN i j hij y
        (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace K ι).ringCatSheaf).map f) i x) :=
  projectiveSerrePairing_naturality K ι n e f i j hij y x

/-- The original cohomology is also the dual of native Ext in complementary degree, through
the flipped original perfect pairing. -/
def projectiveSerreCohomologyDuality (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace K ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace K ι) M)
    (i j : ℕ) (hij : i + j = n) :
    let α : K →+* Γ(ProjectiveSpace K ι, ⊤) :=
      (toSpec K ι).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
    letI := moduleCategoryLinearOfHom (ProjectiveSpace K ι) α
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace K ι) α M i
    Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace K ι) M) i ≃ₗ[K]
      Module.Dual K (Ext.{u + 1} (C := (ProjectiveSpace K ι).Modules)
        M (twistingSheaf K ι (-(Fintype.card ι : ℤ))) j) := by
  let α : K →+* Γ(ProjectiveSpace K ι, ⊤) :=
    (toSpec K ι).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  letI := moduleCategoryLinearOfHom (ProjectiveSpace K ι) α
  letI := moduleCohomologyModuleOfHom (ProjectiveSpace K ι) α M i
  letI : (projectiveSerrePairing K ι n e M i j hij).IsPerfPair :=
    projectiveSerrePairing_isPerfPair K ι n e M hM i j hij
  exact (projectiveSerrePairing K ι n e M i j hij).flip.toPerfPair

/-- The cohomology-side duality evaluates by the same original pairing, with the inputs
interchanged and no change of trace or Yoneda product. -/
theorem projectiveSerreCohomologyDuality_apply (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace K ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace K ι) M)
    (i j : ℕ) (hij : i + j = n)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace K ι) M) i)
    (y : Ext.{u + 1} (C := (ProjectiveSpace K ι).Modules)
      M (twistingSheaf K ι (-(Fintype.card ι : ℤ))) j) :
    projectiveSerreCohomologyDuality K ι n e M hM i j hij x y =
      projectiveSerrePairing K ι n e M i j hij y x := rfl

end AlgebraicGeometry.Scheme.Cohomology
