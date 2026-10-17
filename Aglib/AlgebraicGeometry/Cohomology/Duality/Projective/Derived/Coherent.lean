/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Derived.TopHom
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Effacement
public import Aglib.Algebra.Homology.DerivedCategory.Ext.SingleShift
public import Aglib.CategoryTheory.Triangulated.Yoneda.Exact
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.FiveLemma

/-!
# Relative projective Serre duality in full derived Hom

For coherent module coefficients over a Noetherian base ring, the original canonical
Ext to full derived-Hom comparison is bijective in every nonnegative degree. Actual
uniform negative-twist presentations have coherent kernels. Their original positive
Ext vanishes, and their actual derived global sections are free concentrated singles,
so positive target derived Hom vanishes over every commutative ring.

Native unsigned Ext and mapped-triangle Yoneda exact rows, with the proved original
coefficient and extension compatibilities, transfer the degree-zero bijection by
induction. The resulting linear equivalence retains the unchanged comparison as its
forward map. No coefficient flatness, perfectness or base regularity is assumed.
Dimension zero and all higher base-ring Ext terms are retained.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u) [Fintype ι]

/-- The standard derived-category structure on the indicated module category. -/
local instance projectiveDerivedCoherentSource :
    HasDerivedCategory.{u + 1} (ProjectiveSpace R ι).Modules :=
  HasDerivedCategory.standard _
/-- The standard derived-category structure on the indicated module category. -/
local instance projectiveDerivedCoherentTarget :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

omit [Fintype ι] in
/-- Actual derived global sections of a finite negative-twist sum have no positive
shifted Hom to the top-degree scalar single, over every commutative ring. -/
theorem negativeTwistCoproductDerivedHom_subsingleton {I : Type u} [Finite I]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : I → ℕ) (hN : ∀ a, 0 < N a)
    (i : ℕ) (hi : i ≠ 0) :
    let P := ProjectiveSpace R ι
    let α : R →+* Γ(P, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    let A := ∐ fun a => twistingSheaf R ι (-(N a : ℤ))
    let K := ((moduleGlobalSectionsFunctorOfHom P α).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj A)
    Subsingleton (K ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).obj
      (ModuleCat.of R R))⟦(i : ℤ)⟧) := by
  let P := ProjectiveSpace R ι
  let α : R →+* Γ(P, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let A := ∐ fun a => twistingSheaf R ι (-(N a : ℤ))
  let F := (moduleGlobalSectionsFunctorOfHom P α).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι
  let K := F.obj ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj A)
  have hd : ∀ a, -(N a : ℤ) < 0 := by intro a; have := hN a; omega
  have hz (j : ℤ) (hj : j ≠ (n : ℤ)) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).obj K) := by
    by_cases hj0 : 0 ≤ j
    · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hj0
      let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv P α
        (injectiveResolution A) q
      let := twistingCoproductCohomology_subsingleton_of_neg_degree R ι n e
        (fun a => -(N a : ℤ)) hd q (by exact_mod_cast hj)
      exact ModuleCat.isZero_iff_subsingleton.mpr E.injective.subsingleton
    · exact (moduleGlobalSectionsFunctorOfHom P α).isZero_homology_rightDerivedFunctorPlus_of_isGE
        ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj A) 0 j (by omega)
  let : K.IsGE (n : ℤ) := (DerivedCategory.isGE_iff K _).mpr
    (fun j hj => hz j (ne_of_lt hj))
  let : K.IsLE (n : ℤ) := (DerivedCategory.isLE_iff K _).mpr
    (fun j hj => hz j (ne_of_gt hj))
  let := moduleCohomologyModuleOfHom P α A n
  let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv P α
    (injectiveResolution A) n
  let := twistingCoproductCohomology_free R ι n e (fun a => -(N a : ℤ)) n
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)
  let : Module.Free R (H.obj K) := Module.Free.of_equiv E.symm
  let : Projective (H.obj K) :=
    ModuleCat.projective_of_free (Module.Free.chooseBasis R (H.obj K))
  let eK := DerivedCategory.isoSingleHomology K (n : ℤ)
  let := DerivedCategory.subsingleton_shiftedHom_singleFunctor_of_projective
    (H.obj K) (ModuleCat.of R R) (n : ℤ) (i : ℤ) (by omega)
  exact (Iso.homCongr eK (Iso.refl _)).injective.subsingleton


/-- The unchanged canonical Ext to full derived-Hom comparison is bijective in every
nonnegative degree for actual coherent coefficients over a Noetherian base ring. -/
theorem projectiveDerivedSerreMap_bijective [IsNoetherianRing R]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) (i : ℕ) :
    Function.Bijective (projectiveDerivedSerreMap R ι n e M i) := by
  induction i generalizing M with
  | zero => exact projectiveDerivedSerreMap_zero_bijective R ι n e M hM
  | succ i ih =>
    obtain ⟨N, hN, I, hI, π, hS, hK⟩ :=
      exists_uniformNegativeTwistCoherentPresentation R ι M hM (Fintype.card ι)
    let := hI
    let P := ProjectiveSpace R ι
    let α : R →+* Γ(P, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    let := moduleCategoryLinearOfHom P α
    let ω := twistingSheaf R ι (-(Fintype.card ι : ℤ))
    let F := (moduleGlobalSectionsFunctorOfHom P α).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.ι
    let S := ShortComplex.kernelSequence π
    have hP : affineLocallyFiniteType P S.X₂ :=
      twistingCoproduct_affineLocallyFiniteType R ι (fun _ : I => -(N : ℤ))
    let T := F.mapTriangle.obj hS.singleTrianglePlus
    have hT : T ∈ distTriang (DerivedCategory (ModuleCat.{u} R)) :=
      F.map_distinguished hS.singleTrianglePlus hS.singleTrianglePlus_distinguished
    let V := (DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).obj (ModuleCat.of R R)
    let f₁ := (Ext.mk₀ S.f).precomp ω (zero_add i)
    let f₂ := hS.extClass.precomp ω (show 1 + i = i + 1 by omega)
    let g₁ := ((preadditiveYoneda.obj (V⟦(i : ℤ)⟧)).map T.mor₁.op).hom
    let g₂ := ((preadditiveYoneda.obj V).homologySequenceδ
      ((triangleOpEquivalence _).functor.obj (op T)) (i : ℤ) ((i + 1 : ℕ) : ℤ) (by omega)).hom
    let c₁ := (projectiveDerivedSerreMap R ι n e S.X₂ i).toAddMonoidHom
    let c₂ := (projectiveDerivedSerreMap R ι n e S.X₁ i).toAddMonoidHom
    let c₃ := (projectiveDerivedSerreMap R ι n e S.X₃ (i + 1)).toAddMonoidHom
    have hc₁ : g₁.comp c₁ = c₂.comp f₁ := by
      ext x
      change F.map ((DerivedCategory.Plus.singleFunctor P.Modules 0).map S.f) ≫
        projectiveDerivedSerreMap R ι n e S.X₂ i x =
          projectiveDerivedSerreMap R ι n e S.X₁ i
            ((Ext.mk₀ S.f).comp x (zero_add i))
      exact (projectiveDerivedSerreMap_naturality R ι n e S.f i x).symm
    have hc₂ : g₂.comp c₂ = c₃.comp f₂ := by
      ext x
      change (preadditiveYoneda.obj V).homologySequenceδ
        ((triangleOpEquivalence _).functor.obj (op T)) (i : ℤ) ((i + 1 : ℕ) : ℤ)
          (by omega) (projectiveDerivedSerreMap R ι n e S.X₁ i x) =
            projectiveDerivedSerreMap R ι n e S.X₃ (i + 1)
              (hS.extClass.comp x (by omega))
      rw [preadditiveYoneda_homologySequenceδ_apply]
      simpa only [ShiftedHom.comp] using!
        (projectiveDerivedSerreMap_extClass R ι n e hS i (i + 1) (by omega) x).symm
    have hf : Function.Exact f₁ f₂ :=
      (ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.contravariant_sequence_exact₁' hS ω i (i + 1) (by omega))
    have hg : Function.Exact g₁ g₂ := by
      have h := yoneda_exact_precomp_boundary T hT V (i : ℤ) ((i + 1 : ℕ) : ℤ) (by omega)
      change Function.Exact (fun f => T.mor₁ ≫ f)
        (fun f => (preadditiveYoneda.obj V).homologySequenceδ
          ((triangleOpEquivalence _).functor.obj (op T)) (i : ℤ) ((i + 1 : ℕ) : ℤ)
            (by omega) f)
      simp only [preadditiveYoneda_homologySequenceδ_apply]
      simpa only [Functor.shift, ShiftedHom.comp] using! h
    let : Subsingleton (Ext.{u + 1} S.X₂ ω (i + 1)) :=
      negativeTwistCoproductExt_dualizing_subsingleton R ι n e
      (fun _ : I => N) (fun _ => hN) (i + 1) (by omega)
    have hf₂ : Function.Surjective f₂ := fun x =>
      Ext.contravariant_sequence_exact₃ hS ω x (by subsingleton) (by omega)
    have hNpos : ∀ _ : I, 0 < N := by
      intro _
      have hcard := Fintype.card_congr e
      simp only [Fintype.card_fin] at hcard
      omega
    let : Subsingleton (T.obj₂ ⟶ V⟦((i + 1 : ℕ) : ℤ)⟧) :=
      negativeTwistCoproductDerivedHom_subsingleton R ι n e
        (fun _ : I => N) hNpos (i + 1) (by omega)
    have hg₂ : Function.Surjective g₂ := by
      intro z
      obtain ⟨x, hx⟩ := yoneda_boundary_surjective_of_subsingleton T hT V
        (i : ℤ) ((i + 1 : ℕ) : ℤ) (by omega) z
      refine ⟨x, ?_⟩
      change (preadditiveYoneda.obj V).homologySequenceδ
        ((triangleOpEquivalence _).functor.obj (op T)) (i : ℤ) ((i + 1 : ℕ) : ℤ) (by omega) x = z
      rw [preadditiveYoneda_homologySequenceδ_apply]
      exact hx
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      f₁ f₂ g₁ g₂ c₁ c₂ c₃ hc₁ hc₂ hf hg
      (ih S.X₂ hP).surjective (ih S.X₁ hK) hf₂ hg₂


/-- Relative Serre duality on polynomial projective space over an affine Noetherian base,
with the original canonical comparison as its forward linear map. -/
def projectiveDerivedSerreDuality [IsNoetherianRing R]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) (i : ℕ) :
    let P := ProjectiveSpace R ι
    let α : R →+* Γ(P, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCategoryLinearOfHom P α
    Ext.{u + 1} M (twistingSheaf R ι (-(Fintype.card ι : ℤ))) i ≃ₗ[R]
      (((moduleGlobalSectionsFunctorOfHom P α).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj M) ⟶
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).obj
          (ModuleCat.of R R))⟦(i : ℤ)⟧) := by
  let P := ProjectiveSpace R ι
  let α : R →+* Γ(P, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCategoryLinearOfHom P α
  exact LinearEquiv.ofBijective (projectiveDerivedSerreMap R ι n e M i)
    (projectiveDerivedSerreMap_bijective R ι n e M hM i)

/-- The relative duality equivalence is literally the original derived Serre comparison. -/
theorem projectiveDerivedSerreDuality_apply [IsNoetherianRing R]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) (i : ℕ)
    (x : Ext.{u + 1} M (twistingSheaf R ι (-(Fintype.card ι : ℤ))) i) :
    projectiveDerivedSerreDuality R ι n e M hM i x =
      projectiveDerivedSerreMap R ι n e M i x := rfl

end AlgebraicGeometry.Scheme.Cohomology
