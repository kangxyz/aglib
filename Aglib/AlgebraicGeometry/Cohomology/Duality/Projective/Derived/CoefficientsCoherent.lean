/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Derived.CoefficientsTopHom
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.TwistExt.Coefficients
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Effacement
public import Aglib.Algebra.Homology.DerivedCategory.Ext.SingleShift
public import Aglib.CategoryTheory.Triangulated.Yoneda.Exact
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.FiveLemma

/-!
# Projective Serre duality with arbitrary base-module coefficients

For every native base module J and every coherent module M on polynomial projective
space over a Noetherian ring, the unchanged canonical comparison is bijective in every
nonnegative degree. Its literal target is full derived Hom into (single_n J)[i].
The resulting R-linear equivalence has exactly that comparison as its forward map.

The same original negative-twist presentations efface positive source Ext by the
actual positive-twist coefficient model. Their actual derived global sections have
free top homology and no other homology, so positive target Hom vanishes for arbitrary
J. Native unsigned Ext and mapped-triangle Yoneda exact rows then transfer the proved
degree-zero coefficient bijection by induction, using the actual coherent kernels.

Original source and coefficient morphisms, the ring-coefficient unitor, and the actual
unsigned extension arrow retain their original maps. No flatness or perfectness of M,
regularity of R, or flatness, finiteness, projectivity or injectivity of J is required.
Dimension zero and every higher base-ring Ext term remain in the literal target.
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
/-- The standard derived-category model for modules on `ProjectiveSpace R ι`, used locally. -/
local instance projectiveDerivedCoeffCoherentSource :
    HasDerivedCategory.{u + 1} (ProjectiveSpace R ι).Modules :=
  HasDerivedCategory.standard _
/-- The standard derived-category model for `R`-modules, used locally. -/
local instance projectiveDerivedCoeffCoherentTarget :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

/-- Positive original Ext from a finite sufficiently negative twist sum vanishes
into the literal coefficient residue twist over every commutative base ring. -/
theorem negativeTwistCoproductExt_dualizingCoefficients_subsingleton
    {I : Type u} [Finite I] (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : I → ℕ) (hN : ∀ a, Fintype.card ι ≤ N a) (J : ModuleCat.{u} R)
    (q : ℕ) (hq : q ≠ 0) :
    Subsingleton (Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
      (∐ fun a => twistingSheaf R ι (-(N a : ℤ)))
      (projectiveResidueTwistTensorCoefficients R ι J) q) := by
  let : Fintype I := Fintype.ofFinite I
  let d := fun a => twistingSheaf R ι (-(N a : ℤ))
  let : HasBiproduct d := HasBiproduct.of_hasCoproduct d
  let Ω := projectiveResidueTwistTensorCoefficients R ι J
  let : ∀ a, Subsingleton (Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules) (d a) Ω q) :=
    fun a => negativeTwistExt_dualizingCoefficients_subsingleton R ι n e
      (N a) (hN a) J q hq
  let E := (((extFunctor (C := (ProjectiveSpace R ι).Modules) q).mapIso
    (biproduct.isoCoproduct d).op).app Ω).addCommGroupIsoToAddEquiv.trans
      (Ext.biproductAddEquiv (biproduct.isBilimit d) Ω q)
  exact E.injective.subsingleton

omit [Fintype ι] in
/-- Actual derived global sections of a finite negative twist sum have zero positive
shifted Hom into every native coefficient single. Only the source top homology is projective. -/
theorem negativeTwistCoproductDerivedHomCoefficients_subsingleton {I : Type u} [Finite I]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : I → ℕ) (hN : ∀ a, 0 < N a)
    (J : ModuleCat.{u} R) (i : ℕ) (hi : i ≠ 0) :
    let P := ProjectiveSpace R ι
    let α : R →+* Γ(P, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    let A := ∐ fun a => twistingSheaf R ι (-(N a : ℤ))
    let K := ((moduleGlobalSectionsFunctorOfHom P α).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj A)
    Subsingleton (K ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).obj
      J)⟦(i : ℤ)⟧) := by
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
    (H.obj K) J (n : ℤ) (i : ℤ) (by omega)
  exact (Iso.homCongr eK (Iso.refl _)).injective.subsingleton



/-- The unchanged canonical Ext to full derived-Hom comparison is bijective in every
nonnegative degree for actual coherent coefficients over a Noetherian base ring. -/
theorem projectiveDerivedSerreMapCoefficients_bijective [IsNoetherianRing R]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (J : ModuleCat.{u} R)
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) (i : ℕ) :
    Function.Bijective (projectiveDerivedSerreMapCoefficients R ι n e J M i) := by
  induction i generalizing M with
  | zero => exact projectiveDerivedSerreMapCoefficients_zero_bijective R ι n e J M hM
  | succ i ih =>
    obtain ⟨N, hN, I, hI, π, hS, hK⟩ :=
      exists_uniformNegativeTwistCoherentPresentation R ι M hM (Fintype.card ι)
    let := hI
    let P := ProjectiveSpace R ι
    let α : R →+* Γ(P, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    let := moduleCategoryLinearOfHom P α
    let ω := projectiveResidueTwistTensorCoefficients R ι J
    let F := (moduleGlobalSectionsFunctorOfHom P α).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.ι
    let S := ShortComplex.kernelSequence π
    have hP : affineLocallyFiniteType P S.X₂ :=
      twistingCoproduct_affineLocallyFiniteType R ι (fun _ : I => -(N : ℤ))
    let T := F.mapTriangle.obj hS.singleTrianglePlus
    have hT : T ∈ distTriang (DerivedCategory (ModuleCat.{u} R)) :=
      F.map_distinguished hS.singleTrianglePlus hS.singleTrianglePlus_distinguished
    let V := (DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).obj J
    let f₁ := (Ext.mk₀ S.f).precomp ω (zero_add i)
    let f₂ := hS.extClass.precomp ω (show 1 + i = i + 1 by omega)
    let g₁ := ((preadditiveYoneda.obj (V⟦(i : ℤ)⟧)).map T.mor₁.op).hom
    let g₂ := ((preadditiveYoneda.obj V).homologySequenceδ
      ((triangleOpEquivalence _).functor.obj (op T)) (i : ℤ) ((i + 1 : ℕ) : ℤ) (by omega)).hom
    let c₁ := (projectiveDerivedSerreMapCoefficients R ι n e J S.X₂ i).toAddMonoidHom
    let c₂ := (projectiveDerivedSerreMapCoefficients R ι n e J S.X₁ i).toAddMonoidHom
    let c₃ := (projectiveDerivedSerreMapCoefficients R ι n e J S.X₃ (i + 1)).toAddMonoidHom
    have hc₁ : g₁.comp c₁ = c₂.comp f₁ := by
      ext x
      change F.map ((DerivedCategory.Plus.singleFunctor P.Modules 0).map S.f) ≫
        projectiveDerivedSerreMapCoefficients R ι n e J S.X₂ i x =
          projectiveDerivedSerreMapCoefficients R ι n e J S.X₁ i
            ((Ext.mk₀ S.f).comp x (zero_add i))
      exact (projectiveDerivedSerreMapCoefficients_naturality R ι n e J S.f i x).symm
    have hc₂ : g₂.comp c₂ = c₃.comp f₂ := by
      ext x
      change (preadditiveYoneda.obj V).homologySequenceδ
        ((triangleOpEquivalence _).functor.obj (op T)) (i : ℤ) ((i + 1 : ℕ) : ℤ)
          (by omega) (projectiveDerivedSerreMapCoefficients R ι n e J S.X₁ i x) =
            projectiveDerivedSerreMapCoefficients R ι n e J S.X₃ (i + 1)
              (hS.extClass.comp x (by omega))
      rw [preadditiveYoneda_homologySequenceδ_apply]
      simpa only [ShiftedHom.comp] using!
        (projectiveDerivedSerreMapCoefficients_extClass R ι n e J hS i (i + 1) (by omega) x).symm
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
      negativeTwistCoproductExt_dualizingCoefficients_subsingleton R ι n e
      (fun _ : I => N) (fun _ => hN) J (i + 1) (by omega)
    have hf₂ : Function.Surjective f₂ := fun x =>
      Ext.contravariant_sequence_exact₃ hS ω x (by subsingleton) (by omega)
    have hNpos : ∀ _ : I, 0 < N := by
      intro _
      have hcard := Fintype.card_congr e
      simp only [Fintype.card_fin] at hcard
      omega
    let : Subsingleton (T.obj₂ ⟶ V⟦((i + 1 : ℕ) : ℤ)⟧) :=
      negativeTwistCoproductDerivedHomCoefficients_subsingleton R ι n e
        (fun _ : I => N) hNpos J (i + 1) (by omega)
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
def projectiveDerivedSerreDualityCoefficients [IsNoetherianRing R]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (J : ModuleCat.{u} R)
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) (i : ℕ) :
    let P := ProjectiveSpace R ι
    let α : R →+* Γ(P, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCategoryLinearOfHom P α
    Ext.{u + 1} M (projectiveResidueTwistTensorCoefficients R ι J) i ≃ₗ[R]
      (((moduleGlobalSectionsFunctorOfHom P α).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj M) ⟶
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).obj
          J)⟦(i : ℤ)⟧) := by
  let P := ProjectiveSpace R ι
  let α : R →+* Γ(P, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCategoryLinearOfHom P α
  exact LinearEquiv.ofBijective (projectiveDerivedSerreMapCoefficients R ι n e J M i)
    (projectiveDerivedSerreMapCoefficients_bijective R ι n e J M hM i)

/-- The relative duality equivalence is literally the original derived Serre comparison. -/
theorem projectiveDerivedSerreDualityCoefficients_apply [IsNoetherianRing R]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (J : ModuleCat.{u} R)
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) (i : ℕ)
    (x : Ext.{u + 1} M (projectiveResidueTwistTensorCoefficients R ι J) i) :
    projectiveDerivedSerreDualityCoefficients R ι n e J M hM i x =
      projectiveDerivedSerreMapCoefficients R ι n e J M i x := rfl


/-- Every native coefficient morphism acts by the original shifted-single map. -/
theorem projectiveDerivedSerreDualityCoefficients_naturality_coefficients [IsNoetherianRing R]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {J J' : ModuleCat.{u} R} (f : J ⟶ J')
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) (i : ℕ)
    (x : Ext.{u + 1} M (projectiveResidueTwistTensorCoefficients R ι J) i) :
    projectiveDerivedSerreDualityCoefficients R ι n e J' M hM i
      (x.comp (Ext.mk₀ ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι (-(Fintype.card ι : ℤ)))).map
          ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f)))) (Nat.add_zero i)) =
    projectiveDerivedSerreDualityCoefficients R ι n e J M hM i x ≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (i : ℤ)).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).map f) := by
  rw [projectiveDerivedSerreDualityCoefficients_apply,
    projectiveDerivedSerreDualityCoefficients_apply]
  exact projectiveDerivedSerreMapCoefficients_naturality_coefficients R ι n e f M i x

/-- At the ring coefficient, the original geometric unitor recovers the old comparison. -/
theorem projectiveDerivedSerreDualityCoefficients_self [IsNoetherianRing R]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) (i : ℕ)
    (x : Ext.{u + 1} M
      (projectiveResidueTwistTensorCoefficients R ι (ModuleCat.of R R)) i) :
    projectiveDerivedSerreDualityCoefficients R ι n e (ModuleCat.of R R) M hM i x =
      projectiveDerivedSerreMap R ι n e M i
        (x.comp (Ext.mk₀ (projectiveResidueTwistTensorSelfIso R ι).hom) (Nat.add_zero i)) := by
  rw [projectiveDerivedSerreDualityCoefficients_apply]
  exact projectiveDerivedSerreMapCoefficients_self R ι n e M i x

/-- Actual source precomposition is the installed derived image of the same original map. -/
theorem projectiveDerivedSerreDualityCoefficients_naturality [IsNoetherianRing R]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (J : ModuleCat.{u} R)
    {M N : (ProjectiveSpace R ι).Modules}
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M)
    (hN : affineLocallyFiniteType (ProjectiveSpace R ι) N)
    (ψ : M ⟶ N) (i : ℕ)
    (x : Ext.{u + 1} N (projectiveResidueTwistTensorCoefficients R ι J) i) :
    projectiveDerivedSerreDualityCoefficients R ι n e J M hM i
      ((Ext.mk₀ ψ).comp x (zero_add i)) =
      ((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp
            (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
            DerivedCategory.Plus.ι).map
          ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).map ψ) ≫
        projectiveDerivedSerreDualityCoefficients R ι n e J N hN i x := by
  rw [projectiveDerivedSerreDualityCoefficients_apply,
    projectiveDerivedSerreDualityCoefficients_apply]
  exact projectiveDerivedSerreMapCoefficients_naturality R ι n e J ψ i x

/-- The same native unsigned extension arrow commutes with coefficient duality.
The protected signed Ext.δ has its separate factor Int.negOnePow j. -/
theorem projectiveDerivedSerreDualityCoefficients_extClass [IsNoetherianRing R]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (J : ModuleCat.{u} R)
    {S : ShortComplex (ProjectiveSpace R ι).Modules} (hS : S.ShortExact)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) S.X₃)
    (hK : affineLocallyFiniteType (ProjectiveSpace R ι) S.X₁)
    (i j : ℕ) (hij : 1 + i = j)
    (x : Ext.{u + 1} S.X₁ (projectiveResidueTwistTensorCoefficients R ι J) i) :
    projectiveDerivedSerreDualityCoefficients R ι n e J S.X₃ hM j (hS.extClass.comp x hij) =
      (ShiftedHom.map hS.singleTrianglePlus.mor₃
        ((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp
            (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
            DerivedCategory.Plus.ι)).comp
        (projectiveDerivedSerreDualityCoefficients R ι n e J S.X₁ hK i x) (by omega) := by
  rw [projectiveDerivedSerreDualityCoefficients_apply,
    projectiveDerivedSerreDualityCoefficients_apply]
  exact projectiveDerivedSerreMapCoefficients_extClass R ι n e J hS i j hij x

end AlgebraicGeometry.Scheme.Cohomology
