/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Derived.Coefficients
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Derived.Comparison

/-!
# The canonical projective Ext comparison with arbitrary coefficients

For every base module `J` and scheme-module coefficient `M`, original Ext classes into
`omega ⊗ π*tilde(J)` lift through native `Ext.homPlus`, map through the installed right-derived
global-sections functor and its native shift comparison, and compose with the shifted
actual coefficient trace. The target is literal full derived Hom into `J[i-n]`.

The map is R-linear for the original structural scalar action, natural under both native
source precomposition and base-coefficient morphisms, and compatible with the actual
unsigned extension arrow. At the ring coefficient, the original geometric unitors
identify it with the unchanged original projective Ext comparison in every degree.
Degree zero uses precisely the original coefficient map on additive-sheaf cohomology
followed by the specified trace to `J`, through every supplied source resolution.

Every commutative ring, projective dimension zero, and arbitrary module coefficients are
retained. No coherence, Noetherianity, flatness, projectivity, injectivity, generic
RF-linearity, source bound or duality premise is assumed. Bijectivity is not asserted here.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u) [Fintype ι]

/-- The standard derived-category model for modules on `ProjectiveSpace R ι`, used locally. -/
local instance projectiveDerivedSerreCoefficientsSource :
    HasDerivedCategory.{u + 1} (ProjectiveSpace R ι).Modules :=
  HasDerivedCategory.standard _
/-- The standard derived-category model for `R`-modules, used locally. -/
local instance projectiveDerivedSerreCoefficientsTarget :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

/-- Native Ext maps linearly to full derived Hom using the actual coefficient trace to `J`. -/
def projectiveDerivedSerreMapCoefficients (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R)
    (M : (ProjectiveSpace R ι).Modules) (i : ℕ) :
    let P := ProjectiveSpace R ι
    let α : R →+* Γ(P, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCategoryLinearOfHom P α
    Ext.{u + 1} M (projectiveResidueTwistTensorCoefficients R ι J) i →ₗ[R]
      (((moduleGlobalSectionsFunctorOfHom P α).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj M) ⟶
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).obj
          J)⟦(i : ℤ)⟧) := by
  let P := ProjectiveSpace R ι
  let α : R →+* Γ(P, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := moduleCategoryLinearOfHom P α
  let ω := projectiveResidueTwistTensorCoefficients R ι J
  let F := (moduleGlobalSectionsFunctorOfHom P α).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι
  let t := ShiftedHom.mk₀ (0 : ℤ) rfl (projectiveDerivedTraceCoefficients R ι n e J)
  refine {
    toFun := fun x => (x.homPlus.map F).comp t (zero_add _)
    map_add' := fun x y => ?_
    map_smul' := fun r x => ?_ }
  · have h : (x + y).homPlus = x.homPlus + y.homPlus :=
      (Ext.homPlusAddEquiv i).map_add x y
    rw [h, ShiftedHom.map_add, ShiftedHom.add_comp]
  · have ht := projectiveDerivedTraceCoefficients_smul R ι n e J r
    change F.map ((DerivedCategory.Plus.singleFunctor P.Modules 0).map (r • 𝟙 ω)) ≫
      projectiveDerivedTraceCoefficients R ι n e J =
      r • projectiveDerivedTraceCoefficients R ι n e J at ht
    rw [Ext.smul_eq_comp_mk₀, Ext.homPlus_comp, Ext.homPlus_mk₀,
      ShiftedHom.map_comp]
    erw [ShiftedHom.map_mk₀]
    dsimp only [t]
    rw [ShiftedHom.comp_mk₀, ShiftedHom.comp_mk₀, ShiftedHom.comp_mk₀,
      Category.assoc, ← Functor.map_comp, ht, Functor.map_smul, Linear.comp_smul]
    rfl

/-- The forward arrow is literally the native shifted-Hom image followed by shifted trace. -/
theorem projectiveDerivedSerreMapCoefficients_apply (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R)
    (M : (ProjectiveSpace R ι).Modules) (i : ℕ)
    (x : Ext.{u + 1} M (projectiveResidueTwistTensorCoefficients R ι J) i) :
    projectiveDerivedSerreMapCoefficients R ι n e J M i x =
      (x.homPlus.map ((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp
            (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
            DerivedCategory.Plus.ι)) ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (i : ℤ)).map
          (projectiveDerivedTraceCoefficients R ι n e J) := by
  let F := (moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp
          (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.ι
  exact ShiftedHom.comp_mk₀ (x.homPlus.map F) (0 : ℤ) rfl
    (projectiveDerivedTraceCoefficients R ι n e J)

/-- The comparison preserves original Yoneda precomposition in every nonnegative degree. -/
theorem projectiveDerivedSerreMapCoefficients_comp (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R)
    {M N : (ProjectiveSpace R ι).Modules} {a b c : ℕ}
    (x : Ext.{u + 1} M N a)
    (y : Ext.{u + 1} N (projectiveResidueTwistTensorCoefficients R ι J) b)
    (h : a + b = c) :
    projectiveDerivedSerreMapCoefficients R ι n e J M c (x.comp y h) =
      (x.homPlus.map ((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp
            (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
            DerivedCategory.Plus.ι)).comp
        (projectiveDerivedSerreMapCoefficients R ι n e J N b y) (by omega) := by
  let P := ProjectiveSpace R ι
  let α : R →+* Γ(P, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let F := (moduleGlobalSectionsFunctorOfHom P α).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι
  let t := ShiftedHom.mk₀ (0 : ℤ) rfl (projectiveDerivedTraceCoefficients R ι n e J)
  change ((x.comp y h).homPlus.map F).comp t (zero_add _) =
    (x.homPlus.map F).comp ((y.homPlus.map F).comp t (zero_add _)) (by omega)
  rw [Ext.homPlus_comp, ShiftedHom.map_comp]
  exact ShiftedHom.comp_assoc _ _ _ (by omega) (zero_add _) (by omega)

/-- Original coefficient precomposition is the installed derived image of the same map. -/
theorem projectiveDerivedSerreMapCoefficients_naturality (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R)
    {M N : (ProjectiveSpace R ι).Modules} (ψ : M ⟶ N) (i : ℕ)
    (y : Ext.{u + 1} N (projectiveResidueTwistTensorCoefficients R ι J) i) :
    projectiveDerivedSerreMapCoefficients R ι n e J M i ((Ext.mk₀ ψ).comp y (zero_add i)) =
      ((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp
            (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
            DerivedCategory.Plus.ι).map
          ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).map ψ) ≫
        projectiveDerivedSerreMapCoefficients R ι n e J N i y := by
  rw [projectiveDerivedSerreMapCoefficients_comp, Ext.homPlus_mk₀]
  erw [ShiftedHom.map_mk₀]
  rw [ShiftedHom.mk₀_comp]

/-- The original unsigned extension class is the actual bounded-below connecting arrow.
The protected signed `Ext.δ` has the separate native factor `Int.negOnePow j`. -/
theorem projectiveDerivedSerreMapCoefficients_extClass (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R)
    {S : ShortComplex (ProjectiveSpace R ι).Modules} (hS : S.ShortExact)
    (i j : ℕ) (hij : 1 + i = j)
    (y : Ext.{u + 1} S.X₁ (projectiveResidueTwistTensorCoefficients R ι J) i) :
    projectiveDerivedSerreMapCoefficients R ι n e J S.X₃ j (hS.extClass.comp y hij) =
      (ShiftedHom.map hS.singleTrianglePlus.mor₃
        ((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp
            (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
            DerivedCategory.Plus.ι)).comp
        (projectiveDerivedSerreMapCoefficients R ι n e J S.X₁ i y) (by omega) := by
  rw [projectiveDerivedSerreMapCoefficients_comp, Ext.homPlus_extClass]

/-- Degree zero is the native shifted-Hom class of the original coefficient map and trace. -/
theorem projectiveDerivedSerreMapCoefficients_mk₀ (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R)
    (M : (ProjectiveSpace R ι).Modules)
    (f : M ⟶ projectiveResidueTwistTensorCoefficients R ι J) :
    projectiveDerivedSerreMapCoefficients R ι n e J M 0 (Ext.mk₀ f) =
      ShiftedHom.mk₀ (0 : ℤ) rfl
        (((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp
            (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
            DerivedCategory.Plus.ι).map
          ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).map f) ≫
            projectiveDerivedTraceCoefficients R ι n e J) := by
  let F := (moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp
          (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.ι
  change ((Ext.mk₀ f).homPlus.map F).comp
    (ShiftedHom.mk₀ (0 : ℤ) rfl (projectiveDerivedTraceCoefficients R ι n e J))
      (zero_add _) = _
  rw [Ext.homPlus_mk₀]
  erw [ShiftedHom.map_mk₀]
  exact ShiftedHom.mk₀_comp_mk₀ _ _ _ rfl rfl

/-- Through any supplied source resolution, degree zero is the original coefficient map on
additive-sheaf cohomology followed by the specified trace to `J`, without a source upper bound. -/
theorem projectiveDerivedSerreMapCoefficients_mk₀_homology_apply (n : ℕ)
    (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R)
    (M : (ProjectiveSpace R ι).Modules) (I : InjectiveResolution M)
    (f : M ⟶ projectiveResidueTwistTensorCoefficients R ι J)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).obj
      (((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp
          (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.ι).obj
        ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).obj M))) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) (n : ℤ)).hom.app
        J
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
          ((ShiftedHom.homEquiv (0 : ℤ) rfl).symm
            (projectiveDerivedSerreMapCoefficients R ι n e J M 0 (Ext.mk₀ f))) x) =
      projectiveTraceCoefficientsLinearEquiv R ι n e J
        (moduleCohomologyMapOfHom (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) f n
          (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv (ProjectiveSpace R ι)
            ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) I n x)) := by
  let P := ProjectiveSpace R ι
  let α : R →+* Γ(P, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let ω := projectiveResidueTwistTensorCoefficients R ι J
  let F := (moduleGlobalSectionsFunctorOfHom P α).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι
  let d := F.map ((DerivedCategory.Plus.singleFunctor P.Modules 0).map f)
  let Iω := injectiveResolution ω
  let φ : InjectiveResolution.Hom I Iω f :=
    ⟨InjectiveResolution.desc f Iω I, by
      simpa only [CochainComplex.single₀_map_f_zero] using
        InjectiveResolution.desc_commutes_zero f Iω I⟩
  have h0 : (ShiftedHom.homEquiv (0 : ℤ) rfl).symm
      (projectiveDerivedSerreMapCoefficients R ι n e J M 0 (Ext.mk₀ f)) =
        d ≫ projectiveDerivedTraceCoefficients R ι n e J := by
    rw [projectiveDerivedSerreMapCoefficients_mk₀]
    exact (ShiftedHom.homEquiv (0 : ℤ) rfl).symm_apply_apply _
  erw [h0]
  simp only [Functor.map_comp, ModuleCat.comp_apply]
  have ht := projectiveDerivedTraceCoefficients_homology_apply R ι n e J Iω
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map d x)
  refine ht.trans ?_
  have hn := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_naturality P α φ n x
  exact congrArg (projectiveTraceCoefficientsLinearEquiv R ι n e J) hn

/-- Every original base-coefficient morphism is native shifted-single postcomposition. -/
theorem projectiveDerivedSerreMapCoefficients_naturality_coefficients (n : ℕ)
    (e : ι ≃ Fin (n + 1)) {J J' : ModuleCat.{u} R} (f : J ⟶ J')
    (M : (ProjectiveSpace R ι).Modules) (i : ℕ)
    (x : Ext.{u + 1} M (projectiveResidueTwistTensorCoefficients R ι J) i) :
    projectiveDerivedSerreMapCoefficients R ι n e J' M i
      (x.comp (Ext.mk₀ ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι (-(Fintype.card ι : ℤ)))).map
          ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f)))) (Nat.add_zero i)) =
    projectiveDerivedSerreMapCoefficients R ι n e J M i x ≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (i : ℤ)).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).map f) := by
  let X := ProjectiveSpace R ι
  let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let F := (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι
  let g := (moduleTensorLeftFunctor X (twistingSheaf R ι (-(Fintype.card ι : ℤ)))).map
    ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f))
  have ht := projectiveDerivedTraceCoefficients_naturality R ι n e f
  change F.map ((DerivedCategory.Plus.singleFunctor X.Modules 0).map g) ≫
      projectiveDerivedTraceCoefficients R ι n e J' =
    projectiveDerivedTraceCoefficients R ι n e J ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).map f at ht
  rw [projectiveDerivedSerreMapCoefficients_apply,
    projectiveDerivedSerreMapCoefficients_apply, Ext.homPlus_comp, Ext.homPlus_mk₀,
    ShiftedHom.map_comp]
  erw [ShiftedHom.map_mk₀]
  rw [ShiftedHom.comp_mk₀, Category.assoc, ← Functor.map_comp, ht,
    Functor.map_comp, Category.assoc]

/-- At `J = R`, original Ext postcomposition by the geometric unitor recovers the old comparison. -/
theorem projectiveDerivedSerreMapCoefficients_self (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules) (i : ℕ)
    (x : Ext.{u + 1} M (projectiveResidueTwistTensorCoefficients R ι (ModuleCat.of R R)) i) :
    projectiveDerivedSerreMapCoefficients R ι n e (ModuleCat.of R R) M i x =
    projectiveDerivedSerreMap R ι n e M i
      (x.comp (Ext.mk₀ (projectiveResidueTwistTensorSelfIso R ι).hom) (Nat.add_zero i)) := by
  let X := ProjectiveSpace R ι
  let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let F := (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι
  have ht := projectiveDerivedTraceCoefficients_self R ι n e
  change projectiveDerivedTraceCoefficients R ι n e (ModuleCat.of R R) =
    F.map ((DerivedCategory.Plus.singleFunctor X.Modules 0).map
      (projectiveResidueTwistTensorSelfIso R ι).hom) ≫
      projectiveDerivedTrace R ι n e at ht
  rw [projectiveDerivedSerreMapCoefficients_apply, projectiveDerivedSerreMap_apply,
    Ext.homPlus_comp, Ext.homPlus_mk₀, ShiftedHom.map_comp]
  erw [ShiftedHom.map_mk₀]
  rw [ShiftedHom.comp_mk₀, Category.assoc, ← Functor.map_comp, ← ht]

end AlgebraicGeometry.Scheme.Cohomology
