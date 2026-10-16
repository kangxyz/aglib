/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Ext
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Derived.Trace
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Pairing

/-!
# The canonical projective Ext to derived Hom comparison

Original module Ext classes lift through the native bounded-below inclusion, map through
the installed right-derived global-sections functor and its shift comparison, and compose
with the shifted original derived residue trace. The target is literal full derived Hom
into `R[i-n]`, retaining higher base-ring Ext terms.

The comparison is linear for the original structural scalar action, natural under native
coefficient precomposition, and compatible with the actual unsigned extension arrow.
Degree zero induces exactly the existing canonical top Serre map on original cohomology.
All module coefficients over every commutative ring and dimension zero are retained.
No coherence, flatness, Noetherianity, generic RF-linearity or duality premise is imposed.
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

local instance projectiveDerivedSerreSource :
    HasDerivedCategory.{u + 1} (ProjectiveSpace R ι).Modules :=
  HasDerivedCategory.standard _
local instance projectiveDerivedSerreTarget : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

/-- Native Ext maps linearly to full derived Hom by the original bounded-below lift,
installed right derivation with its native shift comparison, and shifted residue trace. -/
def projectiveDerivedSerreMap (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules) (i : ℕ) :
    let P := ProjectiveSpace R ι
    let α : R →+* Γ(P, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCategoryLinearOfHom P α
    Ext.{u + 1} M (twistingSheaf R ι (-(Fintype.card ι : ℤ))) i →ₗ[R]
      (((moduleGlobalSectionsFunctorOfHom P α).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj M) ⟶
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).obj
          (ModuleCat.of R R))⟦(i : ℤ)⟧) := by
  let P := ProjectiveSpace R ι
  let α : R →+* Γ(P, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := moduleCategoryLinearOfHom P α
  let ω := twistingSheaf R ι (-(Fintype.card ι : ℤ))
  let F := (moduleGlobalSectionsFunctorOfHom P α).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι
  let t := ShiftedHom.mk₀ (0 : ℤ) rfl (projectiveDerivedTrace R ι n e)
  refine {
    toFun := fun x => (x.homPlus.map F).comp t (zero_add _)
    map_add' := fun x y => ?_
    map_smul' := fun r x => ?_ }
  · have h : (x + y).homPlus = x.homPlus + y.homPlus :=
      (Ext.homPlusAddEquiv i).map_add x y
    rw [h, ShiftedHom.map_add, ShiftedHom.add_comp]
  · have ht := projectiveDerivedTrace_smul R ι n e r
    change F.map ((DerivedCategory.Plus.singleFunctor P.Modules 0).map (r • 𝟙 ω)) ≫
      projectiveDerivedTrace R ι n e = r • projectiveDerivedTrace R ι n e at ht
    rw [Ext.smul_eq_comp_mk₀, Ext.homPlus_comp, Ext.homPlus_mk₀,
      ShiftedHom.map_comp]
    erw [ShiftedHom.map_mk₀]
    dsimp only [t]
    rw [ShiftedHom.comp_mk₀, ShiftedHom.comp_mk₀, ShiftedHom.comp_mk₀,
      Category.assoc, ← Functor.map_comp, ht, Functor.map_smul, Linear.comp_smul]
    rfl

/-- The forward arrow is literally the native shifted-Hom image followed by shifted trace. -/
theorem projectiveDerivedSerreMap_apply (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules) (i : ℕ)
    (x : Ext.{u + 1} M (twistingSheaf R ι (-(Fintype.card ι : ℤ))) i) :
    projectiveDerivedSerreMap R ι n e M i x =
      (x.homPlus.map ((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp
            (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
            DerivedCategory.Plus.ι)) ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (i : ℤ)).map
          (projectiveDerivedTrace R ι n e) := by
  let F := (moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.ι
  exact ShiftedHom.comp_mk₀ (x.homPlus.map F) (0 : ℤ) rfl
    (projectiveDerivedTrace R ι n e)

/-- The comparison preserves original Yoneda precomposition in every nonnegative degree. -/
theorem projectiveDerivedSerreMap_comp (n : ℕ) (e : ι ≃ Fin (n + 1))
    {M N : (ProjectiveSpace R ι).Modules} {a b c : ℕ}
    (x : Ext.{u + 1} M N a)
    (y : Ext.{u + 1} N (twistingSheaf R ι (-(Fintype.card ι : ℤ))) b)
    (h : a + b = c) :
    projectiveDerivedSerreMap R ι n e M c (x.comp y h) =
      (x.homPlus.map ((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp
            (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
            DerivedCategory.Plus.ι)).comp
        (projectiveDerivedSerreMap R ι n e N b y) (by omega) := by
  let P := ProjectiveSpace R ι
  let α : R →+* Γ(P, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let F := (moduleGlobalSectionsFunctorOfHom P α).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι
  let t := ShiftedHom.mk₀ (0 : ℤ) rfl (projectiveDerivedTrace R ι n e)
  change ((x.comp y h).homPlus.map F).comp t (zero_add _) =
    (x.homPlus.map F).comp ((y.homPlus.map F).comp t (zero_add _)) (by omega)
  rw [Ext.homPlus_comp, ShiftedHom.map_comp]
  exact ShiftedHom.comp_assoc _ _ _ (by omega) (zero_add _) (by omega)

/-- Original coefficient precomposition is the installed derived image of the same map. -/
theorem projectiveDerivedSerreMap_naturality (n : ℕ) (e : ι ≃ Fin (n + 1))
    {M N : (ProjectiveSpace R ι).Modules} (ψ : M ⟶ N) (i : ℕ)
    (y : Ext.{u + 1} N (twistingSheaf R ι (-(Fintype.card ι : ℤ))) i) :
    projectiveDerivedSerreMap R ι n e M i ((Ext.mk₀ ψ).comp y (zero_add i)) =
      ((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp
            (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
            DerivedCategory.Plus.ι).map
          ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).map ψ) ≫
        projectiveDerivedSerreMap R ι n e N i y := by
  rw [projectiveDerivedSerreMap_comp, Ext.homPlus_mk₀]
  erw [ShiftedHom.map_mk₀]
  rw [ShiftedHom.mk₀_comp]

/-- The original unsigned extension class is the actual bounded-below connecting arrow.
The protected signed `Ext.δ` has the separate native factor `Int.negOnePow j`. -/
theorem projectiveDerivedSerreMap_extClass (n : ℕ) (e : ι ≃ Fin (n + 1))
    {S : ShortComplex (ProjectiveSpace R ι).Modules} (hS : S.ShortExact)
    (i j : ℕ) (hij : 1 + i = j)
    (y : Ext.{u + 1} S.X₁ (twistingSheaf R ι (-(Fintype.card ι : ℤ))) i) :
    projectiveDerivedSerreMap R ι n e S.X₃ j (hS.extClass.comp y hij) =
      (ShiftedHom.map hS.singleTrianglePlus.mor₃
        ((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp
            (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
            DerivedCategory.Plus.ι)).comp
        (projectiveDerivedSerreMap R ι n e S.X₁ i y) (by omega) := by
  rw [projectiveDerivedSerreMap_comp, Ext.homPlus_extClass]

/-- Degree zero is the native shifted-Hom class of the original coefficient map and trace. -/
theorem projectiveDerivedSerreMap_mk₀ (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules)
    (f : M ⟶ twistingSheaf R ι (-(Fintype.card ι : ℤ))) :
    projectiveDerivedSerreMap R ι n e M 0 (Ext.mk₀ f) =
      ShiftedHom.mk₀ (0 : ℤ) rfl
        (((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp
            (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
            DerivedCategory.Plus.ι).map
          ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).map f) ≫
            projectiveDerivedTrace R ι n e) := by
  let F := (moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.ι
  change ((Ext.mk₀ f).homPlus.map F).comp
    (ShiftedHom.mk₀ (0 : ℤ) rfl (projectiveDerivedTrace R ι n e)) (zero_add _) = _
  rw [Ext.homPlus_mk₀]
  erw [ShiftedHom.map_mk₀]
  exact ShiftedHom.mk₀_comp_mk₀ _ _ _ rfl rfl


/-- Through any supplied resolution, degree zero induces exactly the existing top Serre
functional on original cohomology, for every module coefficient without an upper bound. -/
theorem projectiveDerivedSerreMap_mk₀_homology_apply (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules) (I : InjectiveResolution M)
    (f : M ⟶ twistingSheaf R ι (-(Fintype.card ι : ℤ)))
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).obj
      (((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.ι).obj
        ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).obj M))) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) (n : ℤ)).hom.app
        (ModuleCat.of R R)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
          ((ShiftedHom.homEquiv (0 : ℤ) rfl).symm
            (projectiveDerivedSerreMap R ι n e M 0 (Ext.mk₀ f))) x) =
      projectiveTopSerreMap R ι n e M f
        (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) I n x) := by
  let P := ProjectiveSpace R ι
  let α : R →+* Γ(P, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let ω := twistingSheaf R ι (-(Fintype.card ι : ℤ))
  let F := (moduleGlobalSectionsFunctorOfHom P α).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι
  let d := F.map ((DerivedCategory.Plus.singleFunctor P.Modules 0).map f)
  let J := injectiveResolution ω
  let φ : InjectiveResolution.Hom I J f :=
    ⟨InjectiveResolution.desc f J I, by
      simpa only [CochainComplex.single₀_map_f_zero] using
        InjectiveResolution.desc_commutes_zero f J I⟩
  have h0 : (ShiftedHom.homEquiv (0 : ℤ) rfl).symm
      (projectiveDerivedSerreMap R ι n e M 0 (Ext.mk₀ f)) =
        d ≫ projectiveDerivedTrace R ι n e := by
    rw [projectiveDerivedSerreMap_mk₀]
    exact (ShiftedHom.homEquiv (0 : ℤ) rfl).symm_apply_apply _
  erw [h0]
  simp only [Functor.map_comp, ModuleCat.comp_apply]
  have ht := projectiveDerivedTrace_homology_apply R ι n e J
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map d x)
  refine ht.trans ?_
  have hn := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_naturality P α φ n x
  exact (congrArg (projectiveTrace R ι n e) hn).trans
    (projectiveTopSerreMap_apply R ι n e M f
      (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv P α I n x)).symm

end AlgebraicGeometry.Scheme.Cohomology
