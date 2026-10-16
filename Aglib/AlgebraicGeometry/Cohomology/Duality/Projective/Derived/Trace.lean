/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Derived
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Trace
public import Aglib.Algebra.Homology.Simplex.Relative.Weights.NegativeTop
public import Aglib.AlgebraicGeometry.Modules.Linear
public import Aglib.Algebra.Homology.DerivedCategory.TStructure.Homology
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# The native derived projective residue trace

The installed bounded-below right-derived global sections of the existing dualizing
residue twist, included into the full derived category of base-ring modules, is
concentrated in the projective dimension. Its homology-normalized reconstruction gives
an actual trace to `single_n R = R[-n]`. The forward map is exactly the original
R-linear Laurent residue trace, through any supplied injective resolution.

The actual derived trace respects original scalar endomorphisms, detected on its
concentrated homology. No generic RF-linearity, Noetherianity or base flatness is assumed.
Every commutative ring and projective dimension zero are retained.
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

local instance projectiveDerivedTraceSource :
    HasDerivedCategory.{u + 1} (ProjectiveSpace R ι).Modules :=
  HasDerivedCategory.standard _
local instance projectiveDerivedTraceTarget : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

/-- The actual installed derived global sections of the existing dualizing twist,
included from the native bounded-below category into the full derived category. -/
abbrev projectiveDerivedResidueTwist : DerivedCategory (ModuleCat.{u} R) :=
  DerivedCategory.Plus.ι.obj
    ((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp
        (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).obj
        (twistingSheaf R ι (-(Fintype.card ι : ℤ)))))

/-- The existing dualizing twist has no derived global-section homology away from the
projective dimension, including all negative degrees and dimension zero. -/
theorem projectiveDerivedResidueTwist_isZero_homology (n : ℕ) (e : ι ≃ Fin (n + 1))
    (i : ℤ) (hi : i ≠ (n : ℤ)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      (projectiveDerivedResidueTwist R ι)) := by
  let X := ProjectiveSpace R ι
  let α : R →+* Γ(X, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let ω := twistingSheaf R ι (-(Fintype.card ι : ℤ))
  by_cases hi0 : 0 ≤ i
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hi0
    let I := injectiveResolution ω
    let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I q
    have hd : -(Fintype.card ι : ℤ) < 0 := by
      rw [Fintype.card_congr e, Fintype.card_fin]
      omega
    let := ModuleCat.subsingleton_of_isZero
      (MvPolynomial.coordinateLaurentTupleHomology_isZero_of_neg_degree_of_ne_top R n e
        (-(Fintype.card ι : ℤ)) hd q (by exact_mod_cast hi))
    let : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X ω) q) :=
      (twistingLaurentCohomologyLinearEquiv R ι
        (-(Fintype.card ι : ℤ)) q).symm.injective.subsingleton
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact E.injective.subsingleton
  · exact (moduleGlobalSectionsFunctorOfHom X α).isZero_homology_rightDerivedFunctorPlus_of_isGE
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj ω) 0 i (by omega)

/-- The actual derived global sections of the dualizing twist have the top lower bound. -/
theorem projectiveDerivedResidueTwist_isGE (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    (projectiveDerivedResidueTwist R ι).IsGE (n : ℤ) := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact projectiveDerivedResidueTwist_isZero_homology R ι n e i (ne_of_lt hi)

/-- The actual derived global sections of the dualizing twist have the top upper bound. -/
theorem projectiveDerivedResidueTwist_isLE (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    (projectiveDerivedResidueTwist R ι).IsLE (n : ℤ) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact projectiveDerivedResidueTwist_isZero_homology R ι n e i (ne_of_gt hi)

/-- Native derived homology maps to the base ring by the original cohomology comparison
and the unchanged original R-linear Laurent residue trace. -/
def projectiveDerivedTraceHomologyLinearEquiv (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).obj
      (projectiveDerivedResidueTwist R ι)) ≃ₗ[R] R :=
  (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
    (injectiveResolution (twistingSheaf R ι (-(Fintype.card ι : ℤ)))) n).trans
    (projectiveTraceLinearEquiv R ι n e)

/-- The actual derived trace to the native `single_n R = R[-n]`, reconstructed from
concentrated homology and the original residue trace. -/
def projectiveDerivedTrace (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    projectiveDerivedResidueTwist R ι ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).obj (ModuleCat.of R R) := by
  letI := projectiveDerivedResidueTwist_isGE R ι n e
  letI := projectiveDerivedResidueTwist_isLE R ι n e
  exact (DerivedCategory.isoSingleHomology (projectiveDerivedResidueTwist R ι) (n : ℤ)).hom ≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).map
      (ModuleCat.ofHom (projectiveDerivedTraceHomologyLinearEquiv R ι n e).toLinearMap)

/-- The homology map of the actual derived trace is exactly its original residue map. -/
@[reassoc]
theorem projectiveDerivedTrace_homology (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        (projectiveDerivedTrace R ι n e) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) (n : ℤ)).hom.app
        (ModuleCat.of R R) =
      ModuleCat.ofHom (projectiveDerivedTraceHomologyLinearEquiv R ι n e).toLinearMap := by
  let := projectiveDerivedResidueTwist_isGE R ι n e
  let := projectiveDerivedResidueTwist_isLE R ι n e
  let ℓ := ModuleCat.ofHom (projectiveDerivedTraceHomologyLinearEquiv R ι n e).toLinearMap
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R)
    (n : ℤ)).hom.naturality ℓ
  change (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).map ℓ) ≫ _ = _ ≫ ℓ at hn
  change (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
    ((DerivedCategory.isoSingleHomology _ (n : ℤ)).hom ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).map ℓ) ≫ _ = ℓ
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc,
    DerivedCategory.isoSingleHomology_homology, Category.id_comp]

/-- Every supplied resolution recovers the same original actual-cohomology trace. -/
theorem projectiveDerivedTrace_homology_apply (n : ℕ) (e : ι ≃ Fin (n + 1))
    (I : InjectiveResolution (twistingSheaf R ι (-(Fintype.card ι : ℤ))))
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).obj
      (projectiveDerivedResidueTwist R ι)) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) (n : ℤ)).hom.app
        (ModuleCat.of R R)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
          (projectiveDerivedTrace R ι n e) x) =
      projectiveTrace R ι n e
        (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) I n x) := by
  have h := congrArg (fun k => k x) (projectiveDerivedTrace_homology R ι n e)
  simp only [ModuleCat.comp_apply] at h
  refine h.trans ?_
  change projectiveTrace R ι n e
    (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv _ _ _ n x) = _
  exact congrArg (projectiveTrace R ι n e)
    (congrArg (fun E => E x)
      (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_eq _ _ _ I n))

/-- The installed derived image of the original scalar coefficient endomorphism scales
the actual trace, for the original structural category action and native target scalars. -/
theorem projectiveDerivedTrace_smul (n : ℕ) (e : ι ≃ Fin (n + 1)) (r : R) :
    let X := ProjectiveSpace R ι
    let α : R →+* Γ(X, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    let ω := twistingSheaf R ι (-(Fintype.card ι : ℤ))
    letI := moduleCategoryLinearOfHom X α
    DerivedCategory.Plus.ι.map
        ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map (r • 𝟙 ω))) ≫
      projectiveDerivedTrace R ι n e = r • projectiveDerivedTrace R ι n e := by
  dsimp only
  let X := ProjectiveSpace R ι
  let α : R →+* Γ(X, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let ω := twistingSheaf R ι (-(Fintype.card ι : ℤ))
  let := moduleCategoryLinearOfHom X α
  let I := injectiveResolution ω
  let := moduleCohomologyModuleOfHom X α ω n
  let f : ω ⟶ ω := r • 𝟙 ω
  let φ : InjectiveResolution.Hom I I f :=
    ⟨InjectiveResolution.desc f I I, by
      simpa only [CochainComplex.single₀_map_f_zero] using
        InjectiveResolution.desc_commutes_zero f I I⟩
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)
  let d := DerivedCategory.Plus.ι.map
    ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).map f))
  let ℓ := ModuleCat.ofHom (projectiveDerivedTraceHomologyLinearEquiv R ι n e).toLinearMap
  have hf : (SheafOfModules.toSheaf X.ringCatSheaf).map f =
      moduleScalarOfGlobal X ω (α r) := by
    dsimp only [f]
    rw [moduleCategoryLinearOfHom_smul_id]
    ext U x
    exact globalScalarEndomorphism_app X ω (α r) U.unop x
  have hℓ : H.map d ≫ ℓ = ℓ ≫ (r • 𝟙 (ModuleCat.of R R)) := by
    ext x
    have h := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_naturality X α φ n x
    change projectiveTrace R ι n e
        (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I n
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
            ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
              ((DerivedCategory.Plus.singleFunctor X.Modules 0).map f)) x)) =
      r • projectiveTrace R ι n e
        (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I n x)
    rw [h]
    change projectiveTrace R ι n e (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map f)
      n _) = _
    rw [hf]
    exact (projectiveTrace R ι n e).map_smul r _
  let := projectiveDerivedResidueTwist_isGE R ι n e
  let := projectiveDerivedResidueTwist_isLE R ι n e
  have hd : d ≫ projectiveDerivedTrace R ι n e =
      projectiveDerivedTrace R ι n e ≫ S.map (r • 𝟙 (ModuleCat.of R R)) := by
    apply DerivedCategory.homology_map_injective_of_isGE_of_isLE _ _ (n : ℤ)
    apply (cancel_mono ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} R) (n : ℤ)).hom.app (ModuleCat.of R R))).mp
    have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} R) (n : ℤ)).hom.naturality (r • 𝟙 (ModuleCat.of R R))
    change H.map (S.map _) ≫ _ = _ ≫ _ at hn
    simp only [Functor.map_comp, Category.assoc]
    rw [projectiveDerivedTrace_homology, hn, ← Category.assoc,
      projectiveDerivedTrace_homology]
    exact hℓ
  change d ≫ projectiveDerivedTrace R ι n e = r • projectiveDerivedTrace R ι n e
  rw [hd, Functor.map_smul, S.map_id, Linear.comp_smul, Category.comp_id]

/-- The actual residue trace is an isomorphism onto the native top-degree scalar single. -/
theorem projectiveDerivedTrace_isIso (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    IsIso (projectiveDerivedTrace R ι n e) := by
  let := projectiveDerivedResidueTwist_isGE R ι n e
  let := projectiveDerivedResidueTwist_isLE R ι n e
  let ℓ := ModuleCat.ofHom (projectiveDerivedTraceHomologyLinearEquiv R ι n e).toLinearMap
  have : IsIso ℓ := (ConcreteCategory.isIso_iff_bijective ℓ).mpr
    (projectiveDerivedTraceHomologyLinearEquiv R ι n e).bijective
  change IsIso ((DerivedCategory.isoSingleHomology _ (n : ℤ)).hom ≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).map ℓ)
  infer_instance

end AlgebraicGeometry.Scheme.Cohomology
