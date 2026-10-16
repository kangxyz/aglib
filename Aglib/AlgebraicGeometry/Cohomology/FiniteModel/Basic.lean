/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.FiniteProjective.Replacement
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Finite.FlatModel
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Resolution.Derived

/-!
# One finite-projective model for an actual finite affine Cech cover

The original bounded flat Cech truncation and actual finite cohomology give
one bounded finite-projective replacement and an actual comparison to that
same truncation. Its literal scalar extension is a quasi-isomorphism after
every ring map. Native cohomology and derived-global-section comparisons
retain the original finite inclusion and original resolution-derived unit.
Projective and proper suppliers specialize this same model and constructor.

Owner extraction: the geometry-independent record and comparison proofs of
`Cohomology.Projective.FiniteModel`, source SHA-256
`0f3001a0138c2d2cf645b16608bfe1a1fb5ff52797f17f99e2a1910ecb8c4fe4`.
The actual coordinate family is generalized to a supplied actual affine
cover; native objects, maps, universes and relative-flatness scope remain.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace HomologicalComplex

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u) (X : Scheme.{u})
  (f : X ⟶ Spec (CommRingCat.of R)) (U : ι → X.Opens) (M : X.Modules) (n : ℕ)

/-- The sole bounded finite-projective replacement of an original finite Cech
truncation, retaining its actual map and literal arbitrary scalar extensions. -/
structure FiniteCechCohomologyModel where
  complex : CochainComplex (ModuleCat.{u} R) ℤ
  lowerBound : complex.IsStrictlyGE 0
  upperBound : complex.IsStrictlyLE (n : ℤ)
  finite_X : ∀ j, Module.Finite R (complex.X j)
  projective_X : ∀ j, Module.Projective R (complex.X j)
  comparison : complex ⟶ moduleFiniteCechComplex X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M n
  quasiIso : QuasiIso comparison
  baseChange_quasiIso : ∀ (B : Type u) [CommRing B] (σ : R →+* B),
    QuasiIso (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map comparison)

/-- Actual finite original cohomology and relative flatness construct the
same finite-projective model for any supplied finite affine cover. -/
theorem nonempty_finiteCechCohomologyModel_of_finite_cohomology [IsNoetherianRing R]
    [X.IsSeparated] [M.IsQuasicoherent] (e : ι ≃ Fin (n + 1))
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (hflat : Scheme.Modules.relativeFlat f M)
    (hfinite : ∀ q : ℕ,
      letI := moduleCohomologyModuleOfHom X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M q
      Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q)) :
    Nonempty (FiniteCechCohomologyModel R ι X f U M n) := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let K : CochainComplex (ModuleCat.{u} R) ℤ := moduleFiniteCechComplex X α U M n
  let (j : ℤ) : Module.Flat R (K.X j) :=
    moduleFiniteCechComplex_flat_X_of_relativeFlat f M hflat U n e hU hcover j
  let (j : ℤ) : Module.Finite R (K.homology j) := by
    by_cases hj : 0 ≤ j
    · let q := j.toNat
      let := moduleCohomologyModuleOfHom X α M q
      let : Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) := hfinite q
      have hq : (q : ℤ) = j := Int.toNat_of_nonneg hj
      have H : Module.Finite R (K.homology (q : ℤ)) := Module.Finite.equiv
        (moduleFiniteCechCohomologyLinearEquiv X α U M n e hU hcover q).symm
      rw [hq] at H
      exact H
    · let := ModuleCat.subsingleton_of_isZero
        ((K.exactAt_of_isGE 0 j (by omega)).isZero_homology)
      infer_instance
  obtain ⟨P, hge, hle, hfinite, hprojective, u, hu, hbase⟩ :=
    CochainComplex.exists_finiteProjective_model_with_baseChange.{u, u, u} K n
  exact ⟨{ complex := P
           lowerBound := hge
           upperBound := hle
           finite_X := hfinite
           projective_X := hprojective
           comparison := u
           quasiIso := hu
           baseChange_quasiIso := hbase }⟩


/-- Finite categorical intersections of an affine-open family on a separated
scheme are affine. The comparison uses actual opens and their infimum. -/
theorem isAffineOpen_cechTuple_of_isSeparated
    {X : Scheme.{u}} [X.IsSeparated] {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ j, IsAffineOpen (U j)) (q : ℕ) (a : Fin (q + 1) → ι) :
    IsAffineOpen (∏ᶜ fun k => U (a k)) := by
  have he : (∏ᶜ fun k => U (a k)) = ⨅ k, U (a k) := by
    apply le_antisymm
    · exact le_iInf fun k => leOfHom (Pi.π _ k)
    · exact leOfHom (Pi.lift fun k => homOfLE (iInf_le _ k))
  rw [he]
  exact IsAffineOpen.iInf (fun k => hU (a k))

namespace FiniteCechCohomologyModel

variable {R ι X f U M n} (D : FiniteCechCohomologyModel R ι X f U M n)

/-- The actual bounded model packed in the native bounded-below category. -/
def toPlus : CochainComplex.Plus (ModuleCat.{u} R) :=
  ⟨D.complex, 0, D.lowerBound⟩

/-- The original model comparison followed by the original good-truncation
inclusion, as an actual map to the unchanged native integer Cech complex. -/
def toCechPlus : D.toPlus ⟶ moduleCechComplexPlus X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    U M :=
  ⟨D.comparison ≫ moduleFiniteCechInclusion X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    U M n⟩

variable [X.IsSeparated] [M.IsQuasicoherent]
  (hU : ∀ j, IsAffineOpen (U j)) (hcover : iSup U = ⊤)

include hU hcover

/-- The literal map from the model to original integer Cech is a
quasi-isomorphism, using the original finite-cover inclusion. -/
theorem toCechPlus_quasiIso (e : ι ≃ Fin (n + 1)) : QuasiIso D.toCechPlus.hom := by
  let : QuasiIso D.comparison := D.quasiIso
  let : QuasiIso (moduleFiniteCechInclusion X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      U M n) :=
    moduleFiniteCechInclusion_quasiIso X _ _ M n e
      hU
      hcover
  change QuasiIso (D.comparison ≫ _)
  infer_instance

local instance finiteModelDerivedSource : HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

local instance finiteModelDerivedTarget : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

/-- The actual finite-projective model represents the original installed
derived global sections of the original coefficient. Its forward map
factors through the original comparison, original Cech augmentation
zigzag and original injective-resolution derived unit. -/
def derivedGlobalSectionsIso (e : ι ≃ Fin (n + 1)) (I : InjectiveResolution M) :
    DerivedCategory.Plus.Q.obj D.toPlus ≅
      (moduleGlobalSectionsFunctorOfHom X
        (f.appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) := by
  let : IsIso (DerivedCategory.Plus.Q.map D.toCechPlus) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso (ModuleCat.{u} R)) _
      (D.toCechPlus_quasiIso hU hcover e)
  exact asIso (DerivedCategory.Plus.Q.map D.toCechPlus) ≪≫
    moduleCechDerivedGlobalSectionsIso X _ _ I
      hcover
      (isAffineOpen_cechTuple_of_isSeparated U hU)

/-- The native derived-object comparison retains the literal actual map
to original Cech and the original derived Cech comparison. -/
theorem derivedGlobalSectionsIso_hom (e : ι ≃ Fin (n + 1)) (I : InjectiveResolution M)
    (haff : ∀ (q : ℕ) (a : Fin (q + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k))) :
    (D.derivedGlobalSectionsIso hU hcover e I).hom =
      DerivedCategory.Plus.Q.map D.toCechPlus ≫
        (moduleCechDerivedGlobalSectionsIso X
          (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
          U I
          hcover
          haff).hom := rfl

/-- The original model comparison computes original cohomology over the
base ring, with its literal structural scalar action. -/
def cohomologyLinearEquiv (e : ι ≃ Fin (n + 1)) (q : ℕ) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M q
    D.complex.homology (q : ℤ) ≃ₗ[R] Sheaf.H.{u + 1} (moduleAddSheaf X M) q := by
  let : QuasiIso D.comparison := D.quasiIso
  exact (asIso (homologyMap D.comparison (q : ℤ))).toLinearEquiv.trans
    (moduleFiniteCechCohomologyLinearEquiv X _ _ M n e
      hU
      hcover q)

/-- The scalar-linear comparison retains the original native homology
map of the actual model-to-Cech chain comparison. -/
theorem cohomologyLinearEquiv_apply (e : ι ≃ Fin (n + 1)) (q : ℕ)
    (x : D.complex.homology (q : ℤ)) :
    D.cohomologyLinearEquiv hU hcover e q x =
      moduleFiniteCechCohomologyLinearEquiv X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
        U M n e
        hU
        hcover q
        (homologyMap D.comparison (q : ℤ) x) := rfl

/-- The literal arbitrary-base-change representative: tensor the actual
model comparison and then use the original bounded Cech base-change map. -/
def baseChangeComparison (e : ι ≃ Fin (n + 1))
    (hflat : Scheme.Modules.relativeFlat f M) {B : Type u} [CommRing B] (σ : R →+* B) :
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj D.complex ⟶
      moduleFiniteCechComplex (pullback f (Spec.map (CommRingCat.ofHom σ)))
        (r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
        (fun j => p ⁻¹ᵁ (U j)) ((Scheme.Modules.pullback p).obj M) n := by
  exact ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map D.comparison ≫
    (moduleFiniteCechBaseChangeIso f M hflat U n e
      hU
      hcover σ).hom

/-- The actual base-change representative is a quasi-isomorphism for
every ring map, including nonflat maps to non-Noetherian rings. -/
theorem baseChangeComparison_quasiIso (e : ι ≃ Fin (n + 1))
    (hflat : Scheme.Modules.relativeFlat f M) {B : Type u} [CommRing B] (σ : R →+* B) :
    QuasiIso (D.baseChangeComparison hU hcover e hflat σ) := by
  let : QuasiIso
      (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map D.comparison) :=
    D.baseChange_quasiIso B σ
  dsimp only [baseChangeComparison]
  infer_instance

/-- The exact representative square retains the original model-to-Cech
map, both original finite inclusions, and the original integer Cech
base-change arrow. It is the chain-level normalization for the canonical
cohomology and derived base-change maps. -/
@[reassoc]
theorem baseChangeComparison_inclusion (e : ι ≃ Fin (n + 1))
    (hflat : Scheme.Modules.relativeFlat f M) {B : Type u} [CommRing B] (σ : R →+* B) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    D.baseChangeComparison hU hcover e hflat σ ≫
        moduleFiniteCechInclusion (pullback f (Spec.map (CommRingCat.ofHom σ)))
          (r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
          (fun j => p ⁻¹ᵁ (U j)) ((Scheme.Modules.pullback p).obj M) n =
      ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map D.toCechPlus.hom ≫
        moduleCechIntBaseChangeMap f σ M U := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  dsimp only
  have h := moduleFiniteCechBaseChangeIso_hom_ιTruncLE f M hflat
    U n e
    hU
    hcover σ
  dsimp only at h
  simpa only [baseChangeComparison, toCechPlus, Functor.map_comp, Category.assoc] using
    congrArg
      (fun k => ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map D.comparison ≫ k) h

/-- After every ring base change the actual tensor of this same model
computes the unchanged original cohomology of the ordinary pulled
coefficient, with its original structural scalar action in every degree. -/
def baseChangeCohomologyLinearEquiv (e : ι ≃ Fin (n + 1))
    (hflat : Scheme.Modules.relativeFlat f M) {B : Type u} [CommRing B]
    (σ : R →+* B) (q : ℕ) :
    let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    let β := r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
    let N := (Scheme.Modules.pullback p).obj M
    letI := moduleCohomologyModuleOfHom Y β N q
    ((((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj D.complex).homology
      (q : ℤ)) ≃ₗ[B] Sheaf.H.{u + 1} (moduleAddSheaf Y N) q := by
  let a := ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map D.comparison
  let : QuasiIso a := D.baseChange_quasiIso B σ
  exact (asIso (homologyMap a (q : ℤ))).toLinearEquiv.trans
    (moduleFiniteCechBaseChangeCohomologyLinearEquiv f M hflat
      U n e
      hU
      hcover σ q)

/-- The all-base-change computation uses the homology of the literal
scalar extension of the same actual model comparison. -/
theorem baseChangeCohomologyLinearEquiv_apply (e : ι ≃ Fin (n + 1))
    (hflat : Scheme.Modules.relativeFlat f M) {B : Type u} [CommRing B]
    (σ : R →+* B) (q : ℕ)
    (x : (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj
      D.complex).homology (q : ℤ)) :
    D.baseChangeCohomologyLinearEquiv hU hcover e hflat σ q x =
      moduleFiniteCechBaseChangeCohomologyLinearEquiv f M hflat
        U n e
        hU
        hcover σ q
        (homologyMap
          (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map D.comparison)
          (q : ℤ) x) := rfl

end FiniteCechCohomologyModel

end AlgebraicGeometry.Scheme.Cohomology
