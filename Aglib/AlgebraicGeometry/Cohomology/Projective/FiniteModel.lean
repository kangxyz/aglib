/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Projective.ClosedImmersion

/-!
# Constructed finite-projective cohomology models for projective embeddings

The coordinate cover of an actual closed immersion into projective space
specializes the sole finite-affine-cover model. Over a Noetherian base,
proved projective coherent finiteness supplies the actual cohomology input
to that generic constructor. Original public names, constructor/field access
and all original chain, cohomology and derived-unit maps are retained as
transparent specialization and thin delegation. There is one model record
and one construction, shared with the proper supplier.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open HomologicalComplex
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u) {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace R ι) (f : X ⟶ Spec (CommRingCat.of R))
  (M : X.Modules) (n : ℕ)

/-- Actual bounded finite-projective model data and its literal comparison
to the original coordinate-cover good Cech truncation. All-base-change
quasi-isomorphisms concern this same actual chain map. -/
abbrev ProjectiveCohomologyModel :=
  FiniteCechCohomologyModel R ι X f (fun j => i ⁻¹ᵁ coordinateOpen R ι j) M n

namespace ProjectiveCohomologyModel

variable {R ι i f M n}

/-- The original constructor access for the transparent coordinate-cover specialization. -/
abbrev mk (complex : CochainComplex (ModuleCat.{u} R) ℤ)
    (lowerBound : complex.IsStrictlyGE 0) (upperBound : complex.IsStrictlyLE (n : ℤ))
    (finite_X : ∀ j, Module.Finite R (complex.X j))
    (projective_X : ∀ j, Module.Projective R (complex.X j))
    (comparison : complex ⟶ moduleFiniteCechComplex X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      (fun j => i ⁻¹ᵁ coordinateOpen R ι j) M n)
    (quasiIso : QuasiIso comparison)
    (baseChange_quasiIso : ∀ (B : Type u) [CommRing B] (σ : R →+* B),
      QuasiIso (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map comparison)) :
    ProjectiveCohomologyModel R ι i f M n :=
  { complex := complex
    lowerBound := lowerBound
    upperBound := upperBound
    finite_X := finite_X
    projective_X := projective_X
    comparison := comparison
    quasiIso := quasiIso
    baseChange_quasiIso := baseChange_quasiIso }

/-- The same actual finite-projective complex. -/
abbrev complex (D : ProjectiveCohomologyModel R ι i f M n) :=
  FiniteCechCohomologyModel.complex D

/-- The original strict lower bound. -/
abbrev lowerBound (D : ProjectiveCohomologyModel R ι i f M n) :=
  FiniteCechCohomologyModel.lowerBound D

/-- The original strict upper bound. -/
abbrev upperBound (D : ProjectiveCohomologyModel R ι i f M n) :=
  FiniteCechCohomologyModel.upperBound D

/-- Finiteness of the same original terms. -/
abbrev finite_X (D : ProjectiveCohomologyModel R ι i f M n) :=
  FiniteCechCohomologyModel.finite_X D

/-- Projectivity of the same original terms. -/
abbrev projective_X (D : ProjectiveCohomologyModel R ι i f M n) :=
  FiniteCechCohomologyModel.projective_X D

/-- The same actual map to the coordinate-cover Cech truncation. -/
abbrev comparison (D : ProjectiveCohomologyModel R ι i f M n) :=
  FiniteCechCohomologyModel.comparison D

/-- The original comparison quasi-isomorphism. -/
abbrev quasiIso (D : ProjectiveCohomologyModel R ι i f M n) :=
  FiniteCechCohomologyModel.quasiIso D

/-- Quasi-isomorphism of each literal scalar extension of the same map. -/
abbrev baseChange_quasiIso (D : ProjectiveCohomologyModel R ι i f M n) :=
  FiniteCechCohomologyModel.baseChange_quasiIso D

end ProjectiveCohomologyModel

variable [IsClosedImmersion i]

/-- The finite-projective model is constructed from an actual projective
embedding, actual coherent coefficient and actual relative flatness. -/
theorem nonempty_projectiveCohomologyModel_of_embedding [IsNoetherianRing R]
    (e : ι ≃ Fin (n + 1)) (hf : i ≫ toSpec R ι = f)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) :
    Nonempty (ProjectiveCohomologyModel R ι i f M n) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  exact nonempty_finiteCechCohomologyModel_of_finite_cohomology R ι X f
    (fun j => i ⁻¹ᵁ coordinateOpen R ι j) M n e
    (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
    (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) hflat
    (fun q => moduleCohomology_finite_of_projectiveEmbedding R ι i n e f hf M hM q)

/-- A chosen actual finite-projective model, obtained from the proved
existence theorem and retaining its original chain comparison. -/
def projectiveCohomologyModelOfEmbedding [IsNoetherianRing R]
    (e : ι ≃ Fin (n + 1)) (hf : i ≫ toSpec R ι = f)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) :
    ProjectiveCohomologyModel R ι i f M n :=
  Classical.choice (nonempty_projectiveCohomologyModel_of_embedding R ι i f M n e hf hM hflat)

namespace ProjectiveCohomologyModel

variable {R ι i f M n} (D : ProjectiveCohomologyModel R ι i f M n)

/-- The actual bounded model packed in the native bounded-below category. -/
def toPlus : CochainComplex.Plus (ModuleCat.{u} R) := FiniteCechCohomologyModel.toPlus D

/-- The original model comparison followed by the original good-truncation
inclusion, as an actual map to the unchanged native integer Cech complex. -/
def toCechPlus : D.toPlus ⟶ moduleCechComplexPlus X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    (fun j => i ⁻¹ᵁ coordinateOpen R ι j) M := FiniteCechCohomologyModel.toCechPlus D

variable [M.IsQuasicoherent]

/-- The literal map from the model to original integer Cech is a
quasi-isomorphism, using the original coordinate-cover inclusion. -/
theorem toCechPlus_quasiIso (e : ι ≃ Fin (n + 1)) : QuasiIso D.toCechPlus.hom := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  exact FiniteCechCohomologyModel.toCechPlus_quasiIso D
    (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
    (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) e

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
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  exact FiniteCechCohomologyModel.derivedGlobalSectionsIso D
    (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
    (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) e I

/-- The native derived-object comparison retains the literal actual map
to original Cech and the original derived Cech comparison. -/
theorem derivedGlobalSectionsIso_hom (e : ι ≃ Fin (n + 1)) (I : InjectiveResolution M) :
    (D.derivedGlobalSectionsIso e I).hom =
      DerivedCategory.Plus.Q.map D.toCechPlus ≫
        (moduleCechDerivedGlobalSectionsIso X
          (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
          (fun j => i ⁻¹ᵁ coordinateOpen R ι j) I
          (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι))
          (isAffineOpen_projectiveEmbeddingTuple R ι i)).hom := rfl

/-- The original model comparison computes original cohomology over the
base ring, with its literal structural scalar action. -/
def cohomologyLinearEquiv (e : ι ≃ Fin (n + 1)) (q : ℕ) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M q
    D.complex.homology (q : ℤ) ≃ₗ[R] Sheaf.H.{u + 1} (moduleAddSheaf X M) q := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  exact FiniteCechCohomologyModel.cohomologyLinearEquiv D
    (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
    (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) e q

/-- The scalar-linear comparison retains the original native homology
map of the actual model-to-Cech chain comparison. -/
theorem cohomologyLinearEquiv_apply (e : ι ≃ Fin (n + 1)) (q : ℕ)
    (x : D.complex.homology (q : ℤ)) :
    letI : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
    D.cohomologyLinearEquiv e q x =
      moduleFiniteCechCohomologyLinearEquiv X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
        (fun j => i ⁻¹ᵁ coordinateOpen R ι j) M n e
        (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
        (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) q
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
        (fun j => p ⁻¹ᵁ (i ⁻¹ᵁ coordinateOpen R ι j)) ((Scheme.Modules.pullback p).obj M) n := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  exact FiniteCechCohomologyModel.baseChangeComparison D
    (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
    (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) e hflat σ

/-- The actual base-change representative is a quasi-isomorphism for
every ring map, including nonflat maps to non-Noetherian rings. -/
theorem baseChangeComparison_quasiIso (e : ι ≃ Fin (n + 1))
    (hflat : Scheme.Modules.relativeFlat f M) {B : Type u} [CommRing B] (σ : R →+* B) :
    QuasiIso (D.baseChangeComparison e hflat σ) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  exact FiniteCechCohomologyModel.baseChangeComparison_quasiIso D
    (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
    (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) e hflat σ

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
    D.baseChangeComparison e hflat σ ≫
        moduleFiniteCechInclusion (pullback f (Spec.map (CommRingCat.ofHom σ)))
          (r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
          (fun j => p ⁻¹ᵁ (i ⁻¹ᵁ coordinateOpen R ι j)) ((Scheme.Modules.pullback p).obj M) n =
      ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map D.toCechPlus.hom ≫
        moduleCechIntBaseChangeMap f σ M (fun j => i ⁻¹ᵁ coordinateOpen R ι j) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  exact FiniteCechCohomologyModel.baseChangeComparison_inclusion D
    (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
    (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) e hflat σ

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
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  exact FiniteCechCohomologyModel.baseChangeCohomologyLinearEquiv D
    (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
    (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) e hflat σ q

/-- The all-base-change computation uses the homology of the literal
scalar extension of the same actual model comparison. -/
theorem baseChangeCohomologyLinearEquiv_apply (e : ι ≃ Fin (n + 1))
    (hflat : Scheme.Modules.relativeFlat f M) {B : Type u} [CommRing B]
    (σ : R →+* B) (q : ℕ)
    (x : (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj
      D.complex).homology (q : ℤ)) :
    letI : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
    D.baseChangeCohomologyLinearEquiv e hflat σ q x =
      moduleFiniteCechBaseChangeCohomologyLinearEquiv f M hflat
        (fun j => i ⁻¹ᵁ coordinateOpen R ι j) n e
        (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
        (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) σ q
        (homologyMap
          (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map D.comparison)
          (q : ℤ) x) := rfl

end ProjectiveCohomologyModel

end AlgebraicGeometry.Scheme.Cohomology
