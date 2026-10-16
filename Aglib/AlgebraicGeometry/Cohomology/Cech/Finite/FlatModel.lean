/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Flat.ScalarExtension
public import Aglib.Algebra.Homology.Flat.Truncation
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Finite.FlatTerms
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Finite.UniversalTensor

/-!
# The actual bounded flat Cech model and arbitrary base change

Actual relative flatness supplies the original affine-section term flatness.
Actual all-ring Cech base change and finite-cover vanishing prove universal
tensor exactness at the next degree. Thus the original boundary cycles and
every term of the unchanged native good truncation are flat. Its canonical
comparison after every ring map retains the original integer Cech arrow and
the original truncation inclusion. The coefficient after base change is the
ordinary actual module-sheaf pullback.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomologicalComplex

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type u} [CommRing R] {X : Scheme.{u}} [X.IsSeparated]
  (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) [M.IsQuasicoherent]
  (hM : Scheme.Modules.relativeFlat f M)
  {ι : Type u} (U : ι → X.Opens) (n : ℕ) (e : ι ≃ Fin (n + 1))
  (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)

include hM e hU hcover

/-- The actual boundary cycle module at the sharp finite-cover cutoff is
flat, as a consequence of actual universal next-degree tensor exactness. -/
theorem moduleCechIntComplex_flat_cycles_of_relativeFlat :
    Module.Flat R ((moduleCechIntComplex X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M).cycles (n : ℤ)) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let K : CochainComplex (ModuleCat.{u} R) ℤ := moduleCechIntComplex X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M
  let : Module.Flat R (K.X (n : ℤ)) :=
    moduleCechIntComplex_flat_X_of_relativeFlat f M hM U hU (n : ℤ)
  let : Module.Flat R (K.X ((n : ℤ) + 1)) :=
    moduleCechIntComplex_flat_X_of_relativeFlat f M hM U hU ((n : ℤ) + 1)
  let : Module.Flat R (K.X ((n : ℤ) + 2)) :=
    moduleCechIntComplex_flat_X_of_relativeFlat f M hM U hU ((n : ℤ) + 2)
  exact K.flat_cycles_of_universally_lTensor_exact (n : ℤ)
    (moduleCechIntComplex_universally_lTensor_exact f M U n e hU hcover)

/-- Every term of the original bounded native Cech model is flat. The
boundary is the actual proved-flat cycle module, and the model is unchanged. -/
theorem moduleFiniteCechComplex_flat_X_of_relativeFlat (q : ℤ) :
    Module.Flat R ((moduleFiniteCechComplex X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M n).X q) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let K : CochainComplex (ModuleCat.{u} R) ℤ := moduleCechIntComplex X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M
  let : ∀ i, Module.Flat R (K.X i) :=
    fun i => moduleCechIntComplex_flat_X_of_relativeFlat f M hM U hU i
  exact K.flat_truncLE_X_of_universally_lTensor_exact (n : ℤ)
    (moduleCechIntComplex_universally_lTensor_exact f M U n e hU hcover) q

/-- The literal original truncation inclusion remains a quasi-isomorphism
after every ring scalar extension, even when that ring map is not flat. -/
theorem moduleFiniteCechInclusion_extendScalars_quasiIso {B : Type u} [CommRing B]
    (σ : R →+* B) :
    QuasiIso (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map
      (moduleFiniteCechInclusion X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M n)) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let K : CochainComplex (ModuleCat.{u} R) ℤ := moduleCechIntComplex X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M
  let : Module.Flat R (K.X ((n : ℤ) + 1)) :=
    moduleCechIntComplex_flat_X_of_relativeFlat f M hM U hU ((n : ℤ) + 1)
  let : Module.Flat R (K.X ((n : ℤ) + 2)) :=
    moduleCechIntComplex_flat_X_of_relativeFlat f M hM U hU ((n : ℤ) + 2)
  let : CochainComplex.IsLE
      (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj K) (n : ℤ) :=
    moduleCechIntComplex_extendScalars_isLE f M U n e hU hcover σ
  exact CochainComplex.quasiIso_extendScalars_ιTruncLE_of_universally_lTensor_exact σ K (n : ℤ)
    (moduleCechIntComplex_universally_lTensor_exact f M U n e hU hcover)

/-- The original bounded good Cech model commutes canonically with every
ring base change, retaining the actual ordinary pulled coefficient. -/
def moduleFiniteCechBaseChangeIso {B : Type u} [CommRing B] (σ : R →+* B) :
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj
        (moduleFiniteCechComplex X
          (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M n) ≅
      moduleFiniteCechComplex (pullback f (Spec.map (CommRingCat.ofHom σ)))
        (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
        (fun i => p ⁻¹ᵁ U i) ((Scheme.Modules.pullback p).obj M) n := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let K : CochainComplex (ModuleCat.{u} R) ℤ := moduleCechIntComplex X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M
  let : Module.Flat R (K.X ((n : ℤ) + 1)) :=
    moduleCechIntComplex_flat_X_of_relativeFlat f M hM U hU ((n : ℤ) + 1)
  let : Module.Flat R (K.X ((n : ℤ) + 2)) :=
    moduleCechIntComplex_flat_X_of_relativeFlat f M hM U hU ((n : ℤ) + 2)
  exact CochainComplex.extendScalarsTruncLEIso σ K (n : ℤ)
      (moduleCechIntComplex_universally_lTensor_exact f M U n e hU hcover) ≪≫
    ((ComplexShape.embeddingUpIntLE (n : ℤ)).truncLEFunctor (ModuleCat.{u} B)).mapIso
      (moduleCechIntBaseChangeIso f σ M U hU)

/-- The canonical bounded-model comparison retains the literal original
mapped inclusion and the literal original integer Cech base-change arrow. -/
@[reassoc]
theorem moduleFiniteCechBaseChangeIso_hom_ιTruncLE {B : Type u} [CommRing B]
    (σ : R →+* B) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    (moduleFiniteCechBaseChangeIso f M hM U n e hU hcover σ).hom ≫
        moduleFiniteCechInclusion (pullback f (Spec.map (CommRingCat.ofHom σ)))
          (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
          (fun i => p ⁻¹ᵁ U i) ((Scheme.Modules.pullback p).obj M) n =
      ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map
        (moduleFiniteCechInclusion X
          (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M n) ≫
        moduleCechIntBaseChangeMap f σ M U := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  dsimp only
  let K : CochainComplex (ModuleCat.{u} R) ℤ := moduleCechIntComplex X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let L : CochainComplex (ModuleCat.{u} B) ℤ :=
    moduleCechIntComplex (pullback f (Spec.map (CommRingCat.ofHom σ)))
      (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
      (fun i => p ⁻¹ᵁ U i) ((Scheme.Modules.pullback p).obj M)
  let θ : ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj K ⟶ L :=
    moduleCechIntBaseChangeMap f σ M U
  let : Module.Flat R (K.X ((n : ℤ) + 1)) :=
    moduleCechIntComplex_flat_X_of_relativeFlat f M hM U hU ((n : ℤ) + 1)
  let : Module.Flat R (K.X ((n : ℤ) + 2)) :=
    moduleCechIntComplex_flat_X_of_relativeFlat f M hM U hU ((n : ℤ) + 2)
  change ((CochainComplex.extendScalarsTruncLEIso σ K (n : ℤ)
      (moduleCechIntComplex_universally_lTensor_exact f M U n e hU hcover)).hom ≫
        CochainComplex.truncLEMap θ (n : ℤ)) ≫ L.ιTruncLE (n : ℤ) =
      ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map
        (K.ιTruncLE (n : ℤ)) ≫ θ
  rw [Category.assoc, CochainComplex.ιTruncLE_naturality, ← Category.assoc,
    CochainComplex.extendScalarsTruncLEIso_hom_ιTruncLE]

/-- The actual bounded flat source model computes the unchanged sheaf
cohomology of the ordinary pulled coefficient after every ring base change,
in every nonnegative degree and with the original structural scalar action. -/
def moduleFiniteCechBaseChangeCohomologyLinearEquiv {B : Type u} [CommRing B]
    (σ : R →+* B) (j : ℕ) :
    let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
    let N := (Scheme.Modules.pullback p).obj M
    letI := moduleCohomologyModuleOfHom Y β N j
    ((((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj
        (moduleFiniteCechComplex X
          (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M n)).homology
      (j : ℤ)) ≃ₗ[B] Sheaf.H.{u + 1} (moduleAddSheaf Y N) j := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
  let p : Y ⟶ X := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let q : Y ⟶ Spec (CommRingCat.of B) := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let β : B →+* Γ(Y, ⊤) := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  let N : Y.Modules := (Scheme.Modules.pullback p).obj M
  let V : ι → Y.Opens := fun i => p ⁻¹ᵁ U i
  let : IsAffineHom p := MorphismProperty.pullback_fst f
    (Spec.map (CommRingCat.ofHom σ))
    (inferInstance : IsAffineHom (Spec.map (CommRingCat.ofHom σ)))
  let : Y.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  let : N.IsQuasicoherent := Scheme.Modules.quasicoherent_pullback p M
  letI := moduleCohomologyModuleOfHom Y β N j
  let I :
      ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj
          (moduleFiniteCechComplex X
            (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M n) ≅
        moduleFiniteCechComplex Y β V N n :=
    moduleFiniteCechBaseChangeIso f M hM U n e hU hcover σ
  exact ((HomologicalComplex.homologyFunctor
      (ModuleCat.{u} B) (.up ℤ) (j : ℤ)).mapIso I).toLinearEquiv.trans
    (moduleFiniteCechCohomologyLinearEquiv Y β V N n e
      (fun i => (hU i).preimage p) (p.iSup_preimage_eq_top hcover) j)

end AlgebraicGeometry.Scheme.Cohomology
