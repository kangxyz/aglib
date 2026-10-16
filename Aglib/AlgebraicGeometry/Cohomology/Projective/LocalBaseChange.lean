/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel.BaseChangeCriterion
public import Aglib.Algebra.Homology.CochainComplex.BaseChangeCriterion

/-!
# Local surjectivity and freeness criteria for projective cohomology

Over a Noetherian local base, surjectivity of the original residue-field
cohomology base-change map gives arbitrary base change for coherent
relatively flat coefficients on an actual projective embedding. Under
that surjectivity in degree `q+1`, freeness of original cohomology in that
degree is equivalent to surjectivity in degree `q`. In degree zero,
surjectivity already gives freeness because the actual model has no
negative terms. None of these criteria assumes a reduced base ring.
The geometric endpoints construct the universal model internally.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex Module AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {ι : Type u} {X : Scheme.{u}} {i : X ⟶ ProjectiveSpace R ι} [IsClosedImmersion i]
    {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {n : ℕ}

/-- Original residue-field surjectivity gives invertibility after every ring map for
the same actual model, without a reducedness or flatness hypothesis on the ring map. -/
theorem ProjectiveCohomologyModel.moduleCohomologyBaseChangeMap_isIso_of_epi_residue
    (D : ProjectiveCohomologyModel R ι i f M n) [M.IsQuasicoherent]
    (e : ι ≃ Fin (n + 1)) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ)
    [Epi (moduleCohomologyBaseChangeMap f (algebraMap R (IsLocalRing.ResidueField R)) M q)]
    {B : Type u} [CommRing B] (σ : R →+* B) :
    IsIso (moduleCohomologyBaseChangeMap f σ M q) := by
  let (j : ℤ) : Module.Finite R (D.complex.X j) := D.finite_X j
  let (j : ℤ) : Module.Projective R (D.complex.X j) := D.projective_X j
  let : Epi (extendScalarsHomologyMap (algebraMap R (IsLocalRing.ResidueField R))
      D.complex (q : ℤ)) :=
    (D.moduleCohomologyBaseChangeMap_epi_iff e hflat _ q).mp inferInstance
  let : Module.Finite R (D.complex.sc (q : ℤ)).X₂ := by
    change Module.Finite R (D.complex.X (q : ℤ))
    infer_instance
  let : Module.Finite R (D.complex.sc (q : ℤ)).X₃ := by
    change Module.Finite R (D.complex.X ((ComplexShape.up ℤ).next (q : ℤ)))
    infer_instance
  let : Module.Flat R (D.complex.sc (q : ℤ)).X₃ := by
    change Module.Flat R (D.complex.X ((ComplexShape.up ℤ).next (q : ℤ)))
    infer_instance
  apply (D.moduleCohomologyBaseChangeMap_isIso_iff e hflat σ q).mpr
  exact ShortComplex.homologyBaseChangeMap_isIso_of_epi_residue.{u, 0, u}
    σ (D.complex.sc (q : ℤ))

/-- Under original residue-field surjectivity in degree `q+1`, original cohomology is
free in that degree exactly when the original residue-field map in degree `q` is
surjective. The statement allows nonreduced local base rings. -/
theorem ProjectiveCohomologyModel.free_moduleCohomology_iff_epi_residue_predecessor
    (D : ProjectiveCohomologyModel R ι i f M n) [M.IsQuasicoherent]
    (e : ι ≃ Fin (n + 1)) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ)
    [Epi (moduleCohomologyBaseChangeMap f (algebraMap R (IsLocalRing.ResidueField R)) M
      (q + 1))] :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M (q + 1)
    Module.Free R (Sheaf.H.{u + 1} (moduleAddSheaf X M) (q + 1)) ↔
      Epi (moduleCohomologyBaseChangeMap f (algebraMap R (IsLocalRing.ResidueField R)) M q) := by
  let (j : ℤ) : Module.Finite R (D.complex.X j) := D.finite_X j
  let (j : ℤ) : Module.Projective R (D.complex.X j) := D.projective_X j
  let := moduleCohomologyModuleOfHom X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M (q + 1)
  let : Epi (extendScalarsHomologyMap (algebraMap R (IsLocalRing.ResidueField R))
      D.complex ((q + 1 : ℕ) : ℤ)) :=
    (D.moduleCohomologyBaseChangeMap_epi_iff e hflat _ (q + 1)).mp inferInstance
  have hfree : Module.Free R (Sheaf.H.{u + 1} (moduleAddSheaf X M) (q + 1)) ↔
      Module.Free R (D.complex.homology ((q + 1 : ℕ) : ℤ)) := by
    constructor
    · intro h
      let := h
      exact Module.Free.of_equiv (D.cohomologyLinearEquiv e (q + 1)).symm
    · intro h
      let := h
      exact Module.Free.of_equiv (D.cohomologyLinearEquiv e (q + 1))
  have hmodel := D.complex.free_homology_iff_epi_residue_predecessor ((q + 1 : ℕ) : ℤ)
  have hp : ((q + 1 : ℕ) : ℤ) - 1 = (q : ℤ) := by omega
  have hprev : Epi (extendScalarsHomologyMap (algebraMap R (IsLocalRing.ResidueField R))
      D.complex (((q + 1 : ℕ) : ℤ) - 1)) ↔
      Epi (extendScalarsHomologyMap (algebraMap R (IsLocalRing.ResidueField R))
        D.complex (q : ℤ)) := by rw [hp]
  exact hfree.trans (hmodel.trans (hprev.trans
    (D.moduleCohomologyBaseChangeMap_epi_iff e hflat _ q).symm))

/-- Original residue-field surjectivity in degree zero makes the unchanged original
degree-zero cohomology module free. The actual model's strict lower bound discharges
the negative predecessor, so no reducedness hypothesis is required. -/
theorem ProjectiveCohomologyModel.free_moduleCohomology_zero_of_epi_residue
    (D : ProjectiveCohomologyModel R ι i f M n) [M.IsQuasicoherent]
    (e : ι ≃ Fin (n + 1)) (hflat : Scheme.Modules.relativeFlat f M)
    [Epi (moduleCohomologyBaseChangeMap f (algebraMap R (IsLocalRing.ResidueField R)) M 0)] :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M 0
    Module.Free R (Sheaf.H.{u + 1} (moduleAddSheaf X M) 0) := by
  let (j : ℤ) : Module.Finite R (D.complex.X j) := D.finite_X j
  let (j : ℤ) : Module.Projective R (D.complex.X j) := D.projective_X j
  let : D.complex.IsStrictlyGE 0 := D.lowerBound
  let := moduleCohomologyModuleOfHom X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M 0
  let : Epi (extendScalarsHomologyMap (algebraMap R (IsLocalRing.ResidueField R))
      D.complex 0) :=
    (D.moduleCohomologyBaseChangeMap_epi_iff e hflat _ 0).mp inferInstance
  let K : CochainComplex (ModuleCat.{u} (IsLocalRing.ResidueField R)) ℤ :=
    ((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
      (.up ℤ)).obj D.complex
  let : Epi (extendScalarsHomologyMap (algebraMap R (IsLocalRing.ResidueField R))
      D.complex ((0 : ℤ) - 1)) := (K.isZero_of_isGE 0 (0 - 1) (by omega)).epi _
  let : Module.Free R (D.complex.homology 0) :=
    (D.complex.free_homology_iff_epi_residue_predecessor 0).mpr inferInstance
  exact Module.Free.of_equiv (D.cohomologyLinearEquiv e 0)

/-- For an actual projective embedding over a Noetherian local base, surjectivity of
the original residue-field cohomology map gives arbitrary base change in that degree.
The universal finite-projective model is constructed by the proved geometric supplier. -/
theorem moduleCohomologyBaseChangeMap_isIso_of_epi_residue_of_projectiveEmbedding
    [IsNoetherianRing R] (e : ι ≃ Fin (n + 1)) (hf : i ≫ toSpec R ι = f)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ)
    [Epi (moduleCohomologyBaseChangeMap f (algebraMap R (IsLocalRing.ResidueField R)) M q)]
    {B : Type u} [CommRing B] (σ : R →+* B) :
    IsIso (moduleCohomologyBaseChangeMap f σ M q) := by
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  let D := projectiveCohomologyModelOfEmbedding R ι i f M n e hf hM hflat
  exact D.moduleCohomologyBaseChangeMap_isIso_of_epi_residue e hflat q σ

/-- Under original residue-field surjectivity in degree `q+1`, an actual projective
embedding over a Noetherian local base has free cohomology in that degree exactly when
the original predecessor map is surjective. Nonreduced bases are allowed. -/
theorem moduleCohomology_free_iff_epi_residue_predecessor_of_projectiveEmbedding
    [IsNoetherianRing R] (e : ι ≃ Fin (n + 1)) (hf : i ≫ toSpec R ι = f)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ)
    [Epi (moduleCohomologyBaseChangeMap f (algebraMap R (IsLocalRing.ResidueField R)) M
      (q + 1))] :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M (q + 1)
    Module.Free R (Sheaf.H.{u + 1} (moduleAddSheaf X M) (q + 1)) ↔
      Epi (moduleCohomologyBaseChangeMap f (algebraMap R (IsLocalRing.ResidueField R)) M q) := by
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  let D := projectiveCohomologyModelOfEmbedding R ι i f M n e hf hM hflat
  exact D.free_moduleCohomology_iff_epi_residue_predecessor e hflat q

/-- In degree zero, original residue-field surjectivity alone gives free cohomology
for coherent relatively flat coefficients on the actual projective embedding. -/
theorem moduleCohomology_zero_free_of_epi_residue_of_projectiveEmbedding
    [IsNoetherianRing R] (e : ι ≃ Fin (n + 1)) (hf : i ≫ toSpec R ι = f)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M)
    [Epi (moduleCohomologyBaseChangeMap f (algebraMap R (IsLocalRing.ResidueField R)) M 0)] :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M 0
    Module.Free R (Sheaf.H.{u + 1} (moduleAddSheaf X M) 0) := by
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  let D := projectiveCohomologyModelOfEmbedding R ι i f M n e hf hM hflat
  exact D.free_moduleCohomology_zero_of_epi_residue e hflat

end AlgebraicGeometry.Scheme.Cohomology
