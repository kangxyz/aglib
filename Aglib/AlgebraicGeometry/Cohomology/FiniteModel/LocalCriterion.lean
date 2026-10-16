/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.BaseChangeCriterion
public import Aglib.Algebra.Homology.CochainComplex.BaseChangeCriterion

/-!
# Original local cohomology and base-change criteria on the same finite-cover model

The original geometric residue-field comparison is identified with the native
homology mate of the same actual model. Its surjectivity gives arbitrary
original base change. In adjacent degrees it detects freeness of unchanged
cohomology; degree zero uses the actual strict lower term bound.
Neither reducedness nor Noetherianity is needed once the model is supplied.
The original coefficient after base change is its ordinary pullback.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex

namespace AlgebraicGeometry.Scheme.Cohomology.FiniteCechCohomologyModel

variable {R : Type u} [CommRing R] [IsLocalRing R] {ι : Type u}
  {X : Scheme.{u}} [X.IsSeparated] {f : X ⟶ Spec (CommRingCat.of R)}
  {U : ι → X.Opens} {M : X.Modules} [M.IsQuasicoherent] {n : ℕ}
  (D : FiniteCechCohomologyModel R ι X f U M n)
  (hU : ∀ j, IsAffineOpen (U j)) (hcover : iSup U = ⊤)
  (e : ι ≃ Fin (n + 1)) (hflat : Scheme.Modules.relativeFlat f M)

local instance modelFinite (j : ℤ) : Module.Finite R (D.complex.X j) := D.finite_X j
local instance modelProjective (j : ℤ) : Module.Projective R (D.complex.X j) := D.projective_X j

include D hU hcover e hflat

/-- Surjectivity of the original residue-field cohomology comparison gives invertibility
of the original geometric comparison after every ring map over the local base. -/
theorem moduleCohomologyBaseChangeMap_isIso_of_epi_residue (q : ℕ)
    (hres : Epi (moduleCohomologyBaseChangeMap f
      (algebraMap R (IsLocalRing.ResidueField R)) M q))
    {B : Type u} [CommRing B] (σ : R →+* B) :
    IsIso (moduleCohomologyBaseChangeMap f σ M q) := by
  let S := D.complex.sc (q : ℤ)
  let : Module.Finite R S.X₂ := by
    change Module.Finite R (D.complex.X (q : ℤ))
    infer_instance
  let : Module.Finite R S.X₃ := by
    change Module.Finite R (D.complex.X ((ComplexShape.up ℤ).next (q : ℤ)))
    infer_instance
  let : Module.Flat R S.X₃ := by
    change Module.Flat R (D.complex.X ((ComplexShape.up ℤ).next (q : ℤ)))
    infer_instance
  let : Epi (ModuleCat.homologyBaseChangeMap
      (algebraMap R (IsLocalRing.ResidueField R)) S) :=
    (D.moduleCohomologyBaseChangeMap_epi_iff hU hcover e hflat _ q).mp hres
  apply (D.moduleCohomologyBaseChangeMap_isIso_iff hU hcover e hflat σ q).mpr
  exact CategoryTheory.ShortComplex.homologyBaseChangeMap_isIso_of_epi_residue.{u, 0, u} σ S

/-- Under surjectivity of the original degree-`q+1` residue-field map, original
cohomology in that degree is free exactly when the original degree-`q` residue map is
surjective. No reducedness or Noetherianity is assumed. -/
theorem free_moduleCohomology_succ_iff_epi_residue (q : ℕ)
    (hres : Epi (moduleCohomologyBaseChangeMap f
      (algebraMap R (IsLocalRing.ResidueField R)) M (q + 1))) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M (q + 1)
    Module.Free R (Sheaf.H.{u + 1} (moduleAddSheaf X M) (q + 1)) ↔
      Epi (moduleCohomologyBaseChangeMap f
        (algebraMap R (IsLocalRing.ResidueField R)) M q) := by
  let : Epi (extendScalarsHomologyMap (algebraMap R (IsLocalRing.ResidueField R))
      D.complex ((q + 1 : ℕ) : ℤ)) :=
    (D.moduleCohomologyBaseChangeMap_epi_iff hU hcover e hflat _ (q + 1)).mp hres
  have hnative := D.complex.free_homology_iff_epi_residue_predecessor ((q + 1 : ℕ) : ℤ)
  have hpred : ((q + 1 : ℕ) : ℤ) - 1 = (q : ℤ) := by omega
  rw [hpred] at hnative
  let := moduleCohomologyModuleOfHom X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M (q + 1)
  have he : Module.Free R (Sheaf.H.{u + 1} (moduleAddSheaf X M) (q + 1)) ↔
      Module.Free R (D.complex.homology ((q + 1 : ℕ) : ℤ)) := by
    constructor
    · intro h
      let := h
      exact Module.Free.of_equiv (D.cohomologyLinearEquiv hU hcover e (q + 1)).symm
    · intro h
      let := h
      exact Module.Free.of_equiv (D.cohomologyLinearEquiv hU hcover e (q + 1))
  exact he.trans (hnative.trans
    (D.moduleCohomologyBaseChangeMap_epi_iff hU hcover e hflat _ q).symm)

/-- In degree zero, surjectivity of the original residue-field comparison already makes
original cohomology free. The negative predecessor vanishes by the actual model bound. -/
theorem free_moduleCohomology_zero_of_epi_residue
    (hres : Epi (moduleCohomologyBaseChangeMap f
      (algebraMap R (IsLocalRing.ResidueField R)) M 0)) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M 0
    Module.Free R (Sheaf.H.{u + 1} (moduleAddSheaf X M) 0) := by
  let : D.complex.IsStrictlyGE 0 := D.lowerBound
  let k := IsLocalRing.ResidueField R
  let L : CochainComplex (ModuleCat.{u} k) ℤ :=
    ((ModuleCat.extendScalars (algebraMap R k)).mapHomologicalComplex (.up ℤ)).obj D.complex
  let : Subsingleton (L.homology (-1)) :=
    ModuleCat.subsingleton_of_isZero (L.isZero_of_isGE 0 (-1) (by omega))
  have hprev : Epi (extendScalarsHomologyMap (algebraMap R k) D.complex (-1)) :=
    (ModuleCat.epi_iff_surjective _).mpr (fun x => ⟨0, Subsingleton.elim _ _⟩)
  let : Epi (extendScalarsHomologyMap (algebraMap R k) D.complex 0) :=
    (D.moduleCohomologyBaseChangeMap_epi_iff hU hcover e hflat _ 0).mp hres
  let : Module.Free R (D.complex.homology 0) :=
    (D.complex.free_homology_iff_epi_residue_predecessor 0).mpr hprev
  let := moduleCohomologyModuleOfHom X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M 0
  exact Module.Free.of_equiv (D.cohomologyLinearEquiv hU hcover e 0)

end AlgebraicGeometry.Scheme.Cohomology.FiniteCechCohomologyModel
