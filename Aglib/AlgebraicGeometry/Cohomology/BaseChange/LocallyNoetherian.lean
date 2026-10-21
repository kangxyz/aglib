/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Homology.FiniteProjective.SingleModel
public import Aglib.AlgebraicGeometry.Cohomology.Proper.LocalCriterion
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Relative

/-!
# Local proper cohomology from residue concentration

This candidate connects the actual proper finite Cech model to its native
residue-concentration theorem. It supplies a local-ring component of the
locally Noetherian application, including nonreduced local rings. It does not
assert the global scheme theorem or the degree-zero sheaf-mate identification.

Source basis: Aglib revision b001ca8814edba7b56866202765094b724ad0c9e,
`Cohomology/Proper/FiniteModel.lean:63-91`,
`Cohomology/FiniteModel/BaseChangeCriterion.lean:46-72`, and
`Algebra/Homology/FiniteProjective/SingleModel.lean:140-211`.
The input below is vanishing on the actual native residue-field fibre, rather
than an additional base-change or freeness premise. Geometric-to-residue
transport and globalization remain separate obligations.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.BaseChange.LocallyNoetherian` at
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`83a37ac7a172ab89172cfb634978a8bfcc1ceb656b22150a944f15856e5f2c71`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

/-- Over a Noetherian local ring, vanishing of the original positive-degree
residue-fibre cohomology makes original degree-zero cohomology finite free,
with its original residue rank, and makes every original scalar cohomology
comparison invertible. Neither reducedness nor flatness of the new ring is
assumed. This is a local scalar statement, not the global sheaf conclusion. -/
theorem properLocalCohomology_of_residue_vanishing
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (M : X.Modules) (hM : affineLocallyFiniteType X M)
    (hflat : Scheme.Modules.relativeFlat f M)
    (hvan : ∀ q : ℕ, 0 < q → Subsingleton
      (fibreCohomology f M (IsLocalRing.ResidueField R)
        (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))) q)) :
    let k := IsLocalRing.ResidueField R
    let t := Spec.map (CommRingCat.ofHom (algebraMap R k))
    let Y := pullback f t
    let N := (Scheme.Modules.pullback (pullback.fst f t)).obj M
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    let β := (pullback.snd f t).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M 0
    letI := moduleCohomologyModuleOfHom Y β N 0
    Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X M) 0) ∧
      Module.Free R (Sheaf.H.{u + 1} (moduleAddSheaf X M) 0) ∧
      Module.finrank R (Sheaf.H.{u + 1} (moduleAddSheaf X M) 0) =
        Module.finrank k (Sheaf.H.{u + 1} (moduleAddSheaf Y N) 0) ∧
      ∀ (B : Type u) [CommRing B] (σ : R →+* B) (q : ℕ),
        IsIso (moduleCohomologyBaseChangeMap f σ M q) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  obtain ⟨n, U, hU, hcover, ⟨D⟩⟩ :=
    exists_finiteCechCohomologyModel_of_proper (CommRingCat.of R) f M hM hflat
  let (i : ℤ) : Module.Finite R (D.complex.X i) := D.finite_X i
  let (i : ℤ) : Module.Projective R (D.complex.X i) := D.projective_X i
  let : D.complex.IsStrictlyGE 0 := D.lowerBound
  let : D.complex.IsStrictlyLE (n : ℤ) := D.upperBound
  let k := IsLocalRing.ResidueField R
  let ρ := algebraMap R k
  let L : CochainComplex (ModuleCat.{u} k) ℤ :=
    ((ModuleCat.extendScalars ρ).mapHomologicalComplex (.up ℤ)).obj D.complex
  have hfibre : ∀ i : ℤ, i ≠ 0 → IsZero (L.homology i) := by
    intro i hi
    by_cases hneg : i < 0
    · exact L.isZero_of_isGE 0 i (by omega)
    · let q := i.toNat
      have hq : (q : ℤ) = i := by dsimp [q]; omega
      have hpos : 0 < q := by omega
      rw [← hq]
      let : Subsingleton (Sheaf.H.{u + 1}
          (moduleAddSheaf (Limits.pullback f (Spec.map (CommRingCat.ofHom ρ)))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom ρ)))).obj M)) q) :=
        hvan q hpos
      let : Subsingleton (L.homology (q : ℤ)) :=
        (D.baseChangeCohomologyLinearEquiv hU hcover Equiv.ulift hflat ρ q).injective.subsingleton
      exact ModuleCat.isZero_of_subsingleton _
  let : Module.Finite R (D.complex.homology 0) :=
    CochainComplex.finite_homology_zero_of_residue_concentration
      0 (n : ℤ) D.complex hfibre
  let : Module.Free R (D.complex.homology 0) :=
    CochainComplex.free_homology_zero_of_residue_concentration
      0 (n : ℤ) D.complex hfibre
  let t := Spec.map (CommRingCat.ofHom ρ)
  let Y := Limits.pullback f t
  let N := (Scheme.Modules.pullback (Limits.pullback.fst f t)).obj M
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let β := (Limits.pullback.snd f t).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  let := moduleCohomologyModuleOfHom X α M 0
  let := moduleCohomologyModuleOfHom Y β N 0
  dsimp only
  refine ⟨Module.Finite.equiv (D.cohomologyLinearEquiv hU hcover Equiv.ulift 0),
    Module.Free.of_equiv (D.cohomologyLinearEquiv hU hcover Equiv.ulift 0), ?_, ?_⟩
  · calc
      _ = Module.finrank R (D.complex.homology 0) :=
        (D.cohomologyLinearEquiv hU hcover Equiv.ulift 0).finrank_eq.symm
      _ = Module.finrank k (L.homology 0) :=
        CochainComplex.finrank_homology_zero_eq_residue_of_concentration
          0 (n : ℤ) D.complex hfibre
      _ = _ :=
        (D.baseChangeCohomologyLinearEquiv hU hcover Equiv.ulift hflat ρ 0).finrank_eq
  · intro B _ σ q
    apply (D.moduleCohomologyBaseChangeMap_isIso_iff hU hcover Equiv.ulift hflat σ q).mpr
    exact CochainComplex.extendScalarsHomologyMap_isIso_of_residue_concentration
      σ 0 (n : ℤ) D.complex hfibre (q : ℤ)

end AlgebraicGeometry.Scheme.Cohomology
