/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Regular
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.AffineBase
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.CompletionDescent
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Qcqs
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Isomorphism
public import Aglib.AlgebraicGeometry.Cohomology.Exact.Modules
public import Aglib.RingTheory.IntegralClosure.FlatDescent

/-!
# Rationality of the original normal domain completion

An arbitrary normal proper birational model over the completion is dominated
by an actual normalized point chain. Only that chain is descended. Universal
vanishing over the original local ring, original flat unit-coefficient base
change, and original birational H1 injection give vanishing on the supplied
completed model. No algebraization of that model or resolution existence is
assumed. The original ring is not required to be Nagata.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Cohomology

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities

/-- Universal original structure-H1 vanishing passes to the literal maximal-adic
completion when that completion is a normal domain. Only an actual dominating
normalized-point chain is descended; the arbitrary completed model need not
algebraize. No Nagata hypothesis on the original local ring is required. -/
theorem normalModificationH1Vanishing_completion
    (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S] [IsDomain S]
    [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal S) S)]
    [IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal S) S)]
    (hd : ringKrullDim S = 2) (hRat : NormalModificationH1Vanishing S) :
    NormalModificationH1Vanishing (AdicCompletion (IsLocalRing.maximalIdeal S) S) := by
  let H := AdicCompletion (IsLocalRing.maximalIdeal S) S
  let : IsNoetherianRing H := AdicCompletion.isNoetherianRing S (IsLocalRing.maximalIdeal S)
  let : Module.FaithfullyFlat S H := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : IsIntegrallyClosed S := IsIntegrallyClosed.isIntegrallyClosed_of_faithfullyFlat S H
  have hdH : ringKrullDim H = 2 := (AdicCompletion.ringKrullDim_maximalIdeal_eq S).trans hd
  let : Ring.KrullDimLE 2 H := Ring.krullDimLE_iff.mpr hdH.le
  have hH : IsNagataRing.{u, 0} H := IsNagataRing.of_complete_local_dimLE_two H
  intro Z hZ q hqP hqD hZN hqff
  let : IsIntegral Z := hZ
  let : IsProper q := hqP
  let : IsDominant q := hqD
  obtain ⟨T, beta, a, hT, hbetaD, haD, upper, _htriangle, _hTN, _hTNoeth, _hdT,
    _hbetaP, haP, _hbetaff, haff⟩ :=
    NormalizedPointDomination.exists_domination_of_nagata_base H hH hdH.le q hqff
  let : IsIntegral T := hT
  let : IsDominant beta := hbetaD
  let : IsDominant a := haD
  let : IsProper a := haP
  obtain ⟨C, f, lower, hC, hfD, _hlength, hfP, hfff, E, _hEbase, _hEmodel⟩ :=
    Blowup.exists_completionDescent_chain S hd upper
  let : IsIntegral C := hC
  let : IsDominant f := hfD
  let : IsProper f := hfP
  have hCN : NormalStalks C := lower.normalStalks
    (fun x => (isIntegrallyClosed_and_isDomain_stalk_Spec S x).symm)
  let M : C.Modules := SheafOfModules.unit C.ringCatSheaf
  let : M.IsQuasicoherent := Scheme.Modules.isQuasicoherent_unit C
  have hCH : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf C M) 1) := hRat C f hCN hfff
  let σ : S →+* H := algebraMap S H
  let c := LocalRing.completionSpecMap S
  let P : Scheme.{u} := pullback f c
  let j : P ⟶ C := pullback.fst f c
  have hflat : σ.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hBC := moduleCohomologyBaseChangeMap_isIso_of_quasiSeparated f σ hflat M 1
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom
  let := moduleCohomologyModuleOfHom C α M 1
  let : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf C M) 1) := hCH
  have hz : IsZero ((ModuleCat.extendScalars σ).obj
      (ModuleCat.of S (Sheaf.H.{u + 1} (moduleAddSheaf C M) 1))) :=
    (ModuleCat.extendScalars σ).map_isZero (ModuleCat.isZero_of_subsingleton _)
  have hPull : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf P ((Scheme.Modules.pullback j).obj M)) 1) :=
    ModuleCat.subsingleton_of_isZero (hz.of_iso (@asIso _ _ _ _ _ hBC).symm)
  have hPH : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf P (SheafOfModules.unit P.ringCatSheaf)) 1) :=
    moduleCohomology_subsingleton_of_iso (Scheme.Modules.pullbackUnitIso j) 1 hPull
  have hTH : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf T (SheafOfModules.unit T.ringCatSheaf)) 1) := by
    let : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf P (SheafOfModules.unit P.ringCatSheaf)) 1) := hPH
    exact (moduleCohomologyMapAlong_bijective E.hom
      (Scheme.Hom.structureModuleMap E.hom) 1).2.subsingleton
  have hinj := moduleCohomologyMapAlongLinear_unit_injective_of_isProper_birational
    Z (RingHom.id Γ(Z, ⊤)) a hZN haff
  exact ⟨fun x y => hinj (@Subsingleton.elim _ hTH _ _)⟩

end AlgebraicGeometry.Scheme.RationalSingularities
