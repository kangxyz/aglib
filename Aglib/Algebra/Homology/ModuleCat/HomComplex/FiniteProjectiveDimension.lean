/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ModuleCat.HomComplex.ConcentratedHomothety
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Postnikov
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Shift
public import Aglib.Algebra.Homology.DerivedCategory.TStructure.InjectiveDimension
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction.Finite
public import Mathlib.RingTheory.Regular.ProjectiveDimension

/-!
# Finite projective dimension of the original canonical homology

For a finite algebra over a regular local ring, original coinduced duals of
finite modules have bounded cohomology. If coinduction of the regular base
is concentrated in degree `n`, its actual homothety identifies the dual of
the same selected homology with the regular target ring in degree `n`.

Finite self-injective dimension of the target then kills dualized high Ext.
The original bidual evaluation detects those morphisms, and the native
finite-target Ext criterion gives finite projective dimension. No global
duality equivalence, supplied perfect model, or canonical freeness is assumed.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex Opposite

universe u a b w

namespace CochainComplex.HomComplex

section OriginalComparisons

variable {S : Type u} [CommRing S] [HasDerivedCategory.{b} (ModuleCat.{u} S)]

/-- The actual derived dual of a module single, using the existing
single/localization and original fixed-coefficient comparisons. -/
def derivedDualSingleComplexIso
    (J : CochainComplex (ModuleCat.{u} S) ℤ) [J.IsKInjective] (M : ModuleCat.{u} S) :
    (derivedDual J).obj (op ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj M)) ≅
      DerivedCategory.Q.obj (moduleComplex S ((singleFunctor (ModuleCat.{u} S) 0).obj M) J) :=
  (derivedDual J).mapIso
      (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} S) 0).app M).symm.op) ≪≫
    (derivedDualFactors J).app (op ((singleFunctor (ModuleCat.{u} S) 0).obj M))

/-- The actual dual of a shifted single, through the existing signed
source-shift comparison. No global shift-coherence instance is asserted. -/
def derivedDualSingleShiftIso
    (J : CochainComplex (ModuleCat.{u} S) ℤ) [J.IsKInjective]
    (M : ModuleCat.{u} S) (i : ℤ) :
    (derivedDual J).obj (op (((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj M)⟦i⟧)) ≅
      ((derivedDual J).obj
        (op ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj M)))⟦-i⟧ := by
  let c := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} S) 0).app M
  exact (derivedDual J).mapIso
      (((CategoryTheory.shiftFunctor _ i).mapIso c).symm.op) ≪≫
    derivedDualShiftObjIso J ((singleFunctor (ModuleCat.{u} S) 0).obj M) i ≪≫
    (CategoryTheory.shiftFunctor _ (-i)).mapIso ((derivedDual J).mapIso c.op)

/-- The actual homothety identifies the dual of the concentrated homology
with the regular target single shifted by the negative concentration degree. -/
def derivedDualConcentratedHomologyIso
    (J : CochainComplex (ModuleCat.{u} S) ℤ) [J.IsKInjective] [QuasiIso (homothety J)]
    (K : ModuleCat.{u} S) (n : ℤ)
    (c : DerivedCategory.Q.obj J ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} S) n).obj K) :
    (derivedDual J).obj (op ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj K)) ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S S))⟦-n⟧ := by
  let z := concentratedCoefficientZeroIso J K n c
  let h : (derivedDual J).obj (op (DerivedCategory.Q.obj J)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S S) :=
    (derivedDualFactors J).app (op J) ≪≫
      (asIso (DerivedCategory.Q.map (homothety J))).symm ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} S) 0).app (ModuleCat.of S S)).symm
  exact (derivedDual J).mapIso z.op ≪≫ derivedDualShiftObjIso J J n ≪≫
    (CategoryTheory.shiftFunctor _ (-n)).mapIso h

end OriginalComparisons

section RegularBase

variable {R S : Type u} [CommRing R] [CommRing S] [IsRegularLocalRing R]
  (q : R →+* S) (d : ℕ) (hd : ringKrullDim R = (d : ℕ))
  [HasDerivedCategory.{a} (ModuleCat.{u} R)]
  [HasDerivedCategory.{b} (ModuleCat.{u} S)]

include hd in
/-- The actual coinduced dual of a module finite over the regular base has
cohomology in `[0,d]`. The upper bound uses original ambient Ext, not terms
of an arbitrarily chosen finite representative. -/
theorem coinducedDerivedDualSingle_bounds
    (I : InjectiveResolution (ModuleCat.of R R)) (M : ModuleCat.{u} S)
    [Module.Finite R ((ModuleCat.restrictScalars q).obj M)] :
    let J := coinducedCoefficientComplex q I.cochainComplex
    let T := (derivedDual J).obj
      (op ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj M))
    T.IsGE 0 ∧ T.IsLE (d : ℤ) := by
  let : I.cochainComplex.IsKInjective := CochainComplex.isKInjective_of_injective _ 0
  let J := coinducedCoefficientComplex q I.cochainComplex
  let H := moduleComplex S ((singleFunctor (ModuleCat.{u} S) 0).obj M) J
  let : J.IsStrictlyGE 0 := inferInstanceAs
    (CochainComplex.IsStrictlyGE
      (((ModuleCat.coextendScalars q).mapHomologicalComplex (.up ℤ)).obj
        I.cochainComplex) 0)
  let : H.IsStrictlyGE 0 := moduleComplex_single_isStrictlyGE_zero M J
  let : HasProjectiveDimensionLE ((ModuleCat.restrictScalars q).obj M) d :=
    (projectiveDimension_le_iff _ d).mp
      (IsRegularLocalRing.projectiveDimension_le_dimension d R hd _)
  let : H.IsLE (d : ℤ) := by
    rw [CochainComplex.isLE_iff]
    intro j hj
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ j)
    let E : (ModuleCat.restrictScalars q).obj (H.homology (k : ℤ)) ≃ₗ[R]
        Ext.{u} ((ModuleCat.restrictScalars q).obj M) (ModuleCat.of R R) k :=
      coinducedSingleHomologyExtLinearEquiv.{u, u, u, a, u}
        q M (ModuleCat.of R R) I.cochainComplex I.ι' k
    let : Subsingleton (Ext.{u} ((ModuleCat.restrictScalars q).obj M) (ModuleCat.of R R) k) :=
      HasProjectiveDimensionLT.subsingleton ((ModuleCat.restrictScalars q).obj M)
        (d + 1) k (by omega) (ModuleCat.of R R)
    exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun x y => E.injective (Subsingleton.elim _ _)⟩
  let : (DerivedCategory.Q.obj H).IsGE 0 := inferInstance
  let : (DerivedCategory.Q.obj H).IsLE (d : ℤ) := inferInstance
  let c := derivedDualSingleComplexIso J M
  exact ⟨DerivedCategory.TStructure.t.isGE_of_iso c.symm 0,
    DerivedCategory.TStructure.t.isLE_of_iso c.symm (d : ℤ)⟩

end RegularBase

private theorem finite_restrictScalars_of_finite
    {R S : Type u} [CommRing R] [CommRing S] (q : R →+* S)
    [Module.Finite R ((ModuleCat.restrictScalars q).obj (ModuleCat.of S S))]
    (M : ModuleCat.{u} S) [Module.Finite S M] :
    Module.Finite R ((ModuleCat.restrictScalars q).obj M) := by
  let : Module R S := Module.compHom S q
  let : Module R M := Module.compHom M q
  let : Module.Finite R S :=
    inferInstanceAs (Module.Finite R ((ModuleCat.restrictScalars q).obj (ModuleCat.of S S)))
  let : IsScalarTower R S M := ⟨fun r s x => mul_smul (q r) s x⟩
  change Module.Finite R M
  exact Module.Finite.trans S M

section FiniteSelfInjectiveDimension

variable {R S : Type u} [CommRing R] [CommRing S] [IsRegularLocalRing R]
  [IsNoetherianRing S] (q : R →+* S)
  [Module.Finite R ((ModuleCat.restrictScalars q).obj (ModuleCat.of S S))]
  (dR : ℕ) (hdR : ringKrullDim R = (dR : ℕ))
  [HasExt.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{a} (ModuleCat.{u} R)]
  [HasDerivedCategory.{b} (ModuleCat.{u} S)]
  (n : ℕ) (h : ∀ j : ℕ, j ≠ n → Subsingleton
    (Ext.{w} ((ModuleCat.restrictScalars q).obj (ModuleCat.of S S)) (ModuleCat.of R R) j))

include hdR h in
/-- Intrinsic finite self-injective dimension gives finite projective dimension
of the same selected canonical homology. Locality of the target, a trivializing
section, and a projective model over the target are not assumptions. -/
theorem coinducedHomology_hasProjectiveDimensionLE
    (dS : ℕ) [HasInjectiveDimensionLE (ModuleCat.of S S) dS] :
    let K := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
      ((ModuleCat.coextendScalars q).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))
    HasProjectiveDimensionLE K (dS + n) := by
  let K := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
    ((ModuleCat.coextendScalars q).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))
  let : Module.Finite S K :=
    ModuleCat.derivedCoextendScalarsPlusHomology_finite q (ModuleCat.of R R) n
  let I := injectiveResolution (ModuleCat.of R R)
  let : I.cochainComplex.IsKInjective := CochainComplex.isKInjective_of_injective _ 0
  let J := coinducedCoefficientComplex q I.cochainComplex
  let : J.IsKInjective := coinducedCoefficientComplex_isKInjective q I.cochainComplex
  let : QuasiIso (homothety J) := homothety_coinduced_injectiveResolution_quasiIso q dR hdR I
  let D := derivedDual J
  let c := coinducedCoefficientSingleIso.{u, a, b, w} q (ModuleCat.of R R) I n h
  let eK := derivedDualConcentratedHomologyIso J K (n : ℤ) c
  apply ModuleCat.hasProjectiveDimensionLT_of_forall_finite K (dS + n + 1)
  intro L hL
  let : Module.Finite S L := hL
  let : Module.Finite R ((ModuleCat.restrictScalars q).obj L) :=
    finite_restrictScalars_of_finite q L
  let i : ℤ := ((dS + n + 1 : ℕ) : ℤ)
  let X := (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj K
  let Y := ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj L)⟦i⟧
  let DL := D.obj (op ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj L))
  have hB := coinducedDerivedDualSingle_bounds q dR hdR I L
  let : DL.IsGE 0 := hB.1
  let : DL.IsLE (dR : ℤ) := hB.2
  let : (DL⟦-i⟧).IsGE i := DerivedCategory.TStructure.t.isGE_shift DL 0 (-i) i (by omega)
  let : (DL⟦-i⟧).IsLE ((dR : ℤ) + i) :=
    DerivedCategory.TStructure.t.isLE_shift DL (dR : ℤ) (-i) ((dR : ℤ) + i) (by omega)
  let eY := derivedDualSingleShiftIso J L i
  let : (D.obj (op Y)).IsGE i := DerivedCategory.TStructure.t.isGE_of_iso eY.symm i
  let : (D.obj (op Y)).IsLE ((dR : ℤ) + i) :=
    DerivedCategory.TStructure.t.isLE_of_iso eY.symm ((dR : ℤ) + i)
  let : CochainComplex.IsKInjective
      (((ModuleCat.coextendScalars q).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) :=
    inferInstanceAs J.IsKInjective
  have hEval : IsIso ((derivedEvaluation J).app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} S) (-i)).obj L)) :=
    derivedEvaluation_single_isIso_of_restrictFinite q dR hdR L (-i)
      (ModuleCat.of R R) (LinearEquiv.refl R R) I.cochainComplex I.ι'
  let sY : Y ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} S) (-i)).obj L :=
    ((DerivedCategory.singleFunctors (ModuleCat.{u} S)).shiftIso i (-i) 0 (by omega)).app L
  let : IsIso ((derivedEvaluation J).app Y) :=
    (NatTrans.isIso_app_iff_of_iso (derivedEvaluation J) sY).mpr hEval
  apply subsingleton_of_forall_eq 0
  intro x
  let f : X ⟶ Y := x.hom
  have hDf : D.map f.op = 0 := by
    apply (cancel_mono eK.hom).mp
    rw [zero_comp]
    exact DerivedCategory.hom_single_shift_eq_zero_of_injectiveDimension
      (D.obj (op Y)) i ((dR : ℤ) + i) (-(n : ℤ)) (ModuleCat.of S S) dS
      (by dsimp [i]; omega) (D.map f.op ≫ eK.hom)
  have hf : f = 0 := (derivedDual_map_eq_zero_iff J f).mp hDf
  apply Ext.homEquiv.injective
  change f = (0 : Ext.{u} K L (dS + n + 1)).hom
  rw [Ext.zero_hom]
  exact hf

end FiniteSelfInjectiveDimension

end CochainComplex.HomComplex
