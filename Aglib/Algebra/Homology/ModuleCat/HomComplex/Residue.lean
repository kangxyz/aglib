/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Cohomology
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Shift
public import Aglib.Algebra.Homology.DerivedCategory.TStructure.Homology
public import Aglib.RingTheory.RegularLocalRing.FiniteLengthExtDuality
public import Mathlib.RingTheory.LocalRing.Length
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Adjunction.InjectiveComplex
public import Mathlib.CategoryTheory.Abelian.Injective.Extend

/-!
# The intrinsic residue line for the actual coinduced coefficient

For a finite local algebra over a regular local ring of dimension two,
the actual A-module Hom cohomology has length one in degree two and is
zero in every other integer degree. Restriction to R is compared with
native Ext through the original coefficient augmentation. The finite
positive residue degree then computes the length for the existing
A-action. No field trace or coefficient field is chosen.

The original signed source shift and homology-normalized single comparison
identify the derived dual of the residue single in degree one with that
same single. The finite-length Ext supplier is used in its native
same-universe setting.
-/

@[expose] public section
noncomputable section


open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing

universe u v w z

private theorem residue_isSimple (A : Type*) [CommRing A] [IsLocalRing A] :
    IsSimpleModule A (ResidueField A) := by
  change IsSimpleModule A (A ⧸ maximalIdeal A)
  exact (isSimpleModule_iff_isCoatom (R := A) (M := A)
    (m := (maximalIdeal A : Submodule A A))).mpr
      (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal A))

private theorem normalizedSingleHomology_comp
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : DerivedCategory C) (n : ℤ) [K.IsGE n] [K.IsLE n]
    (M : C) (e : (DerivedCategory.homologyFunctor C n).obj K ≅ M) :
    (DerivedCategory.homologyFunctor C n).map
        (DerivedCategory.isoSingleHomology K n ≪≫
          (DerivedCategory.singleFunctor C n).mapIso e).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).hom.app M = e.hom := by
  let H := DerivedCategory.homologyFunctor C n
  let S := DerivedCategory.singleFunctor C n
  let E := DerivedCategory.singleFunctorCompHomologyFunctorIso C n
  have h := E.hom.naturality e.hom
  change H.map (S.map e.hom) ≫ E.hom.app M = E.hom.app (H.obj K) ≫ e.hom at h
  change H.map ((DerivedCategory.isoSingleHomology K n).hom ≫ S.map e.hom) ≫
    E.hom.app M = e.hom
  rw [Functor.map_comp, Category.assoc, h, ← Category.assoc,
    DerivedCategory.isoSingleHomology_homology, Category.id_comp]

namespace IsLocalRing

/-- The actual residue extension of a finite local algebra has finite
length over the original base, without a coefficient-field choice. -/
theorem isFiniteLength_residue_of_finite_local
    (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    [IsLocalRing R] [IsLocalRing A] [Algebra R A]
    [IsLocalHom (algebraMap R A)] [Module.Finite R A] :
    IsFiniteLength R (ResidueField A) := by
  let : IsSimpleModule A (ResidueField A) := residue_isSimple A
  apply Module.length_ne_top_iff.mp
  rw [IsLocalRing.length_restrictScalars R A (ResidueField A),
    Module.length_eq_one, one_mul, Module.length_eq_finrank]
  simp

/-- Equality with the original restricted residue length forces length one
for the intrinsic A-action. The residue degree is finite and strictly positive. -/
theorem length_eq_one_of_restriction_length
    (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    [IsLocalRing R] [IsLocalRing A] [Algebra R A]
    [IsLocalHom (algebraMap R A)] [Module.Finite R A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    (h : Module.length R M = Module.length R (ResidueField A)) :
    Module.length A M = 1 := by
  let f : ℕ∞ := Module.length (ResidueField R) (ResidueField A)
  have hf₀ : f ≠ 0 := (Module.length_pos (R := ResidueField R)
    (M := ResidueField A)).ne'
  have hf_top : f ≠ ⊤ := by
    dsimp [f]
    rw [Module.length_eq_finrank]
    simp
  let : IsSimpleModule A (ResidueField A) := residue_isSimple A
  have hk : Module.length R (ResidueField A) = f := by
    rw [IsLocalRing.length_restrictScalars R A (ResidueField A),
      Module.length_eq_one, one_mul]
  apply (ENat.mul_left_strictMono hf₀ hf_top).injective
  calc
    Module.length A M * f = Module.length R M :=
      (IsLocalRing.length_restrictScalars R A M).symm
    _ = Module.length R (ResidueField A) := h
    _ = 1 * f := by rw [hk, one_mul]

end IsLocalRing

namespace CochainComplex.HomComplex

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [IsLocalRing A]

private def restrictionAlgebraEquiv (M : ModuleCat.{u} A)
    [Module R M] [IsScalarTower R A M] :
    (ModuleCat.restrictScalars (algebraMap R A)).obj M ≃ₗ[R] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change (algebraMap R A r) • (show M from x) = r • (show M from x)
    exact IsScalarTower.algebraMap_smul A r (show M from x)

/-- The residue dual complex has the original A-action from native coinduction. -/
def residueDualComplex (I : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  moduleComplex A
    ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (ResidueField A)))
    (((ModuleCat.coextendScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj I)

/-- The cohomology is an actual A-module before restriction or any Ext comparison. -/
def residueDualHomology (I : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) : ModuleCat.{u} A :=
  (residueDualComplex (A := A) I).homology n

omit [IsLocalRing A] in
/-- Coinduction of the actual injective resolution is K-injective. -/
theorem coinducedResolution_isKInjective
    (I : InjectiveResolution (ModuleCat.of R R)) :
    CochainComplex.IsKInjective
      (show CochainComplex (ModuleCat.{u} A) ℤ from
        ((ModuleCat.coextendScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj
          I.cochainComplex) :=
  (ModuleCat.restrictCoextendScalarsAdj (algebraMap R A)).isKInjective_map_of_injectiveComplex
    I.cochainComplex 0

section Length

variable [IsRegularLocalRing R] [IsLocalHom (algebraMap R A)] [Module.Finite R A]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The original R-linear coinduced Hom-cohomology comparison transfers
the passed Ext-two length theorem to the genuine A-cohomology module. -/
theorem residueDualHomology_length_eq_one (hd : ringKrullDim R = (2 : ℕ))
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective]
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I) [QuasiIso u] :
    Module.length A (residueDualHomology (A := A) I 2) = 1 := by
  let F : ModuleCat.{u} A ⥤ ModuleCat.{u} R :=
    ModuleCat.restrictScalars (algebraMap R A)
  let M : ModuleCat.{u} A := ModuleCat.of A (ResidueField A)
  let L : ModuleCat.{u} A := residueDualHomology I 2
  let : Module R L := Module.compHom L (algebraMap R A)
  let : IsScalarTower R A L :=
    ⟨fun r a x => by
      change (r • a) • x = (algebraMap R A r) • (a • x)
      rw [Algebra.smul_def]
      exact mul_smul _ _ _⟩
  let eM : F.obj M ≃ₗ[R] ResidueField A := restrictionAlgebraEquiv M
  have hM : IsFiniteLength R (F.obj M) := eM.symm.isFiniteLength
    (IsLocalRing.isFiniteLength_residue_of_finite_local R A)
  let E : L ≃ₗ[R] IsRegularLocalRing.extDualTwo R (F.obj M) :=
    (restrictionAlgebraEquiv L).symm.trans
      (coinducedSingleHomologyExtLinearEquiv.{u, u, u, w, u}
        (algebraMap R A) M (ModuleCat.of R R) I u 2)
  have hlen : Module.length R L = Module.length R (ResidueField A) := by
    calc
      Module.length R L = Module.length R (IsRegularLocalRing.extDualTwo R (F.obj M)) :=
        E.length_eq
      _ = Module.length R (F.obj M) :=
        IsRegularLocalRing.length_extDualTwo R hd (F.obj M) hM
      _ = Module.length R (ResidueField A) := eM.length_eq
  exact IsLocalRing.length_eq_one_of_restriction_length R A L hlen

/-- A choice of residue-line isomorphism for the original A-action.
No trace functional or separability condition is used. -/
theorem nonempty_residueDualHomology_linearEquiv (hd : ringKrullDim R = (2 : ℕ))
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective]
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I) [QuasiIso u] :
    Nonempty (residueDualHomology (A := A) I 2 ≃ₗ[A] ResidueField A) := by
  let : IsSimpleModule A (residueDualHomology (A := A) I 2) :=
    Module.length_eq_one_iff.mp (residueDualHomology_length_eq_one hd I u)
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
    (inferInstance : IsSimpleModule A (residueDualHomology (A := A) I 2))
  have hm' : m = maximalIdeal A := IsLocalRing.eq_maximalIdeal hm
  subst m
  exact ⟨e⟩

/-- Original coinduced residue Hom cohomology is zero in every degree
other than two. Nonnegative degrees use the actual Ext comparison;
negative degrees use the actual coefficient resolution's lower term bound. -/
theorem residueDualHomology_isZero_of_ne_two (hd : ringKrullDim R = (2 : ℕ))
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] [I.IsStrictlyGE 0]
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I) [QuasiIso u]
    (n : ℤ) (hn : n ≠ 2) : IsZero (residueDualHomology (A := A) I n) := by
  let F : ModuleCat.{u} A ⥤ ModuleCat.{u} R :=
    ModuleCat.restrictScalars (algebraMap R A)
  let M : ModuleCat.{u} A := ModuleCat.of A (ResidueField A)
  cases n with
  | ofNat n =>
    let eM : F.obj M ≃ₗ[R] ResidueField A := restrictionAlgebraEquiv M
    have hM : IsFiniteLength R (F.obj M) := eM.symm.isFiniteLength
      (IsLocalRing.isFiniteLength_residue_of_finite_local R A)
    let E := coinducedSingleHomologyExtLinearEquiv.{u, u, u, w, u}
      (algebraMap R A) M (ModuleCat.of R R) I u n
    let : Subsingleton (Ext (F.obj M) (ModuleCat.of R R) n) :=
      IsRegularLocalRing.subsingleton_ext_of_isFiniteLength_ne_two R hd
        (F.obj M) hM n (fun h => hn (congrArg Int.ofNat h))
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact ⟨fun x y => E.injective (Subsingleton.elim _ _)⟩
  | negSucc n =>
    let J : CochainComplex (ModuleCat.{u} A) ℤ :=
      ((ModuleCat.coextendScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj I
    let : J.IsStrictlyGE 0 := by dsimp [J]; infer_instance
    let K := moduleComplex A ((singleFunctor (ModuleCat.{u} A) 0).obj M) J
    let : K.IsStrictlyGE 0 := moduleComplex_single_isStrictlyGE_zero.{u, u} M J
    exact K.isZero_of_isGE 0 (Int.negSucc n) (by omega)

/-- The actual residue dual complex has no homology below degree two. -/
theorem residueDualComplex_isGE_two (hd : ringKrullDim R = (2 : ℕ))
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] [I.IsStrictlyGE 0]
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I) [QuasiIso u] :
    (residueDualComplex (A := A) I).IsGE 2 := by
  rw [isGE_iff]
  intro i hi
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ i).mpr
  exact residueDualHomology_isZero_of_ne_two hd I u i (by omega)

/-- The actual residue dual complex has no homology above degree two. -/
theorem residueDualComplex_isLE_two (hd : ringKrullDim R = (2 : ℕ))
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] [I.IsStrictlyGE 0]
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I) [QuasiIso u] :
    (residueDualComplex (A := A) I).IsLE 2 := by
  rw [isLE_iff]
  intro i hi
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ i).mpr
  exact residueDualHomology_isZero_of_ne_two hd I u i (by omega)

/-- The residue dual complex is its original A-homology placed in degree two,
using the homology-normalized single comparison. -/
def residueDualComplexSingleIso [HasDerivedCategory.{z} (ModuleCat.{u} A)]
    (hd : ringKrullDim R = (2 : ℕ))
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] [I.IsStrictlyGE 0]
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I) [QuasiIso u] :
    DerivedCategory.Q.obj (residueDualComplex (A := A) I) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 2).obj
        (residueDualHomology (A := A) I 2) := by
  let := residueDualComplex_isGE_two (A := A) hd I u
  let := residueDualComplex_isLE_two (A := A) hd I u
  exact DerivedCategory.isoSingleHomology
      (DerivedCategory.Q.obj (residueDualComplex (A := A) I)) 2 ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 2).mapIso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 2).app
        (residueDualComplex (A := A) I))

/-- The comparison induces the original homology identification, with no scalar change. -/
theorem residueDualComplexSingleIso_homology
    [HasDerivedCategory.{z} (ModuleCat.{u} A)] (hd : ringKrullDim R = (2 : ℕ))
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] [I.IsStrictlyGE 0]
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I) [QuasiIso u] :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 2).map
        (residueDualComplexSingleIso (A := A) hd I u).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 2).hom.app
        (residueDualHomology (A := A) I 2) =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 2).hom.app
        (residueDualComplex (A := A) I) := by
  let := residueDualComplex_isGE_two (A := A) hd I u
  let := residueDualComplex_isLE_two (A := A) hd I u
  exact normalizedSingleHomology_comp
    (DerivedCategory.Q.obj (residueDualComplex (A := A) I)) 2
    (residueDualHomology (A := A) I 2)
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 2).app
      (residueDualComplex (A := A) I))

/-- The genuine unshifted derived dual of the residue is its intrinsic
residue line placed in degree two. Only the final line identification is chosen. -/
theorem nonempty_derivedResidueIso
    [HasDerivedCategory.{z} (ModuleCat.{u} A)]
    (hd : ringKrullDim R = (2 : ℕ))
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] [I.IsStrictlyGE 0]
    [CochainComplex.IsKInjective
      (show CochainComplex (ModuleCat.{u} A) ℤ from
        ((ModuleCat.coextendScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj I)]
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I) [QuasiIso u] :
    Nonempty
      ((derivedDual
          (((ModuleCat.coextendScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj I)).obj
          (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A (ResidueField A)))) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 2).obj
          (ModuleCat.of A (ResidueField A))) := by
  let M : ModuleCat.{u} A := ModuleCat.of A (ResidueField A)
  let S := (singleFunctor (ModuleCat.{u} A) 0).obj M
  let J : CochainComplex (ModuleCat.{u} A) ℤ :=
    ((ModuleCat.coextendScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj I
  obtain ⟨eL⟩ := nonempty_residueDualHomology_linearEquiv (A := A) hd I u
  let eM : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M ≅
      DerivedCategory.Q.obj S :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app M
  exact ⟨(derivedDual J).mapIso eM.symm.op ≪≫
    (derivedDualFactors J).app (Opposite.op S) ≪≫
    residueDualComplexSingleIso (A := A) hd I u ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 2).mapIso eL.toModuleIso⟩

/-- The actual residue object in degree one has its genuine derived dual
again in degree one, through the native signed source-shift comparison. -/
theorem nonempty_derivedResidueDegreeOneIso
    [HasDerivedCategory.{z} (ModuleCat.{u} A)]
    (hd : ringKrullDim R = (2 : ℕ))
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] [I.IsStrictlyGE 0]
    [CochainComplex.IsKInjective
      (show CochainComplex (ModuleCat.{u} A) ℤ from
        ((ModuleCat.coextendScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj I)]
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I) [QuasiIso u] :
    Nonempty
      ((derivedDual
          (((ModuleCat.coextendScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj I)).obj
          (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 1).obj
            (ModuleCat.of A (ResidueField A)))) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 1).obj
          (ModuleCat.of A (ResidueField A))) := by
  let M : ModuleCat.{u} A := ModuleCat.of A (ResidueField A)
  let S := (singleFunctor (ModuleCat.{u} A) 0).obj M
  let J : CochainComplex (ModuleCat.{u} A) ℤ :=
    ((ModuleCat.coextendScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj I
  obtain ⟨e₀⟩ := nonempty_derivedResidueIso (A := A) hd I u
  let eM : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M ≅
      DerivedCategory.Q.obj S :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app M
  let eSource : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 1).obj M ≅
      (DerivedCategory.Q.obj S)⟦(-1 : ℤ)⟧ :=
    (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso
      (-1) 1 0 (by omega)).app M).symm ≪≫
      (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-1)).mapIso eM
  let eDual : (derivedDual J).obj (Opposite.op (DerivedCategory.Q.obj S)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 2).obj M :=
    (derivedDual J).mapIso eM.op ≪≫ e₀
  exact ⟨(derivedDual J).mapIso eSource.symm.op ≪≫
    derivedDualShiftObjIso J S (-1) ≪≫
    (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) 1).mapIso eDual ≪≫
    ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso 1 1 2 (by omega)).app M⟩

/-- An actual injective resolution supplies every coefficient condition for the residue dual.
The endpoint has no coinduced K-injectivity premise. -/
theorem nonempty_derivedResidueDegreeOneIso_of_injectiveResolution
    [HasDerivedCategory.{z} (ModuleCat.{u} A)] (hd : ringKrullDim R = (2 : ℕ))
    (I : InjectiveResolution (ModuleCat.of R R)) :
    letI := coinducedResolution_isKInjective (A := A) I
    Nonempty
      ((derivedDual
          (((ModuleCat.coextendScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj
            I.cochainComplex)).obj
          (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 1).obj
            (ModuleCat.of A (ResidueField A)))) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 1).obj
          (ModuleCat.of A (ResidueField A))) := by
  let := coinducedResolution_isKInjective (A := A) I
  let : I.cochainComplex.IsKInjective := CochainComplex.isKInjective_of_injective _ 0
  exact nonempty_derivedResidueDegreeOneIso (A := A) hd I.cochainComplex I.ι'

end Length

end CochainComplex.HomComplex
