/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Residue
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.NormalCoefficient
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.InjectiveResolution
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Homology
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Layers
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# The intrinsic coefficient line of derived residue coinduction

For an actual finite local map from a regular local surface ring to an
arbitrary field, the installed derived coinduction of the original ring
single is concentrated in degree two. Its actual degree-two field-module
homology has dimension one. The map need not be surjective and the residue
extension need not be separable.

The model comparison uses the original resolution inclusion and installed
derived unit. Evaluation at one and the canonical field-to-residue quotient
compare its field-linear homology with the existing intrinsic residue dual.
The coefficient line is never identified with the field by an orientation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open CochainComplex CochainComplex.HomComplex

universe u w z

namespace ModuleCat

/-- The canonical field-to-residue map, as an isomorphism of modules over that field. -/
def fieldResidueModuleIso (k : Type u) [Field k] :
    ModuleCat.of k k ≅ ModuleCat.of k (ResidueField k) :=
  (LinearEquiv.ofBijective (Algebra.linearMap k (ResidueField k))
    ⟨(algebraMap k (ResidueField k)).injective, residue_surjective⟩).toModuleIso

/-- This comparison is the original residue quotient map on elements. -/
theorem fieldResidueModuleIso_hom_apply (k : Type u) [Field k] (a : k) :
    (fieldResidueModuleIso k).hom a = residue k a := rfl

variable (R k : Type u) [CommRing R] [Field k] [Algebra R k]

/-- The literal termwise coinduction of a supplied injective coefficient resolution. -/
abbrev residueCoinductionComplex (I : InjectiveResolution (ModuleCat.of R R)) :
    CochainComplex (ModuleCat.{u} k) ℤ :=
  ((ModuleCat.coextendScalars (algebraMap R k)).mapHomologicalComplex (.up ℤ)).obj
    I.cochainComplex

/-- The original coinduced field action is multiplication on the functional's argument. -/
theorem residueCoinductionComplex_smul_apply
    (I : InjectiveResolution (ModuleCat.of R R)) (n : ℤ)
    (a b : k) (φ : (residueCoinductionComplex R k I).X n) :
    CoextendScalars.equiv (algebraMap R k) (I.cochainComplex.X n) (a • φ) b =
      CoextendScalars.equiv (algebraMap R k) (I.cochainComplex.X n) φ (b * a) := rfl

/-- The ordinary coinduction counit at each resolution term evaluates at the original unit. -/
theorem residueCoinductionComplex_counit_apply
    (I : InjectiveResolution (ModuleCat.of R R)) (n : ℤ)
    (φ : (residueCoinductionComplex R k I).X n) :
    ((ModuleCat.restrictCoextendScalarsAdj (algebraMap R k)).counit.app
      (I.cochainComplex.X n)) φ =
      CoextendScalars.equiv (algebraMap R k) (I.cochainComplex.X n) φ (1 : k) := rfl

/-- The residue Hom complex is the actual coinduced complex, via the canonical
residue source and original evaluation at one. Both maps are field-linear. -/
def residueDualCoinductionComplexIso (I : InjectiveResolution (ModuleCat.of R R)) :
    residueDualComplex (A := k) I.cochainComplex ≅ residueCoinductionComplex R k I :=
  (moduleComplexFunctor k (residueCoinductionComplex R k I)).mapIso
      (((CochainComplex.singleFunctor (ModuleCat.{u} k) 0).mapIso
        (fieldResidueModuleIso k)).op) ≪≫
    regularSingleComplexIso (residueCoinductionComplex R k I)

/-- The comparison retains the original source-precomposition and evaluation maps. -/
theorem residueDualCoinductionComplexIso_hom
    (I : InjectiveResolution (ModuleCat.of R R)) :
    (residueDualCoinductionComplexIso R k I).hom =
      precomp k ((CochainComplex.singleFunctor (ModuleCat.{u} k) 0).map
        (fieldResidueModuleIso k).hom) (residueCoinductionComplex R k I) ≫
      (regularSingleComplexIso (residueCoinductionComplex R k I)).hom := rfl

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{z} (ModuleCat.{u} k)]

/-- The installed right-derived coinduction at the original ring single. -/
abbrev derivedResidueCoinduction : DerivedCategory.Plus (ModuleCat.{u} k) :=
  (ModuleCat.coextendScalars (algebraMap R k)).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))

/-- The intrinsic residue coefficient line is the installed object's native homology. -/
abbrev derivedResidueCoefficientLine : ModuleCat.{u} k :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) 2).obj
    (derivedResidueCoinduction R k)

/-- Every supplied actual injective resolution models this same installed object. -/
def derivedResidueResolutionIso (I : InjectiveResolution (ModuleCat.of R R)) :
    DerivedCategory.Plus.Q.obj
        ((ModuleCat.coextendScalars (algebraMap R k)).mapCochainComplexPlus.obj
          I.cochainComplexPlus) ≅ derivedResidueCoinduction R k :=
  I.rightDerivedFunctorPlusIso (ModuleCat.coextendScalars (algebraMap R k))

/-- The model comparison is the installed unit followed by the inverse
of the image of the original resolution inclusion. -/
theorem derivedResidueResolutionIso_hom (I : InjectiveResolution (ModuleCat.of R R)) :
    (derivedResidueResolutionIso R k I).hom =
      (ModuleCat.coextendScalars (algebraMap R k)).rightDerivedFunctorPlusUnit.app
          I.cochainComplexPlus ≫
        inv ((ModuleCat.coextendScalars (algebraMap R k)).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map I.ιPlus)) :=
  I.rightDerivedFunctorPlusIso_hom (ModuleCat.coextendScalars (algebraMap R k))

/-- The original augmentation square identifies the model with the installed derived unit. -/
@[reassoc]
theorem derivedResidueResolutionIso_unit (I : InjectiveResolution (ModuleCat.of R R)) :
    DerivedCategory.Plus.Q.map
        ((ModuleCat.coextendScalars (algebraMap R k)).mapCochainComplexPlus.map I.ιPlus) ≫
      (derivedResidueResolutionIso R k I).hom =
        (ModuleCat.coextendScalars (algebraMap R k)).rightDerivedFunctorPlusUnit.app
          ((CochainComplex.singleFunctorPlus (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) :=
  I.rightDerivedFunctorPlusIso_unit (ModuleCat.coextendScalars (algebraMap R k))

/-- Native homology of the installed object compares with the original
residue-dual homology through field-linear model and chain isomorphisms. -/
def derivedResidueHomologyIso (I : InjectiveResolution (ModuleCat.of R R)) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) n).obj
        (derivedResidueCoinduction R k) ≅
      residueDualHomology (A := k) I.cochainComplex n :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) n).mapIso
      (derivedResidueResolutionIso R k I).symm ≪≫
    (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} k) n).app
      ((ModuleCat.coextendScalars (algebraMap R k)).mapCochainComplexPlus.obj
        I.cochainComplexPlus) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (.up ℤ) n).mapIso
      (residueDualCoinductionComplexIso R k I).symm

/-- The homology comparison respects the original field action on both sides. -/
theorem derivedResidueHomologyIso_smul
    (I : InjectiveResolution (ModuleCat.of R R)) (n : ℤ) (a : k)
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) n).obj
      (derivedResidueCoinduction R k)) :
    (derivedResidueHomologyIso R k I n).hom (a • x) =
      a • (derivedResidueHomologyIso R k I n).hom x :=
  (derivedResidueHomologyIso R k I n).hom.hom.map_smul a x

section Surface

variable [IsRegularLocalRing R] [IsLocalHom (algebraMap R k)] [Module.Finite R k]

/-- Installed derived residue coinduction has no homology outside degree two. -/
theorem derivedResidueCoinduction_homology_isZero (hd : ringKrullDim R = (2 : ℕ))
    (n : ℤ) (hn : n ≠ 2) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) n).obj
      (derivedResidueCoinduction R k)) := by
  let I := injectiveResolution (ModuleCat.of R R)
  let : I.cochainComplex.IsKInjective := CochainComplex.isKInjective_of_injective _ 0
  exact (residueDualHomology_isZero_of_ne_two (A := k) hd I.cochainComplex I.ι' n hn).of_iso
    (derivedResidueHomologyIso R k I n)

/-- The installed object's original degree-two field module has length one. -/
theorem derivedResidueCoefficientLine_length (hd : ringKrullDim R = (2 : ℕ)) :
    Module.length k (derivedResidueCoefficientLine R k) = 1 := by
  let I := injectiveResolution (ModuleCat.of R R)
  let : I.cochainComplex.IsKInjective := CochainComplex.isKInjective_of_injective _ 0
  calc
    Module.length k (derivedResidueCoefficientLine R k) =
        Module.length k (residueDualHomology (A := k) I.cochainComplex 2) :=
      (derivedResidueHomologyIso R k I 2).toLinearEquiv.length_eq
    _ = 1 := residueDualHomology_length_eq_one (A := k) hd I.cochainComplex I.ι'

/-- Finite generation is a consequence of the original field-module length. -/
theorem derivedResidueCoefficientLine_finite (hd : ringKrullDim R = (2 : ℕ)) :
    Module.Finite k (derivedResidueCoefficientLine R k) := by
  let : IsSimpleModule k (derivedResidueCoefficientLine R k) :=
    Module.length_eq_one_iff.mp (derivedResidueCoefficientLine_length R k hd)
  infer_instance

/-- The intrinsic coefficient line is finitely presented over the field. -/
theorem derivedResidueCoefficientLine_finitePresentation (hd : ringKrullDim R = (2 : ℕ)) :
    Module.FinitePresentation k (derivedResidueCoefficientLine R k) := by
  let := derivedResidueCoefficientLine_finite R k hd
  exact Module.finitePresentation_of_finite k (derivedResidueCoefficientLine R k)

/-- The actual residue coefficient module has field dimension one; no basis is selected. -/
theorem derivedResidueCoefficientLine_finrank (hd : ringKrullDim R = (2 : ℕ)) :
    Module.finrank k (derivedResidueCoefficientLine R k) = 1 := by
  let := derivedResidueCoefficientLine_finite R k hd
  have h := derivedResidueCoefficientLine_length R k hd
  rw [Module.length_eq_finrank] at h
  exact_mod_cast h

/-- The installed derived object has the lower bound given by its original homology. -/
theorem derivedResidueCoinduction_isGE (hd : ringKrullDim R = (2 : ℕ)) :
    (derivedResidueCoinduction R k).IsGE 2 := by
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
  intro n hn
  exact derivedResidueCoinduction_homology_isZero R k hd n (ne_of_lt hn)

/-- The installed derived object has the upper bound given by its original homology. -/
theorem derivedResidueCoinduction_isLE (hd : ringKrullDim R = (2 : ℕ)) :
    (derivedResidueCoinduction R k).IsLE 2 := by
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff, DerivedCategory.isLE_iff]
  intro n hn
  exact derivedResidueCoinduction_homology_isZero R k hd n (ne_of_gt hn)

/-- The installed residue coinduction is its intrinsic coefficient line in degree two,
through the original homology-normalized single comparison. -/
def derivedResidueCoinductionSingleIso (hd : ringKrullDim R = (2 : ℕ)) :
    derivedResidueCoinduction R k ≅
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) 2).obj
        (derivedResidueCoefficientLine R k) := by
  let := derivedResidueCoinduction_isGE R k hd
  let := derivedResidueCoinduction_isLE R k hd
  exact DerivedCategory.Plus.isoSingleHomology (derivedResidueCoinduction R k) 2

/-- The canonical comparison induces the identity on the installed degree-two homology. -/
theorem derivedResidueCoinductionSingleIso_homology (hd : ringKrullDim R = (2 : ℕ)) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) 2).map
        (derivedResidueCoinductionSingleIso R k hd).hom ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
        (C := ModuleCat.{u} k) 2).hom.app (derivedResidueCoefficientLine R k) = 𝟙 _ := by
  let := derivedResidueCoinduction_isGE R k hd
  let := derivedResidueCoinduction_isLE R k hd
  change (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 2).map
    ((DerivedCategory.Plus.ι : _ ⥤ DerivedCategory (ModuleCat.{u} k)).map
      (DerivedCategory.Plus.isoSingleHomology (derivedResidueCoinduction R k) 2).hom) ≫ _ = _
  rw [DerivedCategory.Plus.ι_map_isoSingleHomology_hom]
  exact DerivedCategory.isoSingleHomology_homology _ 2

end Surface

end ModuleCat
