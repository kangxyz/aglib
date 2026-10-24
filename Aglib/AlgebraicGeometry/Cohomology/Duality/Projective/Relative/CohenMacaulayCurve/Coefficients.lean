/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Noetherian
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Tensor
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Residue.Coinduction
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Intrinsic line coefficients in curve concentration

The ambient coefficient is the original relative top differential coefficient
functor evaluated at the actual tilde module of the supplied field module.
Its closed right adjoint and canonical module are the original derived object
and its own degree-`n - 1` homology. Coherence uses finite presentations of the
actual tensor factors. A private field-linear identification with the unit
coefficient is used only to detect vanishing.

The source may be nonreduced and non-Gorenstein. At each closed point the
hypothesis is an actual regular element of the maximal ideal whose principal
ideal has maximal radical. No normality, separability, smoothness, orientation
of the coefficient line, or canonical tensor comparison is assumed.
-/

@[expose] public noncomputable section

universe u w z

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace IsLocalRing
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The standard derived-category model for module sheaves on the given scheme. -/
local instance cmCurveCoefficientsHasDerivedCategoryModules (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

private theorem finitePresentation_tensor_of_locallyNoetherian
    {X : Scheme.{u}} [IsLocallyNoetherian X] (M N : X.Modules)
    [M.IsFinitePresentation] [N.IsFinitePresentation] :
    ((moduleTensorLeftFunctor X M).obj N).IsFinitePresentation := by
  apply QuasiCoherent.affineLocallyFiniteType_finitePresentation
  intro A j _
  let : IsLocallyNoetherian (Spec A) := isLocallyNoetherian_of_isOpenImmersion j
  let : IsNoetherianRing A := isLocallyNoetherian_Spec.mp inferInstance
  let M' := M.restrict j
  let N' := N.restrict j
  have : M'.IsFinitePresentation := finitePresentation_restrict j M
  have : N'.IsFinitePresentation := finitePresentation_restrict j N
  let P := moduleSpecΓFunctor.obj M'
  let Q := moduleSpecΓFunctor.obj N'
  have : Module.Finite A P := finite_globalSections_of_finitePresentation A M'
  have : Module.Finite A Q := finite_globalSections_of_finitePresentation A N'
  let T : ModuleCat.{u} A := ModuleCat.of A (TensorProduct A P Q)
  have : Module.Finite A T :=
    inferInstanceAs (Module.Finite A (TensorProduct A P Q))
  have : (tilde T).IsFinitePresentation := finitePresentation_tilde A T
  let e : (moduleTensorLeftFunctor (Spec A) M').obj N' ≅ tilde T :=
    tensorSheafIso (Spec A) (asIso M'.fromTildeΓ).symm
        (asIso N'.fromTildeΓ).symm ≪≫ tildeTensorIso P Q
  have h : QuasiCoherent.affineFiniteSheaf A (tilde T) :=
    ⟨inferInstance, finite_globalSections_of_finitePresentation A _⟩
  exact (QuasiCoherent.affineFiniteSheaf A).prop_of_iso
    ((tensorRestrictionIso j M N).symm ≪≫ e).symm h

variable (k : Type u) [Field k] (ι : Type u)

/-- The original relative coefficient functor evaluated at the actual tilde module. -/
abbrev cmCurveCoefficientAmbient (n : ℕ) (V : ModuleCat.{u} k) :
    (ProjectiveSpace k ι).Modules :=
  (relativeTopDifferentialCoefficientsFunctor (toSpec k ι) n).obj (tilde V)

/-- The original chosen-embedding right adjoint with its actual line coefficient. -/
abbrev cmCurveCoefficientDualizingObject {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j] (n : ℕ)
    (V : ModuleCat.{u} k) : DerivedCategory.Plus C.Modules :=
  (derivedClosedImmersionRightAdjointPlus j).obj
    ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace k ι).Modules 0).obj
      (cmCurveCoefficientAmbient k ι n V))

/-- Native homology of the same original coefficient-valued derived object. -/
abbrev cmCurveCoefficientHomology {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j] (n : ℕ)
    (V : ModuleCat.{u} k) (q : ℤ) : C.Modules :=
  derivedClosedImmersionRightAdjointHomology j (cmCurveCoefficientAmbient k ι n V) q

/-- The coefficient-valued canonical module is its own native homology. -/
abbrev cmCurveCoefficientCanonicalModule {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j] (n : ℕ)
    (V : ModuleCat.{u} k) : C.Modules :=
  cmCurveCoefficientHomology k ι j n V ((n : ℤ) - 1)

/-- Coherence of the actual ambient coefficient needs only finiteness of `V`. -/
theorem cmCurveCoefficientAmbient_finitePresentation
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (V : ModuleCat.{u} k) [Module.Finite k V] :
    (cmCurveCoefficientAmbient k ι n V).IsFinitePresentation := by
  let : Finite ι := Finite.of_equiv _ e.symm
  have : (tilde (R := CommRingCat.of k) V).IsFinitePresentation :=
    finitePresentation_tilde (.of k) V
  have : IsFiniteLocallyFree (ProjectiveSpace k ι)
      (moduleExteriorPower (ProjectiveSpace k ι) (relativeDifferentialSheaf (toSpec k ι)) n) :=
    moduleExteriorTop_isFiniteLocallyFree _ _ n (projectiveDifferential_hasRank k ι n e)
  exact finitePresentation_tensor_of_locallyNoetherian _ _

/-- All original homology sheaves are coherent before imposing concentration. -/
theorem cmCurveCoefficientHomology_finitePresentation {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (V : ModuleCat.{u} k) [Module.Finite k V]
    (q : ℤ) : (cmCurveCoefficientHomology k ι j n V q).IsFinitePresentation := by
  let : Finite ι := Finite.of_equiv _ e.symm
  have := cmCurveCoefficientAmbient_finitePresentation k ι n e V
  exact derivedClosedImmersionRightAdjointHomology_finitePresentation j _ q

/-- The actual canonical homology is coherent for every finite field coefficient. -/
theorem cmCurveCoefficientCanonicalModule_finitePresentation {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (V : ModuleCat.{u} k) [Module.Finite k V] :
    (cmCurveCoefficientCanonicalModule k ι j n V).IsFinitePresentation :=
  cmCurveCoefficientHomology_finitePresentation k ι j n e V ((n : ℤ) - 1)

section Concentration

variable {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
  (n : ℕ) (e : ι ≃ Fin (n + 1)) (V : ModuleCat.{u} k) [Module.Finite k V]
  (hV : Module.finrank k V = 1)
  (hCM : ∀ x : C, IsClosed ({x} : Set C) →
    ∃ b ∈ maximalIdeal (C.presheaf.stalk x), IsSMulRegular (C.presheaf.stalk x) b ∧
      (Ideal.span {b}).radical = maximalIdeal (C.presheaf.stalk x))

include e hV hCM

/-- All-integer concentration for the original line coefficient. The auxiliary
field-linear identification is confined to this vanishing proof. -/
theorem cmCurveCoefficientHomology_isZero (q : ℤ) (hq : q ≠ (n : ℤ) - 1) :
    IsZero (cmCurveCoefficientHomology k ι j n V q) := by
  obtain ⟨v⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (R := k) (M := V) (M' := k) (by simpa using hV)
  let eV : tilde V ≅ SheafOfModules.unit (Spec (.of k)).ringCatSheaf :=
    (tilde.functor (.of k)).mapIso v.toModuleIso ≪≫ tildeSelf
  let eK : cmCurveCoefficientDualizingObject k ι j n V ≅
      cmCurveDualizingObject k ι j n :=
    (derivedClosedImmersionRightAdjointPlus j).mapIso
      ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace k ι).Modules 0).mapIso
        ((relativeTopDifferentialCoefficientsFunctor (toSpec k ι) n).mapIso eV))
  exact (cmCurveHomology_isZero k ι j n e hCM q hq).of_iso
    ((DerivedCategory.Plus.homologyFunctor C.Modules q).mapIso eK)

/-- The lower bound belongs to the original coefficient-valued object. -/
theorem cmCurveCoefficientDualizingObject_isGE :
    (cmCurveCoefficientDualizingObject k ι j n V).IsGE ((n : ℤ) - 1) := by
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
  intro q hq
  exact cmCurveCoefficientHomology_isZero k ι j n e V hV hCM q (ne_of_lt hq)

/-- The upper bound belongs to the original coefficient-valued object. -/
theorem cmCurveCoefficientDualizingObject_isLE :
    (cmCurveCoefficientDualizingObject k ι j n V).IsLE ((n : ℤ) - 1) := by
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff, DerivedCategory.isLE_iff]
  intro q hq
  exact cmCurveCoefficientHomology_isZero k ι j n e V hV hCM q (ne_of_gt hq)

/-- Reconstruction uses the object's own homology and the installed canonical
single-homology isomorphism, without choosing an orientation of `V`. -/
def cmCurveCoefficientCanonicalIso :
    cmCurveCoefficientDualizingObject k ι j n V ≅
      (DerivedCategory.Plus.singleFunctor C.Modules ((n : ℤ) - 1)).obj
        (cmCurveCoefficientCanonicalModule k ι j n V) := by
  let := cmCurveCoefficientDualizingObject_isGE k ι j n e V hV hCM
  let := cmCurveCoefficientDualizingObject_isLE k ι j n e V hV hCM
  exact DerivedCategory.Plus.isoSingleHomology
    (cmCurveCoefficientDualizingObject k ι j n V) ((n : ℤ) - 1)

/-- The canonical reconstruction induces the identity on its original homology. -/
theorem cmCurveCoefficientCanonicalIso_homology :
    (DerivedCategory.Plus.homologyFunctor C.Modules ((n : ℤ) - 1)).map
        (cmCurveCoefficientCanonicalIso k ι j n e V hV hCM).hom ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
        (C := C.Modules) ((n : ℤ) - 1)).hom.app
          (cmCurveCoefficientCanonicalModule k ι j n V) = 𝟙 _ := by
  let := cmCurveCoefficientDualizingObject_isGE k ι j n e V hV hCM
  let := cmCurveCoefficientDualizingObject_isLE k ι j n e V hV hCM
  change (DerivedCategory.homologyFunctor C.Modules ((n : ℤ) - 1)).map
    ((DerivedCategory.Plus.ι : _ ⥤ DerivedCategory C.Modules).map
      (DerivedCategory.Plus.isoSingleHomology
        (cmCurveCoefficientDualizingObject k ι j n V) ((n : ℤ) - 1)).hom) ≫ _ = _
  rw [DerivedCategory.Plus.ι_map_isoSingleHomology_hom]
  exact DerivedCategory.isoSingleHomology_homology _ ((n : ℤ) - 1)

end Concentration

section Residue

variable (R : Type u) [CommRing R] [Algebra R k]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{z} (ModuleCat.{u} k)]
  [IsRegularLocalRing R] [IsLocalHom (algebraMap R k)] [Module.Finite R k]

/-- The installed residue coefficient line enters the same family directly,
with its original field action and no field-linear orientation. -/
def cmCurveDerivedResidueCoefficientCanonicalIso
    (hd : ringKrullDim R = (2 : ℕ)) {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ maximalIdeal (C.presheaf.stalk x), IsSMulRegular (C.presheaf.stalk x) b ∧
        (Ideal.span {b}).radical = maximalIdeal (C.presheaf.stalk x)) :
    cmCurveCoefficientDualizingObject k ι j n (ModuleCat.derivedResidueCoefficientLine R k) ≅
      (DerivedCategory.Plus.singleFunctor C.Modules ((n : ℤ) - 1)).obj
        (cmCurveCoefficientCanonicalModule k ι j n
          (ModuleCat.derivedResidueCoefficientLine R k)) := by
  let := ModuleCat.derivedResidueCoefficientLine_finite R k hd
  exact cmCurveCoefficientCanonicalIso k ι j n e
    (ModuleCat.derivedResidueCoefficientLine R k)
    (ModuleCat.derivedResidueCoefficientLine_finrank R k hd) hCM

/-- The specialization to the intrinsic residue line retains the same identity
normalization on its own canonical homology. -/
theorem cmCurveDerivedResidueCoefficientCanonicalIso_homology
    (hd : ringKrullDim R = (2 : ℕ)) {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ maximalIdeal (C.presheaf.stalk x), IsSMulRegular (C.presheaf.stalk x) b ∧
        (Ideal.span {b}).radical = maximalIdeal (C.presheaf.stalk x)) :
    (DerivedCategory.Plus.homologyFunctor C.Modules ((n : ℤ) - 1)).map
        (cmCurveDerivedResidueCoefficientCanonicalIso k ι R hd j n e hCM).hom ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
        (C := C.Modules) ((n : ℤ) - 1)).hom.app
          (cmCurveCoefficientCanonicalModule k ι j n
            (ModuleCat.derivedResidueCoefficientLine R k)) = 𝟙 _ := by
  let := ModuleCat.derivedResidueCoefficientLine_finite R k hd
  exact cmCurveCoefficientCanonicalIso_homology k ι j n e
    (ModuleCat.derivedResidueCoefficientLine R k)
    (ModuleCat.derivedResidueCoefficientLine_finrank R k hd) hCM

end Residue

end AlgebraicGeometry.Scheme.Cohomology
