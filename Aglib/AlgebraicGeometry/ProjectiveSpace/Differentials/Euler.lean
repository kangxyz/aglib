/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.RingTheory.MvPolynomial.DegreeOne
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure
public import Aglib.AlgebraicGeometry.ProjectiveSpace.GlobalGeneration
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Isomorphism
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Unit
public import Aglib.AlgebraicGeometry.Modules.Pullback.Free
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Free
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Free.Sections
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Restriction
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Affine
public import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Actual coordinate arrows for the projective Euler sequence

Use the actual polynomial projective space, its original structure map,
the actual inverse twist, the actual pullback of the homogeneous degree-one
module, and the original unit module. The augmentation is original
coordinate evaluation followed by original twist multiplication. Its
coordinate formula, epimorphism, and the prescribed original chart-kernel
vectors are proved without an exactness supplier.

The coordinate formula is that of Stacks Project Lemma 50.11.1, Tag 0FMG.
The source omits verification of exactness; the augmentation and
kernel-vector equations here are checked directly. The native polynomial
chart frame of the actual relative differential sheaf also retains every
original principal-open differential value. The resulting original chart
Euler differential arrows have their prescribed section formula and zero
composite with the original augmentation. Global gluing, injectivity, and
short exactness remain separate obligations.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace
variable (R : Type u) [CommRing R] (ι : Type u)

/-- The actual degree-one homogeneous polynomial coefficient module. -/
def eulerDegreeOneModule : ModuleCat (CommRingCat.of R) :=
  ModuleCat.of R (MvPolynomial.homogeneousSubmodule ι R 1)

/-- The actual pullback of the degree-one coefficient module to polynomial projective space. -/
def eulerCoefficientSheaf : (ProjectiveSpace R ι).Modules :=
  (Scheme.Modules.pullback (toSpec R ι)).obj (tilde (eulerDegreeOneModule R ι))

/-- The original degree-one coordinate basis induces the native pulled-back free comparison. -/
def eulerCoefficientIsoFree : eulerCoefficientSheaf R ι ≅
    SheafOfModules.free (R := (ProjectiveSpace R ι).ringCatSheaf) ι :=
  (Scheme.Modules.pullback (toSpec R ι)).mapIso
    (Scheme.Modules.tildeBasisIso (eulerDegreeOneModule R ι)
      (MvPolynomial.homogeneousDegreeOneBasis R ι)) ≪≫
    Scheme.Modules.pullbackFreeIso (toSpec R ι) ι

/-- The original pulled-back coordinate generator, as a compatible section family. -/
def eulerCoefficientSection (j : ι) : (eulerCoefficientSheaf R ι).sections :=
  SheafOfModules.sectionsMap (eulerCoefficientIsoFree R ι).inv
    (SheafOfModules.freeSection j)

/-- Evaluation sends the original degree-one generators to their actual homogeneous sections. -/
def eulerEvaluation : eulerCoefficientSheaf R ι ⟶ twistingSheaf R ι 1 :=
  (eulerCoefficientIsoFree R ι).hom ≫ coordinatePowerGeneratingMap R ι 1

/-- The actual Euler middle sheaf, retaining the degree-one module and tensor orientation. -/
def eulerMiddle : (ProjectiveSpace R ι).Modules :=
  (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (-1))).obj
    (eulerCoefficientSheaf R ι)

/-- The Euler augmentation uses original coordinate evaluation and twist multiplication. -/
def eulerAugmentation : eulerMiddle R ι ⟶
    SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf :=
  (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (-1))).map
      (eulerEvaluation R ι) ≫
    (twistingTensorIso R ι (-1) 1).hom ≫ (twistingZeroIso R ι).hom

/-- The original ratio `X_j / X_i` on every displayed coordinate subopen. -/
def eulerCoordinateRatio (i j : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) : Γ(ProjectiveSpace R ι, V) :=
  twistingSectionsEquiv R ι 1 i hi
    ((homogeneousSectionFamily R ι 1 (coordinatePower R ι 1 j)).val (op V))

@[simp]
theorem eulerCoordinateRatio_self (i : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) : eulerCoordinateRatio R ι i i hi = 1 :=
  homogeneousSectionFamily_coordinatePower_local R ι 1 i hi

/-- The pure tensor of the original inverse coordinate frame and pulled-back generator. -/
def eulerMiddleGenerator (i j : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) : Γ(eulerMiddle R ι, V) :=
  moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι (-1))
    (eulerCoefficientSheaf R ι) V (twistingGenerator R ι (-1) i hi)
      ((eulerCoefficientSection R ι j).val (op V))

/-- Original coordinate evaluation retains the original global polynomial section. -/
theorem eulerEvaluation_coordinateSection (j : ι) (V : (ProjectiveSpace R ι).Opens) :
    (eulerEvaluation R ι).val.app (op V) ((eulerCoefficientSection R ι j).val (op V)) =
      (homogeneousSectionFamily R ι 1 (coordinatePower R ι 1 j)).val (op V) := by
  change (coordinatePowerGeneratingMap R ι 1).val.app (op V)
    ((eulerCoefficientIsoFree R ι).hom.val.app (op V)
      ((eulerCoefficientIsoFree R ι).inv.val.app (op V)
        ((SheafOfModules.freeSection j).val (op V)))) = _
  have h := congrArg (fun k => k.val.app (op V)
    ((SheafOfModules.freeSection (R := (ProjectiveSpace R ι).ringCatSheaf) j).val (op V)))
      (eulerCoefficientIsoFree R ι).inv_hom_id
  exact (congrArg ((coordinatePowerGeneratingMap R ι 1).val.app (op V)) h).trans
    (coordinatePowerGeneratingMap_freeSection R ι 1 j V)

/-- The augmentation has the original chart formula `(1/X_i) dX_j ↦ X_j/X_i`. -/
theorem eulerAugmentation_generator (i j : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) :
    (eulerAugmentation R ι).val.app (op V) (eulerMiddleGenerator R ι i j hi) =
      eulerCoordinateRatio R ι i j hi := by
  change (twistingZeroToUnit R ι).val.app (op V)
    ((twistingTensorMap R ι (-1) 1).val.app (op V)
      (((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (-1))).map
        (eulerEvaluation R ι)).val.app (op V)
          (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι (-1))
            (eulerCoefficientSheaf R ι) V (twistingGenerator R ι (-1) i hi)
              ((eulerCoefficientSection R ι j).val (op V))))) = _
  have hmap := moduleTensorLeftFunctor_map_section
    (twistingSheaf R ι (-1)) (eulerEvaluation R ι) V
    (twistingGenerator R ι (-1) i hi) ((eulerCoefficientSection R ι j).val (op V))
  rw [show (((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (-1))).map
      (eulerEvaluation R ι)).val.app (op V)
        (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι (-1))
          (eulerCoefficientSheaf R ι) V (twistingGenerator R ι (-1) i hi)
            ((eulerCoefficientSection R ι j).val (op V)))) = _ from hmap]
  have hev : (eulerEvaluation R ι).app V
      ((eulerCoefficientSection R ι j).val (op V)) =
        (homogeneousSectionFamily R ι 1 (coordinatePower R ι 1 j)).val (op V) :=
    eulerEvaluation_coordinateSection R ι j V
  rw [hev]
  rw [twistingTensorMap_section, twistingZeroToUnit_app R ι i hi]
  have hmul := twistingSectionsEquiv_mul R ι (-1) 1 i hi
    (twistingGenerator R ι (-1) i hi)
      ((homogeneousSectionFamily R ι 1 (coordinatePower R ι 1 j)).val (op V))
  rw [twistingSectionsEquiv_generator, one_mul] at hmul
  exact hmul

/-- The actual Euler augmentation is locally split onto the original unit. -/
theorem eulerAugmentation_epi : Epi (eulerAugmentation R ι) := by
  let : (SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).ReflectsEpimorphisms :=
    Functor.reflectsEpimorphisms_of_faithful _
  apply (SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).epi_of_epi_map
  suffices h : Sheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
        (eulerAugmentation R ι)) by
    let := h
    infer_instance
  apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
  intro V s x hxV
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ iSup (coordinateOpen R ι) by rw [iSup_coordinateOpen_eq_top]; trivial)
  let W := V ⊓ coordinateOpen R ι i
  let a : Γ(ProjectiveSpace R ι, W) :=
    (SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf).val.map
      (homOfLE inf_le_left).op s
  refine ⟨W, inf_le_left, ?_, hxV, hi⟩
  refine ⟨a • eulerMiddleGenerator R ι i i (V := W) inf_le_right, ?_⟩
  change (eulerAugmentation R ι).val.app (op W)
    (a • eulerMiddleGenerator R ι i i inf_le_right) = a
  rw [((eulerAugmentation R ι).val.app (op W)).hom.map_smul,
    eulerAugmentation_generator, eulerCoordinateRatio_self, smul_eq_mul, mul_one]


/-- The original local kernel vector prescribed by the projective Euler formula. -/
def eulerKernelGenerator (i j : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) : Γ(eulerMiddle R ι, V) :=
  eulerMiddleGenerator R ι i j hi -
    eulerCoordinateRatio R ι i j hi • eulerMiddleGenerator R ι i i hi

/-- Every prescribed original Euler differential value lies in the actual augmentation kernel. -/
theorem eulerAugmentation_kernelGenerator (i j : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) :
    (eulerAugmentation R ι).val.app (op V) (eulerKernelGenerator R ι i j hi) = 0 := by
  change (eulerAugmentation R ι).val.app (op V)
    (eulerMiddleGenerator R ι i j hi -
      eulerCoordinateRatio R ι i j hi • eulerMiddleGenerator R ι i i hi) = 0
  rw [((eulerAugmentation R ι).val.app (op V)).hom.map_sub,
    ((eulerAugmentation R ι).val.app (op V)).hom.map_smul,
    eulerAugmentation_generator, eulerAugmentation_generator, eulerCoordinateRatio_self,
    smul_eq_mul, mul_one, sub_self]


/-- The chart coefficient of the original homogeneous section is the original fraction. -/
theorem eulerCoordinateRatio_eq_fraction (i j : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) :
    eulerCoordinateRatio R ι i j hi =
      sectionRestrict (ProjectiveSpace R ι) hi
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i)
          (coordinateRatio R ι i j)) := by
  let s := homogeneousSectionFamily R ι 1 (coordinatePower R ι 1 j)
  have hn := s.property (homOfLE hi).op
  have hf : homogeneousChartFraction R ι 1 (coordinatePower R ι 1 j) i =
      coordinateRatio R ι i j := by
    simp only [homogeneousChartFraction, coordinatePower, pow_one, coordinateRatio]
  have hp : twistingSectionsEquiv R ι 1 i le_rfl (s.val (op (coordinateOpen R ι i))) =
      Proj.awayToSection (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i)
        (coordinateRatio R ι i j) :=
    (homogeneousSection_local R ι 1 (coordinatePower R ι 1 j) i).trans
      (congrArg (Proj.awayToSection (MvPolynomial.homogeneousSubmodule ι R)
        (MvPolynomial.X i)) hf)
  change twistingSectionsEquiv R ι 1 i hi (s.val (op V)) = _
  exact (congrArg (twistingSectionsEquiv R ι 1 i hi) hn).symm.trans
    ((twistingSectionsEquiv_restrict R ι 1 i hi le_rfl _).trans
      (congrArg (sectionRestrict (ProjectiveSpace R ι) hi) hp))

/-- The actual polynomial spectrum chart, using the original coordinate-open isomorphism. -/
abbrev eulerPolynomialChart (i : ι) :
    Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R)) ⟶ ProjectiveSpace R ι :=
  (coordinateOpenIsoSpecPolynomial R ι i).inv ≫ (coordinateOpen R ι i).ι

/-- The original polynomial chart preserves the original coefficient-ring structure map. -/
theorem eulerPolynomialChart_toSpec (i : ι) :
    eulerPolynomialChart R ι i ≫ toSpec R ι =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : R →+* MvPolynomial {j : ι // j ≠ i} R)) := by
  change Spec.map (CommRingCat.ofHom (coordinateRingToPolynomial R ι i)) ≫
    (Proj.awayι (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one) ≫ toSpec R ι = _
  rw [coordinateChart_toSpec, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact coordinateRingToPolynomial_coefficient R ι i r

/-- Original relative differentials restricted to a native polynomial chart are the actual
polynomial Kähler module sheaf, through the proved original open-square comparison. -/
def eulerPolynomialOmegaTildeIso (i : ι) :
    (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)).restrict
        (eulerPolynomialChart R ι i) ≅
      tilde (CommRingCat.KaehlerDifferential (CommRingCat.ofHom
        (MvPolynomial.C : R →+* MvPolynomial {j : ι // j ≠ i} R))) :=
  Scheme.Modules.Differentials.relativeDifferentialOpenSquareIso (toSpec R ι)
    (eulerPolynomialChart R ι i)
    (Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : R →+* MvPolynomial {j : ι // j ≠ i} R))) (𝟙 _)
      (by simpa only [Category.comp_id] using eulerPolynomialChart_toSpec R ι i) ≪≫
    Scheme.Modules.Differentials.relativeDifferentialAffineIso _

/-- A native polynomial frame of the actual relative differential sheaf, with its original
principal-open differential values retained in the same construction. -/
def eulerPolynomialOmegaFrame (i : ι) :
    let S : CommRingCat.{u} := CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R)
    {e : (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)).restrict
        (eulerPolynomialChart R ι i) ≅
      SheafOfModules.free (R := (Spec S).ringCatSheaf) {j : ι // j ≠ i} //
      ∀ (r : S) (j : {j : ι // j ≠ i}),
        let U := PrimeSpectrum.basicOpen r
        e.hom.val.app (op U)
          ((Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
            (((eulerPolynomialChart R ι i).appIso U).inv
              (((Scheme.ΓSpecIso S).inv ≫ (Spec S).presheaf.map U.leTop.op)
                (MvPolynomial.X j)))) =
          (SheafOfModules.freeSection (R := (Spec S).ringCatSheaf) j).val (op U)} := by
  let P := MvPolynomial {j : ι // j ≠ i} R
  let S : CommRingCat.{u} := CommRingCat.of P
  let σ : CommRingCat.of R ⟶ S := CommRingCat.ofHom MvPolynomial.C
  let B (a : Algebra R P) : Type u :=
    letI := a
    {b : Module.Basis {j : ι // j ≠ i} P Ω[P⁄R] //
      ∀ j, b j = KaehlerDifferential.D R P (MvPolynomial.X j)}
  have hA : (MvPolynomial.C : R →+* P).toAlgebra = (inferInstance : Algebra R P) :=
    toAlgebra_algebraMap
  have hb₀ : B (inferInstance : Algebra R P) :=
    ⟨KaehlerDifferential.mvPolynomialBasis R {j : ι // j ≠ i},
      KaehlerDifferential.mvPolynomialBasis_apply R {j : ι // j ≠ i}⟩
  let b : {b : Module.Basis {j : ι // j ≠ i} P (CommRingCat.KaehlerDifferential σ) //
      ∀ j, b j = CommRingCat.KaehlerDifferential.d (MvPolynomial.X j)} :=
    (congrArg B hA).mpr hb₀
  let e := eulerPolynomialOmegaTildeIso R ι i ≪≫ Scheme.Modules.tildeBasisIso _ b.val
  refine ⟨e, ?_⟩
  intro r j
  let U := PrimeSpectrum.basicOpen (R := S) r
  let a : Γ(Spec S, U) :=
    ((Scheme.ΓSpecIso S).inv ≫ (Spec S).presheaf.map U.leTop.op) (MvPolynomial.X j)
  have hsq : eulerPolynomialChart R ι i ≫ toSpec R ι = Spec.map σ ≫ 𝟙 _ := by
    simpa only [Category.comp_id] using eulerPolynomialChart_toSpec R ι i
  let sq := Scheme.Modules.Differentials.relativeDifferentialOpenSquareIso (toSpec R ι)
    (eulerPolynomialChart R ι i) (Spec.map σ) (𝟙 _) hsq
  have hs : sq.hom.val.app (op U)
      ((Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
        (((eulerPolynomialChart R ι i).appIso U).inv a)) =
      (Scheme.Modules.Differentials.relativeDifferentialDerivation (Spec.map σ)).d a :=
    (Scheme.Modules.Differentials.relativeDifferentialOpenSquareIso_hom_d (toSpec R ι)
      (eulerPolynomialChart R ι i) (Spec.map σ) (𝟙 _) hsq U
      (((eulerPolynomialChart R ι i).appIso U).inv a)).trans
      (congrArg (Scheme.Modules.Differentials.relativeDifferentialDerivation (Spec.map σ)).d
        (Iso.inv_hom_id_apply ((eulerPolynomialChart R ι i).appIso U) a))
  have ha : (Scheme.Modules.Differentials.relativeDifferentialAffineIso σ).hom.val.app (op U)
      ((Scheme.Modules.Differentials.relativeDifferentialDerivation (Spec.map σ)).d a) =
      tilde.toOpen (CommRingCat.KaehlerDifferential σ) U
        (CommRingCat.KaehlerDifferential.d (MvPolynomial.X j)) :=
    Scheme.Modules.Differentials.relativeDifferentialAffineIso_hom_d σ r (MvPolynomial.X j)
  have hf := Scheme.Modules.tildeBasisIso_hom_toOpen
    (CommRingCat.KaehlerDifferential σ) b.val j U
  have hf' : (Scheme.Modules.tildeBasisIso (CommRingCat.KaehlerDifferential σ) b.val).hom.val.app
        (op U) (tilde.toOpen (CommRingCat.KaehlerDifferential σ) U
          (CommRingCat.KaehlerDifferential.d (MvPolynomial.X j))) =
      (SheafOfModules.freeSection (R := (Spec S).ringCatSheaf) j).val
        (op U) :=
    (congrArg (fun z =>
      (Scheme.Modules.tildeBasisIso (CommRingCat.KaehlerDifferential σ) b.val).hom.val.app
        (op U) (tilde.toOpen (CommRingCat.KaehlerDifferential σ) U z)) (b.property j)).symm.trans hf
  change (Scheme.Modules.tildeBasisIso (CommRingCat.KaehlerDifferential σ) b.val).hom.val.app
    (op U) ((Scheme.Modules.Differentials.relativeDifferentialAffineIso σ).hom.val.app (op U)
      (sq.hom.val.app (op U)
        ((Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
          (((eulerPolynomialChart R ι i).appIso U).inv a)))) = _
  exact (congrArg (fun z =>
    (Scheme.Modules.tildeBasisIso (CommRingCat.KaehlerDifferential σ) b.val).hom.val.app (op U)
      ((Scheme.Modules.Differentials.relativeDifferentialAffineIso σ).hom.val.app (op U) z))
        hs).trans
    ((congrArg ((Scheme.Modules.tildeBasisIso (CommRingCat.KaehlerDifferential σ) b.val).hom.val.app
      (op U)) ha).trans hf')

/-- The free isomorphism underlying the checked original polynomial differential frame. -/
def eulerPolynomialOmegaFreeIso (i : ι) := (eulerPolynomialOmegaFrame R ι i).val


/-- The constructed polynomial frame sends the original relative differential of every
localized chart coordinate to the corresponding original free section. -/
theorem eulerPolynomialOmegaFreeIso_hom_d (i : ι) :
    let S : CommRingCat.{u} := CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R)
    ∀ (r : S) (j : {j : ι // j ≠ i}),
      let U := PrimeSpectrum.basicOpen r
      (eulerPolynomialOmegaFreeIso R ι i).hom.val.app (op U)
        ((Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
          (((eulerPolynomialChart R ι i).appIso U).inv
            (((Scheme.ΓSpecIso S).inv ≫ (Spec S).presheaf.map U.leTop.op)
              (MvPolynomial.X j)))) =
        (SheafOfModules.freeSection (R := (Spec S).ringCatSheaf) j).val (op U) :=
  (eulerPolynomialOmegaFrame R ι i).property

/-- Original coordinate coefficients commute with original section restriction. -/
theorem eulerCoordinateRatio_restrict (i j : ι)
    {V W : (ProjectiveSpace R ι).Opens} (h : V ≤ W) (hi : W ≤ coordinateOpen R ι i) :
    sectionRestrict (ProjectiveSpace R ι) h (eulerCoordinateRatio R ι i j hi) =
      eulerCoordinateRatio R ι i j (h.trans hi) := by
  let s := homogeneousSectionFamily R ι 1 (coordinatePower R ι 1 j)
  exact (twistingSectionsEquiv_restrict R ι 1 i h hi (s.val (op W))).symm.trans
    (congrArg (twistingSectionsEquiv R ι 1 i (h.trans hi))
      (s.property (homOfLE h).op))

/-- Original Euler middle generators commute with original section restriction. -/
theorem eulerMiddleGenerator_restrict (i j : ι)
    {V W : (ProjectiveSpace R ι).Opens} (h : V ≤ W) (hi : W ≤ coordinateOpen R ι i) :
    (eulerMiddle R ι).val.map (homOfLE h).op (eulerMiddleGenerator R ι i j hi) =
      eulerMiddleGenerator R ι i j (h.trans hi) := by
  exact (moduleTensorSection_restrict (X := ProjectiveSpace R ι)
    (twistingSheaf R ι (-1)) (eulerCoefficientSheaf R ι) (homOfLE h)
    (twistingGenerator R ι (-1) i hi) ((eulerCoefficientSection R ι j).val (op W))).trans
    (congrArg₂ (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι (-1))
      (eulerCoefficientSheaf R ι) V)
      (twistingGenerator_restrict R ι (-1) i h hi)
      ((eulerCoefficientSection R ι j).property (homOfLE h).op))

/-- The prescribed original Euler kernel vectors commute with actual restrictions. -/
theorem eulerKernelGenerator_restrict (i j : ι)
    {V W : (ProjectiveSpace R ι).Opens} (h : V ≤ W) (hi : W ≤ coordinateOpen R ι i) :
    (eulerMiddle R ι).val.map (homOfLE h).op (eulerKernelGenerator R ι i j hi) =
      eulerKernelGenerator R ι i j (h.trans hi) := by
  have hj := eulerMiddleGenerator_restrict R ι i j h hi
  have hii := eulerMiddleGenerator_restrict R ι i i h hi
  have hr : (ProjectiveSpace R ι).presheaf.map (homOfLE h).op
      (eulerCoordinateRatio R ι i j hi) = eulerCoordinateRatio R ι i j (h.trans hi) :=
    eulerCoordinateRatio_restrict R ι i j h hi
  have hs := (eulerMiddle R ι).val.map_smul (homOfLE h).op
    (eulerCoordinateRatio R ι i j hi) (eulerMiddleGenerator R ι i i hi)
  exact (((eulerMiddle R ι).val.map (homOfLE h).op).hom.map_sub _ _).trans
    (congrArg₂ (fun a b : Γ(eulerMiddle R ι, V) => a - b) hj
      (hs.trans (congrArg₂ (fun (r : Γ(ProjectiveSpace R ι, V))
        (s : Γ(eulerMiddle R ι, V)) => r • s) hr hii)))

/-- Every image subopen of the original polynomial chart lies in its original coordinate open. -/
theorem eulerPolynomialChart_image_le (i : ι)
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens) :
    eulerPolynomialChart R ι i ''ᵁ V ≤ coordinateOpen R ι i := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ((coordinateOpenIsoSpecPolynomial R ι i).inv y).property

/-- The original compatible Euler kernel-vector family on a native polynomial chart. -/
def eulerKernelSectionOnPolynomialChart (i : ι) (j : {j : ι // j ≠ i}) :
    ((eulerMiddle R ι).restrict (eulerPolynomialChart R ι i)).sections :=
  _root_.PresheafOfModules.sectionsMk
    (fun V => eulerKernelGenerator R ι i j.val (eulerPolynomialChart_image_le R ι i V.unop))
    (by
      intro V W k
      exact eulerKernelGenerator_restrict R ι i j.val
        ((eulerPolynomialChart R ι i).image_mono k.unop.le)
        (eulerPolynomialChart_image_le R ι i V.unop))

/-- The original free polynomial differential generators map to their prescribed kernel vectors. -/
def eulerKernelFromFreeOnPolynomialChart (i : ι) :
    SheafOfModules.free
      (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf)
      {j : ι // j ≠ i} ⟶ (eulerMiddle R ι).restrict (eulerPolynomialChart R ι i) :=
  ((eulerMiddle R ι).restrict (eulerPolynomialChart R ι i)).freeHomEquiv.symm
    (eulerKernelSectionOnPolynomialChart R ι i)

/-- The original free-section formula of the actual chart kernel-vector morphism. -/
theorem eulerKernelFromFreeOnPolynomialChart_freeSection (i : ι) (j : {j : ι // j ≠ i})
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens) :
    (eulerKernelFromFreeOnPolynomialChart R ι i).val.app (op V)
      ((SheafOfModules.freeSection
        (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf)
        j).val (op V)) =
      eulerKernelGenerator R ι i j.val (eulerPolynomialChart_image_le R ι i V) :=
  congrArg (fun s : ((eulerMiddle R ι).restrict (eulerPolynomialChart R ι i)).sections =>
    s.val (op V))
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (eulerKernelSectionOnPolynomialChart R ι i) j)

/-- The actual relative Euler differential arrow on the original native polynomial chart. -/
def eulerDifferentialOnPolynomialChart (i : ι) :
    (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)).restrict
        (eulerPolynomialChart R ι i) ⟶
      (eulerMiddle R ι).restrict (eulerPolynomialChart R ι i) :=
  (eulerPolynomialOmegaFreeIso R ι i).hom ≫ eulerKernelFromFreeOnPolynomialChart R ι i

/-- The chart differential arrow retains the original relative-d Euler formula. -/
theorem eulerDifferentialOnPolynomialChart_d (i : ι) :
    let S : CommRingCat.{u} := CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R)
    ∀ (r : S) (j : {j : ι // j ≠ i}),
      let U := PrimeSpectrum.basicOpen r
      (eulerDifferentialOnPolynomialChart R ι i).val.app (op U)
        ((Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
          (((eulerPolynomialChart R ι i).appIso U).inv
            (((Scheme.ΓSpecIso S).inv ≫ (Spec S).presheaf.map U.leTop.op)
              (MvPolynomial.X j)))) =
        eulerKernelGenerator R ι i j.val (eulerPolynomialChart_image_le R ι i U) := by
  exact fun r j =>
    (congrArg ((eulerKernelFromFreeOnPolynomialChart R ι i).val.app
      (op (PrimeSpectrum.basicOpen r))) (eulerPolynomialOmegaFreeIso_hom_d R ι i r j)).trans
      (eulerKernelFromFreeOnPolynomialChart_freeSection R ι i j (PrimeSpectrum.basicOpen r))

/-- Original augmentation restricted to the native polynomial chart, with the original unit. -/
def eulerAugmentationOnPolynomialChart (i : ι) :
    (eulerMiddle R ι).restrict (eulerPolynomialChart R ι i) ⟶
      SheafOfModules.unit
        (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf :=
  (Scheme.Modules.restrictFunctor (eulerPolynomialChart R ι i)).map (eulerAugmentation R ι) ≫
    (Scheme.Modules.restrictUnitIso (eulerPolynomialChart R ι i)).hom

/-- The actual native chart kernel-vector map is killed by the restricted original augmentation. -/
theorem eulerKernelFromFreeOnPolynomialChart_comp_augmentation (i : ι) :
    eulerKernelFromFreeOnPolynomialChart R ι i ≫ eulerAugmentationOnPolynomialChart R ι i = 0 := by
  apply (SheafOfModules.freeHomEquiv
    (SheafOfModules.unit
      (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf)).injective
  funext j
  ext V
  change (Scheme.Modules.restrictUnitIso (eulerPolynomialChart R ι i)).hom.val.app V
    ((eulerAugmentation R ι).val.app (op (eulerPolynomialChart R ι i ''ᵁ V.unop))
      ((eulerKernelFromFreeOnPolynomialChart R ι i).val.app V
        ((SheafOfModules.freeSection
          (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf)
          j).val V))) = 0
  rw [eulerKernelFromFreeOnPolynomialChart_freeSection]
  exact (congrArg ((Scheme.Modules.restrictUnitIso (eulerPolynomialChart R ι i)).hom.val.app V)
    (eulerAugmentation_kernelGenerator R ι i j.val
      (eulerPolynomialChart_image_le R ι i V.unop))).trans (map_zero _)

/-- The actual relative Euler arrows form a complex on the original native polynomial chart. -/
theorem eulerDifferentialOnPolynomialChart_comp_augmentation (i : ι) :
    eulerDifferentialOnPolynomialChart R ι i ≫ eulerAugmentationOnPolynomialChart R ι i = 0 := by
  rw [eulerDifferentialOnPolynomialChart, Category.assoc,
    eulerKernelFromFreeOnPolynomialChart_comp_augmentation]
  simp



end AlgebraicGeometry.ProjectiveSpace
