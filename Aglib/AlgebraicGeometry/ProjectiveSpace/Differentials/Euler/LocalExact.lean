/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Differentials.Euler.MiddleFrame
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Actual relative Euler arrows and exactness on polynomial charts

The actual restricted relative differential sheaf maps to the actual Euler tensor middle
object by the original coordinate kernel-vector formula. The second arrow is the restriction
of the original global augmentation with the original unit comparison. Explicit coordinate
projection and section maps split this native short complex, proving short exactness for
all commutative rings and arbitrary coordinate types, including an empty complementary basis.
The original relative differential of `X_j/X_i` maps to its original coordinate kernel
vector on every principal chart open. Compatibility and global gluing remain separate
obligations.
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

/-- The actual Euler chart arrow sends the original relative differential of the original
ratio `X_j/X_i` to its original coordinate kernel vector. -/
theorem eulerDifferentialOnPolynomialChart_d_ratio (i : ι) :
    let S : CommRingCat.{u} := .of (MvPolynomial {j : ι // j ≠ i} R)
    ∀ (r : S) (j : {j : ι // j ≠ i}),
      let V := PrimeSpectrum.basicOpen r
      (eulerDifferentialOnPolynomialChart R ι i).val.app (op V)
        ((Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
          (eulerCoordinateRatio R ι i j.val (eulerPolynomialChart_image_le R ι i V))) =
        eulerKernelGenerator R ι i j.val (eulerPolynomialChart_image_le R ι i V) := by
  exact fun r j => (congrArg (fun s => (eulerDifferentialOnPolynomialChart R ι i).val.app
    (op (PrimeSpectrum.basicOpen r))
      ((Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d s))
        (eulerCoordinateRatio_eq_polynomialSection R ι i j (PrimeSpectrum.basicOpen r))).trans
          (eulerDifferentialOnPolynomialChart_d R ι i r j)

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



/-- The original complementary coordinate sections, with the zero family at the distinguished
coordinate. -/
def eulerComplementSectionOnPolynomialChart (i j : ι) :
    (SheafOfModules.free
      (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf)
      {j : ι // j ≠ i}).sections := by
  classical
  exact if h : j ≠ i then SheafOfModules.freeSection ⟨j, h⟩ else
    _root_.PresheafOfModules.sectionsMk (fun _ => 0) (by intro V W k; exact map_zero _)

/-- Projection away from the original distinguished coordinate in the original free frame. -/
def eulerFreeComplementProjection (i : ι) :
    SheafOfModules.free
      (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf) ι ⟶
      SheafOfModules.free
        (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf)
        {j : ι // j ≠ i} :=
  (SheafOfModules.free
    (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf)
      {j : ι // j ≠ i}).freeHomEquiv.symm (eulerComplementSectionOnPolynomialChart R ι i)

/-- Projection preserves each original complementary coordinate vector. -/
theorem eulerFreeComplementProjection_freeSection (i : ι) (j : {j : ι // j ≠ i})
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens) :
    (eulerFreeComplementProjection R ι i).val.app (op V)
      ((SheafOfModules.freeSection
        (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf) j.val).val
          (op V)) =
      (SheafOfModules.freeSection
        (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf) j).val
          (op V) := by
  classical
  exact (congrArg (fun s : (SheafOfModules.free
      (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf)
      {j : ι // j ≠ i}).sections => s.val (op V))
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (eulerComplementSectionOnPolynomialChart R ι i) j.val)).trans
        (by simp [eulerComplementSectionOnPolynomialChart, j.property])

/-- Projection kills the distinguished original coordinate vector. -/
theorem eulerFreeComplementProjection_freeSection_self (i : ι)
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens) :
    (eulerFreeComplementProjection R ι i).val.app (op V)
      ((SheafOfModules.freeSection
        (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf) i).val
          (op V)) = 0 := by
  classical
  exact (congrArg (fun s : (SheafOfModules.free
      (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf)
      {j : ι // j ≠ i}).sections => s.val (op V))
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (eulerComplementSectionOnPolynomialChart R ι i) i)).trans
        (by simp [eulerComplementSectionOnPolynomialChart,
          _root_.PresheafOfModules.sectionsMk])

/-- The actual original middle sheaf projects to complementary free coordinates. -/
def eulerKernelProjectionOnPolynomialChart (i : ι) :
    (eulerMiddle R ι).restrict (eulerPolynomialChart R ι i) ⟶
      SheafOfModules.free
        (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf)
        {j : ι // j ≠ i} :=
  (eulerMiddlePolynomialFreeIso R ι i).hom ≫ eulerFreeComplementProjection R ι i

/-- A complementary original middle generator projects to the same complementary coordinate. -/
theorem eulerKernelProjectionOnPolynomialChart_generator (i : ι) (j : {j : ι // j ≠ i})
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens) :
    (eulerKernelProjectionOnPolynomialChart R ι i).val.app (op V)
      (eulerMiddleGenerator R ι i j.val (eulerPolynomialChart_image_le R ι i V)) =
      (SheafOfModules.freeSection
        (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf) j).val
          (op V) :=
  (congrArg ((eulerFreeComplementProjection R ι i).val.app (op V))
    (eulerMiddlePolynomialFreeIso_hom_generator R ι i j.val V)).trans
      (eulerFreeComplementProjection_freeSection R ι i j V)

/-- The distinguished original middle generator has zero complementary coordinates. -/
theorem eulerKernelProjectionOnPolynomialChart_generator_self (i : ι)
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens) :
    (eulerKernelProjectionOnPolynomialChart R ι i).val.app (op V)
      (eulerMiddleGenerator R ι i i (eulerPolynomialChart_image_le R ι i V)) = 0 :=
  (congrArg ((eulerFreeComplementProjection R ι i).val.app (op V))
    (eulerMiddlePolynomialFreeIso_hom_generator R ι i i V)).trans
      (eulerFreeComplementProjection_freeSection_self R ι i V)

/-- The actual complementary projection retains the original scalar action through the
original chart structure-sheaf map. -/
theorem eulerKernelProjectionOnPolynomialChart_smul (i : ι)
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens)
    (r : Γ(ProjectiveSpace R ι, eulerPolynomialChart R ι i ''ᵁ V))
    (m : Γ(eulerMiddle R ι, eulerPolynomialChart R ι i ''ᵁ V)) :
    (eulerKernelProjectionOnPolynomialChart R ι i).val.app (op V) (r • m) =
      ((eulerPolynomialChart R ι i).appIso V).hom r •
        (eulerKernelProjectionOnPolynomialChart R ι i).val.app (op V) m :=
  (congrArg ((eulerFreeComplementProjection R ι i).val.app (op V))
    (eulerMiddlePolynomialFreeIso_hom_smul R ι i V r m)).trans
      (((eulerFreeComplementProjection R ι i).val.app (op V)).hom.map_smul _ _)

/-- The actual kernel-vector arrow has a left inverse on the original polynomial chart. -/
theorem eulerKernelFromFreeOnPolynomialChart_comp_projection (i : ι) :
    eulerKernelFromFreeOnPolynomialChart R ι i ≫
      eulerKernelProjectionOnPolynomialChart R ι i = 𝟙 _ := by
  apply (SheafOfModules.freeHomEquiv
    (SheafOfModules.free
      (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf)
      {j : ι // j ≠ i})).injective
  funext j
  ext V
  let g := eulerPolynomialChart R ι i
  let q := (eulerKernelProjectionOnPolynomialChart R ι i).val.app V
  let r := eulerCoordinateRatio R ι i j.val (eulerPolynomialChart_image_le R ι i V.unop)
  let m := eulerMiddleGenerator R ι i i (eulerPolynomialChart_image_le R ι i V.unop)
  have hs := eulerKernelProjectionOnPolynomialChart_smul R ι i V.unop r m
  have hi := eulerKernelProjectionOnPolynomialChart_generator_self R ι i V.unop
  have hj := eulerKernelProjectionOnPolynomialChart_generator R ι i j V.unop
  have hm : q (r • m) = 0 :=
    hs.trans ((congrArg (fun z => ((g.appIso V.unop).hom r) • z) hi).trans (smul_zero _))
  have hk : q (eulerKernelGenerator R ι i j.val
      (eulerPolynomialChart_image_le R ι i V.unop)) =
        (SheafOfModules.freeSection
          (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf) j).val V :=
    (q.hom.map_sub _ _).trans
      ((congrArg₂ (fun a b => a - b) hj hm).trans (sub_zero _))
  exact (congrArg q
    (eulerKernelFromFreeOnPolynomialChart_freeSection R ι i j V.unop)).trans hk

/-- The original distinguished coordinate vector splits the actual augmentation on the chart. -/
def eulerAugmentationSectionOnPolynomialChart (i : ι) :
    SheafOfModules.unit
      (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf ⟶
      (eulerMiddle R ι).restrict (eulerPolynomialChart R ι i) :=
  SheafOfModules.ιFree i ≫ (eulerMiddlePolynomialFreeIso R ι i).inv

/-- The augmentation section at one is the original distinguished tensor generator. -/
theorem eulerAugmentationSectionOnPolynomialChart_one (i : ι)
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens) :
    (eulerAugmentationSectionOnPolynomialChart R ι i).val.app (op V)
      (1 : Γ(Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R)), V)) =
      eulerMiddleGenerator R ι i i (eulerPolynomialChart_image_le R ι i V) :=
  eulerMiddlePolynomialFreeIso_inv_freeSection R ι i i V

/-- The restricted original augmentation retains the original coordinate-ratio formula. -/
theorem eulerAugmentationOnPolynomialChart_generator (i j : ι)
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens) :
    (eulerAugmentationOnPolynomialChart R ι i).val.app (op V)
      (eulerMiddleGenerator R ι i j (eulerPolynomialChart_image_le R ι i V)) =
      ((eulerPolynomialChart R ι i).appIso V).hom
        (eulerCoordinateRatio R ι i j (eulerPolynomialChart_image_le R ι i V)) :=
  congrArg ((Scheme.Modules.restrictUnitIso (eulerPolynomialChart R ι i)).hom.val.app (op V))
    (eulerAugmentation_generator R ι i j (eulerPolynomialChart_image_le R ι i V))

/-- The original coordinate-vector section is a right inverse of the actual chart augmentation. -/
theorem eulerAugmentationSectionOnPolynomialChart_comp_augmentation (i : ι) :
    eulerAugmentationSectionOnPolynomialChart R ι i ≫
      eulerAugmentationOnPolynomialChart R ι i = 𝟙 _ := by
  apply (SheafOfModules.unit
    (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf).unitHomEquiv.injective
  ext V
  let X := Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))
  change (eulerAugmentationOnPolynomialChart R ι i).val.app V
    ((eulerAugmentationSectionOnPolynomialChart R ι i).val.app V
      (1 : Γ(X, V.unop))) = (1 : Γ(X, V.unop))
  exact (congrArg ((eulerAugmentationOnPolynomialChart R ι i).val.app V)
    (eulerAugmentationSectionOnPolynomialChart_one R ι i V.unop)).trans
      ((eulerAugmentationOnPolynomialChart_generator R ι i i V.unop).trans
        ((congrArg ((eulerPolynomialChart R ι i).appIso V.unop).hom
          (eulerCoordinateRatio_self R ι i
            (eulerPolynomialChart_image_le R ι i V.unop))).trans
              ((eulerPolynomialChart R ι i).appIso V.unop).hom.hom.map_one))

/-- The augmentation section converts the original structure scalar to the original tensor
multiple of the distinguished coordinate vector. -/
theorem eulerAugmentationSectionOnPolynomialChart_scalar (i : ι)
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens)
    (r : Γ(ProjectiveSpace R ι, eulerPolynomialChart R ι i ''ᵁ V)) :
    (eulerAugmentationSectionOnPolynomialChart R ι i).val.app (op V)
      (((eulerPolynomialChart R ι i).appIso V).hom r) =
      r • eulerMiddleGenerator R ι i i (eulerPolynomialChart_image_le R ι i V) := by
  let X := Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))
  let g := eulerPolynomialChart R ι i
  let s := eulerAugmentationSectionOnPolynomialChart R ι i
  let r' : Γ(X, V) := (g.appIso V).hom r
  let m : Γ(eulerMiddle R ι, g ''ᵁ V) :=
    eulerMiddleGenerator R ι i i (eulerPolynomialChart_image_le R ι i V)
  let m' : Γ((eulerMiddle R ι).restrict g, V) := m
  have ht : r' • m' = r • m := by
    change ((g.appIso V).inv r') • m = r • m
    exact congrArg (fun a : Γ(ProjectiveSpace R ι, g ''ᵁ V) => a • m)
      (Iso.hom_inv_id_apply (g.appIso V) r)
  exact (congrArg (s.val.app (op V)) (mul_one r')).symm.trans
    (((s.val.app (op V)).hom.map_smul r' (1 : Γ(X, V))).trans
      ((congrArg (fun z : Γ((eulerMiddle R ι).restrict g, V) => r' • z)
        (eulerAugmentationSectionOnPolynomialChart_one R ι i V)).trans ht))

/-- The original complementary kernel vectors and distinguished coordinate vector decompose
all original middle sections on the actual polynomial chart. -/
theorem eulerPolynomialChart_decomposition (i : ι) :
    eulerKernelProjectionOnPolynomialChart R ι i ≫
        eulerKernelFromFreeOnPolynomialChart R ι i +
      eulerAugmentationOnPolynomialChart R ι i ≫
        eulerAugmentationSectionOnPolynomialChart R ι i = 𝟙 _ := by
  apply (cancel_epi (eulerMiddlePolynomialFreeIso R ι i).inv).1
  apply (((eulerMiddle R ι).restrict (eulerPolynomialChart R ι i)).freeHomEquiv).injective
  funext j
  ext V
  change (eulerKernelFromFreeOnPolynomialChart R ι i).val.app V
      ((eulerKernelProjectionOnPolynomialChart R ι i).val.app V
        ((eulerMiddlePolynomialFreeIso R ι i).inv.val.app V
          ((SheafOfModules.freeSection
            (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf) j).val
            V))) +
    (eulerAugmentationSectionOnPolynomialChart R ι i).val.app V
      ((eulerAugmentationOnPolynomialChart R ι i).val.app V
        ((eulerMiddlePolynomialFreeIso R ι i).inv.val.app V
          ((SheafOfModules.freeSection
            (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf) j).val
            V))) =
      (eulerMiddlePolynomialFreeIso R ι i).inv.val.app V
        ((SheafOfModules.freeSection
          (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf) j).val V)
  let g := eulerPolynomialChart R ι i
  let q := (eulerKernelProjectionOnPolynomialChart R ι i).val.app V
  let a := (eulerKernelFromFreeOnPolynomialChart R ι i).val.app V
  let e := (eulerAugmentationOnPolynomialChart R ι i).val.app V
  let s := (eulerAugmentationSectionOnPolynomialChart R ι i).val.app V
  let w := eulerMiddleGenerator R ι i j (eulerPolynomialChart_image_le R ι i V.unop)
  let m := eulerMiddleGenerator R ι i i (eulerPolynomialChart_image_le R ι i V.unop)
  let r := eulerCoordinateRatio R ι i j (eulerPolynomialChart_image_le R ι i V.unop)
  have hright : s (e w) = r • m :=
    (congrArg s (eulerAugmentationOnPolynomialChart_generator R ι i j V.unop)).trans
      (eulerAugmentationSectionOnPolynomialChart_scalar R ι i V.unop r)
  have hw : a (q w) + s (e w) = w := by
    by_cases h : j ≠ i
    · have hleft : a (q w) = eulerKernelGenerator R ι i j
          (eulerPolynomialChart_image_le R ι i V.unop) :=
        (congrArg a
          (eulerKernelProjectionOnPolynomialChart_generator R ι i ⟨j, h⟩ V.unop)).trans
            (eulerKernelFromFreeOnPolynomialChart_freeSection R ι i ⟨j, h⟩ V.unop)
      exact (congrArg₂ (fun x y : Γ(eulerMiddle R ι, g ''ᵁ V.unop) => x + y)
        hleft hright).trans (sub_add_cancel _ _)
    · have hji : j = i := not_not.mp h
      subst j
      have hleft : a (q w) = 0 :=
        (congrArg a (eulerKernelProjectionOnPolynomialChart_generator_self R ι i V.unop)).trans
          a.hom.map_zero
      have hr : r = (1 : Γ(ProjectiveSpace R ι, g ''ᵁ V.unop)) :=
        eulerCoordinateRatio_self R ι i (eulerPolynomialChart_image_le R ι i V.unop)
      have hright' : s (e w) = m := hright.trans
        ((congrArg (fun z : Γ(ProjectiveSpace R ι, g ''ᵁ V.unop) => z • m) hr).trans
          (one_smul _ _))
      exact (congrArg₂ (fun x y : Γ(eulerMiddle R ι, g ''ᵁ V.unop) => x + y)
        hleft hright').trans (zero_add _)
  have hinv := eulerMiddlePolynomialFreeIso_inv_freeSection R ι i j V.unop
  exact (congrArg (fun z : Γ((eulerMiddle R ι).restrict g, V.unop) =>
    a (q z) + s (e z)) hinv).trans (hw.trans hinv.symm)

/-- The actual relative Euler arrows on the original polynomial chart. -/
def eulerShortComplexOnPolynomialChart (i : ι) :
    CategoryTheory.ShortComplex
      (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Modules :=
  CategoryTheory.ShortComplex.mk
    (eulerDifferentialOnPolynomialChart R ι i)
    (eulerAugmentationOnPolynomialChart R ι i)
    (eulerDifferentialOnPolynomialChart_comp_augmentation R ι i)

/-- The original chart Euler complex has its explicit coordinate splitting. -/
def eulerShortComplexOnPolynomialChartSplitting (i : ι) :
    (eulerShortComplexOnPolynomialChart R ι i).Splitting where
  r := eulerKernelProjectionOnPolynomialChart R ι i ≫
    (eulerPolynomialOmegaFreeIso R ι i).inv
  s := eulerAugmentationSectionOnPolynomialChart R ι i
  f_r := by
    change ((eulerPolynomialOmegaFreeIso R ι i).hom ≫
      eulerKernelFromFreeOnPolynomialChart R ι i) ≫
        (eulerKernelProjectionOnPolynomialChart R ι i ≫
          (eulerPolynomialOmegaFreeIso R ι i).inv) = 𝟙 _
    rw [Category.assoc, ← Category.assoc (eulerKernelFromFreeOnPolynomialChart R ι i),
      eulerKernelFromFreeOnPolynomialChart_comp_projection, Category.id_comp, Iso.hom_inv_id]
  s_g := eulerAugmentationSectionOnPolynomialChart_comp_augmentation R ι i
  id := by
    change (eulerKernelProjectionOnPolynomialChart R ι i ≫
      (eulerPolynomialOmegaFreeIso R ι i).inv) ≫
        ((eulerPolynomialOmegaFreeIso R ι i).hom ≫
          eulerKernelFromFreeOnPolynomialChart R ι i) +
      eulerAugmentationOnPolynomialChart R ι i ≫
        eulerAugmentationSectionOnPolynomialChart R ι i = 𝟙 _
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      eulerPolynomialChart_decomposition R ι i

/-- The actual relative Euler sequence is short exact on every original polynomial chart. -/
theorem eulerShortComplexOnPolynomialChart_shortExact (i : ι) :
    (eulerShortComplexOnPolynomialChart R ι i).ShortExact :=
  (eulerShortComplexOnPolynomialChartSplitting R ι i).shortExact

end AlgebraicGeometry.ProjectiveSpace
