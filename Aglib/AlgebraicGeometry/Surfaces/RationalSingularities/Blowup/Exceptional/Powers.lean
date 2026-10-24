/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Blowup.Exceptional
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.Pullback
public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.ClosedImmersion
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Original exceptional power sections

For the full exceptional scheme E of the ordinary rational surface blowup,
the original restricted ideal power is canonically L^n for L=i*I. The actual
ideal-product short exact sequence has the original inclusion and the
original restriction adjunction unit as its maps.

The original scalar sections identify Γ(X,I^n) with m^n. H1 of the next power
gives surjectivity onto Γ(E,L^n), and exactness identifies the kernel with
m^(n+1). The resulting equivalence is linear over the original A/m action.
It retains every original quotient value, agrees in degree zero with the
structural coefficient map already constructed in Exceptional, and respects
the actual ideal product on original representatives.

The same row and the derived positive-power H2 bound give H1(E,L^n)=0 for
all n≥0. No reduction, coefficient section, CM/Hilbert hypothesis or
Gorenstein/slope-two conclusion is involved.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Blowup

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

private theorem compose_iso_inclusions {C : Type*} [Category* C] {M N P Q : C}
    (e : M ≅ N) (f : N ≅ P) (a : P ⟶ Q) (b : N ⟶ Q) (c : M ⟶ Q)
    (hf : f.hom ≫ a = b) (he : e.hom ≫ b = c) :
    (e ≪≫ f).hom ≫ a = c :=
  (Category.assoc e.hom f.hom a).trans
    ((congrArg (fun z => e.hom ≫ z) hf).trans he)

private theorem power_iso_inv_isIso {C : Type*} [Category* C]
    {M N : C} (e : M ≅ N) : IsIso e.inv := inferInstance

private theorem power_cancel_iso_hom {C : Type*} [Category* C]
    {L M N : C} (e : L ≅ M) (f g : M ⟶ N) (h : e.hom ≫ f = e.hom ≫ g) : f = g :=
  (cancel_epi e.hom).mp h

private theorem power_hom_inv_assoc {C : Type*} [Category* C]
    {L M N : C} (e : L ≅ M) (f : L ⟶ N) : e.hom ≫ (e.inv ≫ f) = f :=
  e.hom_inv_id_assoc f

private theorem power_trans_mapIso_hom {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {M N : C} {V : D} (e : V ≅ F.obj M) (r : M ≅ N) :
    (e ≪≫ F.mapIso r).hom = e.hom ≫ F.map r.hom := rfl

private theorem tensor_ideal_inclusion {X C D : Scheme.{u}}
    (i : C ⟶ X) (j : D ⟶ X) :
    (moduleTensorLeftFunctor X (idealModule i)).map (idealInclusion j) ≫
      (rightUnitor (C := X.Modules) (idealModule i)).hom ≫ idealInclusion i =
        Cartier.idealMultiplication i j := by
  apply moduleTensor_hom_ext
  intro U a b
  let c : Γ(X, U) := (idealInclusion j).val.app (op U) b
  have h₁ := congrArg (fun z => (idealInclusion i).val.app (op U)
      ((rightUnitor (C := X.Modules) (idealModule i)).hom.val.app (op U) z))
    (moduleTensorLeftFunctor_map_section (idealModule i) (idealInclusion j) U a b)
  have h₂ := congrArg (fun z => (idealInclusion i).val.app (op U) z)
    (tensorRightUnitIso_hom_section X (idealModule i) U a c)
  have h₃ := ((idealInclusion i).val.app (op U)).hom.map_smul c a
  have h₄ := idealMultiplication_section i j U a b
  exact h₁.trans (h₂.trans (h₃.trans
    ((mul_comm c (show Γ(X, U) from (idealInclusion i).val.app (op U) a)).trans h₄.symm)))

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The original Cartier line on the ordinary blowup. -/
def ordinaryExceptionalLine (hd : ringKrullDim A = 2) : LineBundle (source A hd) :=
  ⟨idealModule (exceptionalCurveInclusion A hd), (datum A).cartier⟩

/-- The original line L=i*I on the full exceptional scheme. -/
def exceptionalLine (hd : ringKrullDim A = 2) : LineBundle (exceptionalCurve A hd) :=
  pullbackLineBundle (exceptionalCurveInclusion A hd) (ordinaryExceptionalLine A hd)

/-- The original restricted ideal power, canonically L^n. -/
def exceptionalPower (hd : ringKrullDim A = 2) (n : ℕ) : (exceptionalCurve A hd).Modules :=
  (Modules.pullback (exceptionalCurveInclusion A hd)).obj (ordinaryIdealPower A hd n)

/-- The native Cartier comparison with the literal original ideal power. -/
def ordinaryTensorPowerIso (hd : ringKrullDim A = 2) (n : ℕ) :
    (tensorPowerLineBundle (source A hd) (ordinaryExceptionalLine A hd) n).val ≅
      ordinaryIdealPower A hd n := by
  let i := exceptionalCurveInclusion A hd
  let e := Surfaces.Contraction.FormalNeighborhood.cartierIdealPowerIso i (datum A).cartier n
  have h : (i.ker ^ n).subschemeι.ker = ((exceptionalIdeal A hd) ^ n).subschemeι.ker :=
    (Scheme.IdealSheafData.ker_subschemeι _).trans
      ((ordinaryPower_kernel_eq A hd n).trans (Scheme.IdealSheafData.ker_subschemeι _).symm)
  exact e ≪≫ Surfaces.Contraction.FormalNeighborhood.idealModuleIsoOfKernelEq _ _ h

/-- Restriction and the native tensor-power pullback comparison identify the same L^n. -/
def exceptionalPowerTensorIso (hd : ringKrullDim A = 2) (n : ℕ) :
    exceptionalPower A hd n ≅
      (tensorPowerLineBundle (exceptionalCurve A hd) (exceptionalLine A hd) n).val :=
  (Modules.pullback (exceptionalCurveInclusion A hd)).mapIso
      (ordinaryTensorPowerIso A hd n).symm ≪≫
    PowerPullback.pullbackPowerIso (exceptionalCurveInclusion A hd)
      (ordinaryExceptionalLine A hd) n

/-- The original zeroth-power ideal inclusion is invertible. -/
theorem ordinaryPowerZeroInclusion_isIso (hd : ringKrullDim A = 2) :
    IsIso (idealInclusion ((exceptionalIdeal A hd) ^ 0).subschemeι) := by
  let X := source A hd
  have htop : IsIso (idealInclusion (⊤ : X.IdealSheafData).subschemeι) :=
    power_iso_inv_isIso (C := X.Modules)
      (Surfaces.Contraction.FormalNeighborhood.topIdealModuleIso (X := X))
  have hpow : (exceptionalIdeal A hd) ^ 0 = (⊤ : X.IdealSheafData) := pow_zero _
  exact (congrArg (fun J : X.IdealSheafData => IsIso (idealInclusion J.subschemeι)) hpow).mpr htop

/-- The original zero-power comparison has the literal ideal inclusion as its forward map. -/
def ordinaryPowerZeroIso (hd : ringKrullDim A = 2) :
    ordinaryIdealPower A hd 0 ≅ originalUnit (source A hd) :=
  @asIso (source A hd).Modules inferInstance
    (ordinaryIdealPower A hd 0) (originalUnit (source A hd))
    (idealInclusion ((exceptionalIdeal A hd) ^ 0).subschemeι)
    (ordinaryPowerZeroInclusion_isIso A hd)

/-- Degree zero retains the original exceptional structure-module pullback. -/
def exceptionalPowerZeroIso (hd : ringKrullDim A = 2) :
    exceptionalPower A hd 0 ≅ originalUnit (exceptionalCurve A hd) :=
  (Modules.pullback (exceptionalCurveInclusion A hd)).mapIso (ordinaryPowerZeroIso A hd) ≪≫
    pullbackUnitIso (exceptionalCurveInclusion A hd)

/-- Native multiplication I^n tensor I identifies with the original next power. -/
def ordinaryPowerStepIso (hd : ringKrullDim A = 2) (n : ℕ) :
    tensorSheaf (source A hd) (ordinaryIdealPower A hd n)
      (idealModule (exceptionalCurveInclusion A hd)) ≅ ordinaryIdealPower A hd (n + 1) := by
  let i := ((exceptionalIdeal A hd) ^ n).subschemeι
  let j := exceptionalCurveInclusion A hd
  let e := idealProductIso i j (ordinaryIdealPower_locallyRankOne A hd n)
  have hi : i.ker = (exceptionalIdeal A hd) ^ n :=
    Scheme.IdealSheafData.ker_subschemeι ((exceptionalIdeal A hd) ^ n)
  have hj : j.ker = exceptionalIdeal A hd :=
    Scheme.IdealSheafData.ker_subschemeι (exceptionalIdeal A hd)
  have hp : i.ker * j.ker = (exceptionalIdeal A hd) ^ (n + 1) :=
    (congrArg₂ (fun J K : (source A hd).IdealSheafData => J * K) hi hj).trans
      (pow_succ (exceptionalIdeal A hd) n).symm
  have h : (i.ker * j.ker).subschemeι.ker =
      ((exceptionalIdeal A hd) ^ (n + 1)).subschemeι.ker :=
    (Scheme.IdealSheafData.ker_subschemeι _).trans
      (hp.trans (Scheme.IdealSheafData.ker_subschemeι _).symm)
  exact e ≪≫ Surfaces.Contraction.FormalNeighborhood.idealModuleIsoOfKernelEq _ _ h

/-- The product comparison retains the native original multiplication into the unit. -/
theorem ordinaryPowerStepIso_inclusion (hd : ringKrullDim A = 2) (n : ℕ) :
    (ordinaryPowerStepIso A hd n).hom ≫
      idealInclusion ((exceptionalIdeal A hd) ^ (n + 1)).subschemeι =
        Cartier.idealMultiplication ((exceptionalIdeal A hd) ^ n).subschemeι
          (exceptionalCurveInclusion A hd) := by
  let i := ((exceptionalIdeal A hd) ^ n).subschemeι
  let j := exceptionalCurveInclusion A hd
  let e := idealProductIso i j (ordinaryIdealPower_locallyRankOne A hd n)
  have hi : i.ker = (exceptionalIdeal A hd) ^ n :=
    Scheme.IdealSheafData.ker_subschemeι ((exceptionalIdeal A hd) ^ n)
  have hj : j.ker = exceptionalIdeal A hd :=
    Scheme.IdealSheafData.ker_subschemeι (exceptionalIdeal A hd)
  have hp : i.ker * j.ker = (exceptionalIdeal A hd) ^ (n + 1) :=
    (congrArg₂ (fun J K : (source A hd).IdealSheafData => J * K) hi hj).trans
      (pow_succ (exceptionalIdeal A hd) n).symm
  have h : (i.ker * j.ker).subschemeι.ker =
      ((exceptionalIdeal A hd) ^ (n + 1)).subschemeι.ker :=
    (Scheme.IdealSheafData.ker_subschemeι _).trans
      (hp.trans (Scheme.IdealSheafData.ker_subschemeι _).symm)
  let c := Surfaces.Contraction.FormalNeighborhood.idealModuleIsoOfKernelEq _ _ h
  exact compose_iso_inclusions e c _ _ _
    (Surfaces.Contraction.FormalNeighborhood.idealModuleIsoOfKernelEq_hom_inclusion _ _ h)
    (idealProductIso_hom_inclusion i j (ordinaryIdealPower_locallyRankOne A hd n))

/-- The literal original ideal-product row with quotient i_*L^n. -/
def exceptionalPowerSequence (hd : ringKrullDim A = 2) (n : ℕ) :
    ShortComplex (source A hd).Modules := by
  let X := source A hd
  let E := exceptionalCurve A hd
  let i := exceptionalCurveInclusion A hd
  let P := ordinaryIdealPower A hd n
  let T := moduleTensorLeftFunctor X P
  let S := (Hom.idealSequence i).map T
  let e₁ : S.X₁ ≅ ordinaryIdealPower A hd (n + 1) := ordinaryPowerStepIso A hd n
  let e₂ : S.X₂ ≅ P := rightUnitor (C := X.Modules) P
  let e₃ : S.X₃ ≅ (Modules.pushforward i).obj (exceptionalPower A hd n) :=
    closedImmersionProjectionFormulaIso i P (originalUnit E) ≪≫
      (Modules.pushforward i).mapIso
        (rightUnitor (C := E.Modules) ((Modules.pullback i).obj P))
  exact Surfaces.Contraction.cartierSequenceOfIsos S e₁ e₂ e₃

/-- Exactness follows from tensoring the actual ideal row by the actual invertible power. -/
theorem exceptionalPowerSequence_shortExact (hd : ringKrullDim A = 2) (n : ℕ) :
    (exceptionalPowerSequence A hd n).ShortExact := by
  let X := source A hd
  let P := ordinaryIdealPower A hd n
  let : IsFiniteLocallyFree X P :=
    isFiniteLocallyFree_of_isLocallyRankOne (ordinaryIdealPower_locallyRankOne A hd n)
  have h := tensor_shortExact_finiteLocallyFree P
    (Hom.idealSequence (exceptionalCurveInclusion A hd))
    (Hom.idealSequence_shortExact (exceptionalCurveInclusion A hd))
  exact Surfaces.Contraction.cartierSequenceOfIsos_shortExact _ _ _ _ h

/-- The first row map is the original inclusion of successive ideal powers. -/
theorem exceptionalPowerSequence_f_inclusion (hd : ringKrullDim A = 2) (n : ℕ) :
    (exceptionalPowerSequence A hd n).f ≫
      idealInclusion ((exceptionalIdeal A hd) ^ n).subschemeι =
        idealInclusion ((exceptionalIdeal A hd) ^ (n + 1)).subschemeι := by
  let X := source A hd
  let i := exceptionalCurveInclusion A hd
  let P := ordinaryIdealPower A hd n
  let e := ordinaryPowerStepIso A hd n
  let S := exceptionalPowerSequence A hd n
  apply power_cancel_iso_hom (C := X.Modules) e
  have hf : e.hom ≫ S.f = (moduleTensorLeftFunctor X P).map (idealInclusion i) ≫
      (rightUnitor (C := X.Modules) P).hom :=
    power_hom_inv_assoc (C := X.Modules) e
      ((moduleTensorLeftFunctor X P).map (idealInclusion i) ≫
        (rightUnitor (C := X.Modules) P).hom)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ idealInclusion ((exceptionalIdeal A hd) ^ n).subschemeι) hf).trans
      ((tensor_ideal_inclusion ((exceptionalIdeal A hd) ^ n).subschemeι i).trans
        (ordinaryPowerStepIso_inclusion A hd n).symm))


private theorem power_projection_unit_square {Y X : Scheme.{u}} (f : Y ⟶ X) (P : X.Modules) :
    (moduleTensorLeftFunctor X P).map (structureModuleMap f) ≫
      projectionFormulaMap f P (originalUnit Y) ≫
        (Modules.pushforward f).map
          (rightUnitor (C := Y.Modules) ((Modules.pullback f).obj P)).hom =
      (rightUnitor (C := X.Modules) P).hom ≫
        (Modules.pullbackPushforwardAdjunction f).unit.app P := by
  apply moduleTensor_hom_ext
  intro U p a
  let Q := (Modules.pullback f).obj P
  let η := (Modules.pullbackPushforwardAdjunction f).unit.app P
  let r := (rightUnitor (C := Y.Modules) Q).hom
  let L := fun z : Γ(tensorSheaf X P ((Modules.pushforward f).obj (originalUnit Y)), U) =>
    ((Modules.pushforward f).map r).val.app (op U)
      ((projectionFormulaMap f P (originalUnit Y)).val.app (op U) z)
  have h₀ := congrArg L
    (moduleTensorLeftFunctor_map_section P (structureModuleMap f) U p a)
  have h₁ := congrArg (fun z : Γ(tensorSheaf Y Q (originalUnit Y), f ⁻¹ᵁ U) =>
    r.val.app (op (f ⁻¹ᵁ U)) z)
      (projectionFormulaMap_section f P (originalUnit Y) U p (f.app U a))
  have h₂ := tensorRightUnitIso_hom_section Y Q (f ⁻¹ᵁ U)
    (η.val.app (op U) p) (f.app U a)
  have h₃ := (η.val.app (op U)).hom.map_smul a p
  have h₄ := congrArg (fun z : Γ(P, U) => η.val.app (op U) z)
    (tensorRightUnitIso_hom_section X P U p a).symm
  exact h₀.trans (h₁.trans (h₂.trans (h₃.symm.trans h₄)))

/-- The quotient map is the original restriction adjunction unit, on the same ideal power. -/
theorem exceptionalPowerSequence_g (hd : ringKrullDim A = 2) (n : ℕ) :
    (exceptionalPowerSequence A hd n).g =
      (Modules.pullbackPushforwardAdjunction (exceptionalCurveInclusion A hd)).unit.app
        (ordinaryIdealPower A hd n) := by
  let X := source A hd
  let E := exceptionalCurve A hd
  let i := exceptionalCurveInclusion A hd
  let P := ordinaryIdealPower A hd n
  let e₂ := rightUnitor (C := X.Modules) P
  let e₃ := closedImmersionProjectionFormulaIso i P (originalUnit E) ≪≫
    (Modules.pushforward i).mapIso
      (rightUnitor (C := E.Modules) ((Modules.pullback i).obj P))
  let η := (Modules.pullbackPushforwardAdjunction i).unit.app P
  have he₃ : e₃.hom = projectionFormulaMap i P (originalUnit E) ≫
      (Modules.pushforward i).map
        (rightUnitor (C := E.Modules) ((Modules.pullback i).obj P)).hom :=
    power_trans_mapIso_hom (Modules.pushforward i)
      (closedImmersionProjectionFormulaIso i P (originalUnit E))
      (rightUnitor (C := E.Modules) ((Modules.pullback i).obj P))
  have h : (moduleTensorLeftFunctor X P).map (structureModuleMap i) ≫ e₃.hom =
      e₂.hom ≫ η :=
    (congrArg (fun z : (moduleTensorLeftFunctor X P).obj
        ((Modules.pushforward i).obj (originalUnit E)) ⟶
        (Modules.pushforward i).obj (exceptionalPower A hd n) =>
      (moduleTensorLeftFunctor X P).map (structureModuleMap i) ≫ z) he₃).trans
        (power_projection_unit_square i P)
  exact (congrArg (fun z => e₂.inv ≫ z) h).trans (e₂.inv_hom_id_assoc η)

/-- Original ordinary global sections with their original structural A-action. -/
abbrev ordinaryPowerSections (hd : ringKrullDim A = 2) (n : ℕ) : ModuleCat.{u} A :=
  (Cohomology.moduleGlobalSectionsFunctorOfHom (source A hd) (ordinaryCoefficients A hd)).obj
    (ordinaryIdealPower A hd n)

/-- Original exceptional sections with the A-action coming through their actual pushforward. -/
abbrev exceptionalPowerSections (hd : ringKrullDim A = 2) (n : ℕ) : ModuleCat.{u} A :=
  (Cohomology.moduleGlobalSectionsFunctorOfHom (source A hd) (ordinaryCoefficients A hd)).obj
    ((Modules.pushforward (exceptionalCurveInclusion A hd)).obj (exceptionalPower A hd n))

/-- The original κ-structure acts on these same exceptional sections. -/
instance exceptionalPowerSectionsQuotientModule (hd : ringKrullDim A = 2) (n : ℕ) :
    Module (A ⧸ IsLocalRing.maximalIdeal A) (exceptionalPowerSections A hd n) :=
  Module.compHom (Γ(exceptionalPower A hd n, ⊤)) (exceptionalCoefficients A hd)

/-- The scalar tower follows from the actual quotient-coefficient triangle. -/
instance exceptionalPowerSections_scalarTower (hd : ringKrullDim A = 2) (n : ℕ) :
    IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A) (exceptionalPowerSections A hd n) := by
  constructor
  intro a b s
  let c := exceptionalCoefficients A hd
  let s₀ : Γ(exceptionalPower A hd n, ⊤) := s
  change c (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a * b) • s₀ =
    (exceptionalCurveInclusion A hd).appTop (ordinaryCoefficients A hd a) • (c b • s₀)
  exact (congrArg (fun z : Γ(exceptionalCurve A hd, ⊤) => z • s₀)
    (map_mul c (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a) b)).trans
      ((mul_smul (c (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a)) (c b) s₀).trans
        (congrArg (fun z : Γ(exceptionalCurve A hd, ⊤) => z • (c b • s₀))
          (exceptionalCoefficients_quotient A hd a)))

/-- The native ideal-power quotient m^n/m^(n+1), with its canonical κ-module action. -/
abbrev exceptionalPowerLayer (n : ℕ) :=
  (IsLocalRing.maximalIdeal A ^ n : Ideal A) ⧸
    (IsLocalRing.maximalIdeal A •
      (⊤ : Submodule A (IsLocalRing.maximalIdeal A ^ n : Ideal A)))

/-- The original quotient class of an original ideal-power element. -/
def exceptionalPowerClass (n : ℕ) :
    (IsLocalRing.maximalIdeal A ^ n : Ideal A) →ₗ[A] exceptionalPowerLayer A n :=
  Submodule.mkQ _

/-- This native quotient kills exactly the original next ideal power. -/
theorem exceptionalPowerClass_eq_zero (n : ℕ)
    (a : ↥(IsLocalRing.maximalIdeal A ^ n)) :
    exceptionalPowerClass A n a = 0 ↔ (a : A) ∈ IsLocalRing.maximalIdeal A ^ (n + 1) := by
  let I := IsLocalRing.maximalIdeal A
  let J := I • (⊤ : Submodule A (I ^ n : Ideal A))
  have hq : J.mkQ a = 0 ↔ a ∈ J := Submodule.Quotient.mk_eq_zero J
  have hm : a ∈ J ↔ (a : A) ∈ I ^ (n + 1) := by
    change a ∈ I • (⊤ : Submodule A (I ^ n : Ideal A)) ↔ _
    simpa only [smul_eq_mul, pow_succ'] using
      (Submodule.mem_smul_top_iff (I := I) (I ^ n : Ideal A) a)
  exact hq.trans hm

private theorem power_unitMul_value (X : Scheme.{u}) (a : Γ(X, ⊤)) :
    (show Γ(X, ⊤) from (unitMul X a).val.app (op ⊤) (1 : Γ(X, ⊤))) = a := by
  change 1 * X.presheaf.map (𝟙 (op (⊤ : X.Opens))) a = a
  rw [CategoryTheory.Functor.map_id]
  exact one_mul a

/-- The original structural coefficient map as a linear map to its native unit sections. -/
def ordinaryCoefficientsLinear (hd : ringKrullDim A = 2) :
    A →ₗ[A] (Cohomology.moduleGlobalSectionsFunctorOfHom (source A hd)
      (ordinaryCoefficients A hd)).obj (originalUnit (source A hd)) :=
  LinearMap.toSpanSingleton A _ (1 : Γ(source A hd, ⊤))

/-- The linear map evaluates to the original structural ring coefficient. -/
theorem ordinaryCoefficientsLinear_apply (hd : ringKrullDim A = 2) (a : A) :
    ordinaryCoefficientsLinear A hd a = ordinaryCoefficients A hd a := by
  change ordinaryCoefficients A hd a * 1 = ordinaryCoefficients A hd a
  exact mul_one _

/-- The actual global section attached to the original power-ideal element. -/
def ordinaryPowerSectionValue (hd : ringKrullDim A = 2) (n : ℕ)
    (a : ↥(IsLocalRing.maximalIdeal A ^ n)) : ordinaryPowerSections A hd n :=
  unitHomGlobalSectionsEquiv (source A hd) (ordinaryIdealPower A hd n)
    (ordinaryPowerScalarSection A hd n a)

/-- The value of that section under the literal original ideal inclusion. -/
theorem ordinaryPowerSectionValue_inclusion (hd : ringKrullDim A = 2) (n : ℕ)
    (a : ↥(IsLocalRing.maximalIdeal A ^ n)) :
    (idealInclusion ((exceptionalIdeal A hd) ^ n).subschemeι).val.app (op ⊤)
      (ordinaryPowerSectionValue A hd n a) = ordinaryCoefficients A hd (a : A) := by
  have h := congrArg (fun f : originalUnit (source A hd) ⟶ originalUnit (source A hd) =>
    f.val.app (op ⊤) (1 : Γ(source A hd, ⊤)))
      (ordinaryPowerScalarSection_inclusion A hd n a)
  exact h.trans (power_unitMul_value (source A hd) (ordinaryCoefficients A hd (a : A)))

/-- The actual scalar sections are A-linear for the original structural action. -/
def ordinaryPowerSectionLinear (hd : ringKrullDim A = 2) (n : ℕ) :
    (IsLocalRing.maximalIdeal A ^ n : Ideal A) →ₗ[A] ordinaryPowerSections A hd n := by
  let X := source A hd
  let F := Cohomology.moduleGlobalSectionsFunctorOfHom X (ordinaryCoefficients A hd)
  let i := ((exceptionalIdeal A hd) ^ n).subschemeι
  let g := (F.map (idealInclusion i)).hom
  have hg : Function.Injective g := moduleHom_app_injective (idealInclusion i) ⊤
  let f := ordinaryPowerSectionValue A hd n
  let h := (ordinaryCoefficientsLinear A hd).comp (IsLocalRing.maximalIdeal A ^ n).subtype
  have hf (a) : g (f a) = h a :=
    (ordinaryPowerSectionValue_inclusion A hd n a).trans
      (ordinaryCoefficientsLinear_apply A hd (a : A)).symm
  exact {
    toFun := f
    map_add' := fun a b => hg ((hf (a + b)).trans ((h.map_add a b).trans
      ((congrArg₂ (· + ·) (hf a).symm (hf b).symm).trans (g.map_add (f a) (f b)).symm)))
    map_smul' := fun r a => hg ((hf (r • a)).trans ((h.map_smul r a).trans
      ((congrArg (r • ·) (hf a).symm).trans (g.map_smul r (f a)).symm))) }

/-- The linear constructor keeps the exact original section value. -/
theorem ordinaryPowerSectionLinear_apply (hd : ringKrullDim A = 2) (n : ℕ)
    (a : ↥(IsLocalRing.maximalIdeal A ^ n)) :
    ordinaryPowerSectionLinear A hd n a = ordinaryPowerSectionValue A hd n a := rfl

variable [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

/-- The original ordinary ideal-power H1 vanishes in every nonnegative degree. -/
theorem ordinaryIdealPower_H1 (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (n : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} (Cohomology.moduleAddSheaf (source A hd)
      (ordinaryIdealPower A hd n)) 1) := by
  cases n with
  | zero =>
    have hO := hRat (source A hd) (map A hd)
      (ordinary_normalStalks A hd hA hRat) (map_fieldMap_isIso A hd)
    exact Cohomology.moduleCohomology_subsingleton_of_iso (ordinaryPowerZeroIso A hd).symm 1 hO
  | succ n => exact ordinaryPositiveIdealPower_H1 A hd hA hRat n

/-- The actual coherent higher bound gives H2 and all higher degrees
on the positive ordinary powers. -/
theorem ordinaryPositiveIdealPower_higher (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A)
    (n q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H.{u + 1} (Cohomology.moduleAddSheaf (source A hd)
      (ordinaryIdealPower A hd (n + 1))) q) := by
  let X := source A hd
  let Y := normalization A hd
  let f := nu A hd
  let : IsFinite f := nu_isFinite A hd hA
  let M : Y.Modules := normalizedIdealPower A hd (n + 1)
  let P := tensorPowerLineBundle Y (normalizedIdealLineBundle A hd) (n + 1)
  let : IsFiniteLocallyFree Y M := isFiniteLocallyFree_of_isLocallyRankOne
    (isLocallyRankOne_of_iso Y (normalizedIdealPowerIso A hd (n + 1)) P.property)
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M
    (fun R j _ => (coherent_of_finiteLocallyFree M R j).1)
  let : Subsingleton (Sheaf.H.{u + 1} (Cohomology.moduleAddSheaf Y M) q) :=
    normalization_coherent_higher_vanishing A hd hA M (coherent_of_finiteLocallyFree M) q hq
  have hpush : Subsingleton (Sheaf.H.{u + 1}
      (Cohomology.moduleAddSheaf X ((Modules.pushforward f).obj M)) q) :=
    (Cohomology.moduleAffinePushforwardCohomologyLinearEquiv f
      (ordinaryCoefficients A hd) M q).toEquiv.subsingleton
  have hv : IsIso (idealPowerNormalizationUnit A hd (n + 1)) :=
    ordinaryPositivePowerNormalization_isIso A hd hA hRat n
  let e : ordinaryIdealPower A hd (n + 1) ≅ (Modules.pushforward f).obj M :=
    @asIso X.Modules inferInstance _ _ (idealPowerNormalizationUnit A hd (n + 1)) hv
  exact Cohomology.moduleCohomology_subsingleton_of_iso e.symm q hpush

/-- The nonnegative twists on the full exceptional scheme have H1 zero. -/
theorem exceptionalPower_H1 (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (n : ℕ) :
    Subsingleton (Sheaf.H.{u + 1}
      (Cohomology.moduleAddSheaf (exceptionalCurve A hd) (exceptionalPower A hd n)) 1) := by
  let X := source A hd
  let E := exceptionalCurve A hd
  let i := exceptionalCurveInclusion A hd
  let S := exceptionalPowerSequence A hd n
  let M := exceptionalPower A hd n
  let : IsFiniteLocallyFree E M := isFiniteLocallyFree_of_isLocallyRankOne
    (pullback_locallyRankOne i _ (ordinaryIdealPower_locallyRankOne A hd n))
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M
    (fun R j _ => (coherent_of_finiteLocallyFree M R j).1)
  let : Subsingleton (Sheaf.H.{u + 1}
      (Cohomology.moduleAddSheaf X ((Modules.pushforward i).obj M)) 1) :=
    Cohomology.moduleCohomology_subsingleton_X₃ S (exceptionalPowerSequence_shortExact A hd n) 1
      (ordinaryIdealPower_H1 A hd hA hRat n)
      (ordinaryPositiveIdealPower_higher A hd hA hRat n 2 (by decide))
  exact (Cohomology.moduleAffinePushforwardCohomologyLinearEquiv i
    (ordinaryCoefficients A hd) M 1).symm.toEquiv.subsingleton

/-- The original quotient restriction on each power is onto on global sections. -/
theorem exceptionalPowerSequence_global_surjective (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (n : ℕ) :
    Function.Surjective ((exceptionalPowerSequence A hd n).g.val.app (op ⊤)) := by
  let X := source A hd
  let S := exceptionalPowerSequence A hd n
  let α := ordinaryCoefficients A hd
  let : Subsingleton (Sheaf.H.{u + 1} (Cohomology.moduleAddSheaf X S.X₁) 1) :=
    ordinaryPositiveIdealPower_H1 A hd hA hRat n
  let := Cohomology.moduleCohomologyModuleOfHom X α S.X₃ 0
  let := Cohomology.moduleCohomologyModuleOfHom X α S.X₁ (0 + 1)
  exact Cohomology.surjective_of_moduleCohomologyConnectingOfHom_zero_eq_zero
    (X := X) α S (exceptionalPowerSequence_shortExact A hd n) (by
      apply LinearMap.ext
      intro x
      exact Subsingleton.elim _ _)


/-- The original scalar sections exhaust precisely the original ordinary power sections. -/
theorem ordinaryPowerSectionLinear_bijective (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (n : ℕ) :
    Function.Bijective (ordinaryPowerSectionLinear A hd n) := by
  let X := source A hd
  let Y := normalization A hd
  let i := ((exceptionalIdeal A hd) ^ n).subschemeι
  let j := ((normalizedExceptionalIdeal A hd) ^ n).subschemeι
  let f := nu A hd
  constructor
  · intro a b hab
    apply Subtype.ext
    apply (ordinaryCoefficients_bijective A hd).1
    exact (ordinaryPowerSectionValue_inclusion A hd n a).symm.trans
      ((congrArg (fun z => (idealInclusion i).val.app (op ⊤) z) hab).trans
        (ordinaryPowerSectionValue_inclusion A hd n b))
  · intro s
    let b : Γ(X, ⊤) := (idealInclusion i).val.app (op ⊤) s
    obtain ⟨a, ha⟩ := (ordinaryCoefficients_bijective A hd).2 b
    let t : Γ(idealModule j, ⊤) :=
      (idealPowerNormalizationUnit A hd n).val.app (op ⊤) s
    have htri : (show Γ(Y, ⊤) from (idealInclusion j).val.app (op ⊤) t) = f.appTop b :=
      congrArg (fun z : ordinaryIdealPower A hd n ⟶
        (Modules.pushforward f).obj (originalUnit Y) => z.val.app (op ⊤) s)
        (idealPowerNormalizationUnit_inclusion A hd n)
    have hcoeff : f.appTop (ordinaryCoefficients A hd a) = coefficients A hd a :=
      congrArg (fun φ : A →+* Γ(Y, ⊤) => φ a) (coefficients_nu A hd)
    have hval : coefficients A hd a =
        (show Γ(Y, ⊤) from (idealInclusion j).val.app (op ⊤) t) :=
      hcoeff.symm.trans ((congrArg f.appTop ha).trans htri.symm)
    let z := (idealSectionsEquiv j ⊤).toEquiv t
    have hz : (z : Γ(Y, ⊤)) = coefficients A hd a :=
      (idealSectionsEquiv_val j ⊤ t).trans hval.symm
    have hmem : coefficients A hd a ∈ RingHom.ker j.appTop.hom :=
      (congrArg (fun x : Γ(Y, ⊤) => x ∈ RingHom.ker j.appTop.hom) hz).mp z.property
    have ham : a ∈ IsLocalRing.maximalIdeal A ^ n := by
      rw [← normalizedIdealPower_sectionImage A hd hA hRat n]
      exact hmem
    refine ⟨⟨a, ham⟩, ?_⟩
    apply moduleHom_app_injective (idealInclusion i) ⊤
    exact (ordinaryPowerSectionValue_inclusion A hd n ⟨a, ham⟩).trans ha

/-- The actual ordinary section equivalence, with no chosen copy of its coefficient ring. -/
def ordinaryPowerSectionsEquiv (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (n : ℕ) :
    (IsLocalRing.maximalIdeal A ^ n : Ideal A) ≃ₗ[A] ordinaryPowerSections A hd n :=
  LinearEquiv.ofBijective (ordinaryPowerSectionLinear A hd n)
    (ordinaryPowerSectionLinear_bijective A hd hA hRat n)

/-- The actual restriction of an original scalar power section. -/
def exceptionalPowerSectionMap (hd : ringKrullDim A = 2) (n : ℕ) :
    (IsLocalRing.maximalIdeal A ^ n : Ideal A) →ₗ[A] exceptionalPowerSections A hd n :=
  (((Cohomology.moduleGlobalSectionsFunctorOfHom (source A hd) (ordinaryCoefficients A hd)).map
    (exceptionalPowerSequence A hd n).g).hom).comp (ordinaryPowerSectionLinear A hd n)

omit [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] in
/-- Its values are restriction by the original adjunction unit. -/
theorem exceptionalPowerSectionMap_apply (hd : ringKrullDim A = 2) (n : ℕ)
    (a : ↥(IsLocalRing.maximalIdeal A ^ n)) :
    exceptionalPowerSectionMap A hd n a =
      ((Modules.pullbackPushforwardAdjunction (exceptionalCurveInclusion A hd)).unit.app
        (ordinaryIdealPower A hd n)).val.app (op ⊤) (ordinaryPowerSectionValue A hd n a) :=
  congrArg (fun z => z.val.app (op ⊤) (ordinaryPowerSectionValue A hd n a))
    (exceptionalPowerSequence_g A hd n)

omit [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] in
/-- The original global ideal-product row is exact at the original power sections. -/
theorem exceptionalPowerSequence_global_exact (hd : ringKrullDim A = 2) (n : ℕ) :
    let F := Cohomology.moduleGlobalSectionsFunctorOfHom (source A hd)
      (ordinaryCoefficients A hd)
    ((exceptionalPowerSequence A hd n).map F).Exact := by
  let F := Cohomology.moduleGlobalSectionsFunctorOfHom (source A hd)
    (ordinaryCoefficients A hd)
  let S := exceptionalPowerSequence A hd n
  have hS := exceptionalPowerSequence_shortExact A hd n
  exact hS.exact.map_of_mono_of_preservesKernel F hS.mono_f inferInstance

omit [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] in
/-- Consecutive scalar sections follow the actual original power inclusion. -/
theorem ordinaryPowerSection_transition (hd : ringKrullDim A = 2) (n : ℕ)
    (a : ↥(IsLocalRing.maximalIdeal A ^ (n + 1))) :
    (exceptionalPowerSequence A hd n).f.val.app (op ⊤)
      (ordinaryPowerSectionValue A hd (n + 1) a) =
        ordinaryPowerSectionValue A hd n
          ⟨(a : A), Ideal.pow_le_pow_right (Nat.le_succ n) a.property⟩ := by
  apply moduleHom_app_injective
    (idealInclusion ((exceptionalIdeal A hd) ^ n).subschemeι) ⊤
  have h := congrArg (fun z : ordinaryIdealPower A hd (n + 1) ⟶ originalUnit (source A hd) =>
    z.val.app (op ⊤) (ordinaryPowerSectionValue A hd (n + 1) a))
      (exceptionalPowerSequence_f_inclusion A hd n)
  exact h.trans ((ordinaryPowerSectionValue_inclusion A hd (n + 1) a).trans
    (ordinaryPowerSectionValue_inclusion A hd n
      ⟨(a : A), Ideal.pow_le_pow_right (Nat.le_succ n) a.property⟩).symm)

/-- Restriction kills exactly the original next ideal-power elements. -/
theorem exceptionalPowerSectionMap_eq_zero (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (n : ℕ)
    (a : ↥(IsLocalRing.maximalIdeal A ^ n)) :
    exceptionalPowerSectionMap A hd n a = 0 ↔ (a : A) ∈ IsLocalRing.maximalIdeal A ^ (n + 1) := by
  let S := exceptionalPowerSequence A hd n
  let F := Cohomology.moduleGlobalSectionsFunctorOfHom (source A hd)
    (ordinaryCoefficients A hd)
  constructor
  · intro ha
    obtain ⟨s, hs⟩ := (ShortComplex.moduleCat_exact_iff (S.map F)).mp
      (exceptionalPowerSequence_global_exact A hd n) (ordinaryPowerSectionValue A hd n a) ha
    obtain ⟨b, rfl⟩ := (ordinaryPowerSectionLinear_bijective A hd hA hRat (n + 1)).2 s
    have he := (ordinaryPowerSection_transition A hd n b).symm.trans hs
    have hab := (ordinaryPowerSectionLinear_bijective A hd hA hRat n).1 he
    exact (congrArg Subtype.val hab) ▸ b.property
  · intro ha
    let b : ↥(IsLocalRing.maximalIdeal A ^ (n + 1)) := ⟨(a : A), ha⟩
    have ht := ordinaryPowerSection_transition A hd n b
    have hz := congrArg (fun z : ordinaryIdealPower A hd (n + 1) ⟶
        (Modules.pushforward (exceptionalCurveInclusion A hd)).obj (exceptionalPower A hd n) =>
      z.val.app (op ⊤) (ordinaryPowerSectionValue A hd (n + 1) b)) S.zero
    exact (congrArg (fun x => S.g.val.app (op ⊤) x) ht).symm.trans hz

/-- The kernel is the native denominator m times the nth power module. -/
theorem exceptionalPowerSectionMap_ker (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (n : ℕ) :
    LinearMap.ker (exceptionalPowerSectionMap A hd n) =
      IsLocalRing.maximalIdeal A •
        (⊤ : Submodule A (IsLocalRing.maximalIdeal A ^ n : Ideal A)) := by
  ext a
  change exceptionalPowerSectionMap A hd n a = 0 ↔ _
  exact (exceptionalPowerSectionMap_eq_zero A hd hA hRat n a).trans
    ((exceptionalPowerClass_eq_zero A n a).symm.trans (Submodule.Quotient.mk_eq_zero _))

/-- All exceptional power sections are restrictions of original scalar power sections. -/
theorem exceptionalPowerSectionMap_surjective (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (n : ℕ) :
    Function.Surjective (exceptionalPowerSectionMap A hd n) :=
  (exceptionalPowerSequence_global_surjective A hd hA hRat n).comp
    (ordinaryPowerSectionLinear_bijective A hd hA hRat n).2

/-- The quotient section equivalence for the original structural A-action. -/
def exceptionalPowerThetaA (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (n : ℕ) :
    exceptionalPowerLayer A n ≃ₗ[A] exceptionalPowerSections A hd n :=
  (Submodule.quotEquivOfEq _ _ (exceptionalPowerSectionMap_ker A hd hA hRat n).symm).trans
    ((exceptionalPowerSectionMap A hd n).quotKerEquivOfSurjective
      (exceptionalPowerSectionMap_surjective A hd hA hRat n))

/-- The same quotient section map is linear over the original residue field. -/
def exceptionalPowerTheta (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (n : ℕ) :
    exceptionalPowerLayer A n ≃ₗ[A ⧸ IsLocalRing.maximalIdeal A]
      exceptionalPowerSections A hd n :=
  LinearEquiv.ofBijective
    ((exceptionalPowerThetaA A hd hA hRat n).toLinearMap.extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective)
    (exceptionalPowerThetaA A hd hA hRat n).bijective

/-- The residue-linear equivalence sends every original class to its original restricted section. -/
theorem exceptionalPowerTheta_class (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (n : ℕ)
    (a : ↥(IsLocalRing.maximalIdeal A ^ n)) :
    exceptionalPowerTheta A hd hA hRat n (exceptionalPowerClass A n a) =
      ((Modules.pullbackPushforwardAdjunction (exceptionalCurveInclusion A hd)).unit.app
        (ordinaryIdealPower A hd n)).val.app (op ⊤) (ordinaryPowerSectionValue A hd n a) := by
  change exceptionalPowerThetaA A hd hA hRat n (Submodule.Quotient.mk a) = _
  exact exceptionalPowerSectionMap_apply A hd n a


omit [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] in
/-- The original zeroth-power comparison is the original ideal inclusion. -/
theorem ordinaryPowerZeroIso_hom (hd : ringKrullDim A = 2) :
    (ordinaryPowerZeroIso A hd).hom =
      idealInclusion ((exceptionalIdeal A hd) ^ 0).subschemeι := rfl

/-- The uniform quotient maps recover the already constructed original residue-field map. -/
theorem exceptionalPowerTheta_zero (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (a : A) :
    (exceptionalPowerZeroIso A hd).hom.val.app (op ⊤)
      (exceptionalPowerTheta A hd hA hRat 0
        (exceptionalPowerClass A 0 ⟨a, by simp⟩)) =
      exceptionalCoefficientsEquiv A hd hA hRat
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a) := by
  let X := source A hd
  let E := exceptionalCurve A hd
  let i := exceptionalCurveInclusion A hd
  let adj := Modules.pullbackPushforwardAdjunction i
  let e := ordinaryPowerZeroIso A hd
  let u := pullbackUnitIso i
  let a₀ : ↥(IsLocalRing.maximalIdeal A ^ 0) := ⟨a, by simp⟩
  let s := ordinaryPowerSectionValue A hd 0 a₀
  have hn := congrArg (fun z : ordinaryIdealPower A hd 0 ⟶
      (Modules.pushforward i).obj ((Modules.pullback i).obj (originalUnit X)) =>
    z.val.app (op ⊤) s) (adj.unit.naturality e.hom).symm
  have hu : adj.unit.app (originalUnit X) ≫ (Modules.pushforward i).map u.hom =
      structureModuleMap i :=
    (adj.homEquiv_unit (originalUnit X) (originalUnit E) u.hom).symm.trans
      (pullbackUnitIso_homEquiv i)
  have huv := congrArg (fun z : originalUnit X ⟶
      (Modules.pushforward i).obj (originalUnit E) =>
    z.val.app (op ⊤) (e.hom.val.app (op ⊤) s)) hu
  have hs : (show Γ(X, ⊤) from e.hom.val.app (op ⊤) s) = ordinaryCoefficients A hd a :=
    (congrArg (fun z : ordinaryIdealPower A hd 0 ⟶ originalUnit X => z.val.app (op ⊤) s)
      (ordinaryPowerZeroIso_hom A hd)).trans (ordinaryPowerSectionValue_inclusion A hd 0 a₀)
  have hθ := exceptionalPowerTheta_class A hd hA hRat 0 a₀
  exact (congrArg (fun z => (exceptionalPowerZeroIso A hd).hom.val.app (op ⊤) z) hθ).trans
    ((congrArg (fun z => u.hom.val.app (op ⊤) z) hn).trans
      (huv.trans ((congrArg i.appTop hs).trans (exceptionalCoefficients_quotient A hd a).symm)))

/-- The original native Cartier multiplication of arbitrary original powers. -/
def ordinaryPowerProductIso (hd : ringKrullDim A = 2) (n m : ℕ) :
    tensorSheaf (source A hd) (ordinaryIdealPower A hd n) (ordinaryIdealPower A hd m) ≅
      ordinaryIdealPower A hd (n + m) := by
  let i := ((exceptionalIdeal A hd) ^ n).subschemeι
  let j := ((exceptionalIdeal A hd) ^ m).subschemeι
  let e := idealProductIso i j (ordinaryIdealPower_locallyRankOne A hd n)
  have h : (i.ker * j.ker).subschemeι.ker =
      ((exceptionalIdeal A hd) ^ (n + m)).subschemeι.ker := by
    simp only [i, j, Scheme.IdealSheafData.ker_subschemeι, pow_add]
  exact e ≪≫ Surfaces.Contraction.FormalNeighborhood.idealModuleIsoOfKernelEq _ _ h

omit [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] in
/-- Product inclusion is the original multiplication into the original structure sheaf. -/
theorem ordinaryPowerProductIso_inclusion (hd : ringKrullDim A = 2) (n m : ℕ) :
    (ordinaryPowerProductIso A hd n m).hom ≫
      idealInclusion ((exceptionalIdeal A hd) ^ (n + m)).subschemeι =
        Cartier.idealMultiplication ((exceptionalIdeal A hd) ^ n).subschemeι
          ((exceptionalIdeal A hd) ^ m).subschemeι := by
  let i := ((exceptionalIdeal A hd) ^ n).subschemeι
  let j := ((exceptionalIdeal A hd) ^ m).subschemeι
  let e := idealProductIso i j (ordinaryIdealPower_locallyRankOne A hd n)
  have h : (i.ker * j.ker).subschemeι.ker =
      ((exceptionalIdeal A hd) ^ (n + m)).subschemeι.ker := by
    simp only [i, j, Scheme.IdealSheafData.ker_subschemeι, pow_add]
  let c := Surfaces.Contraction.FormalNeighborhood.idealModuleIsoOfKernelEq _ _ h
  exact compose_iso_inclusions e c _ _ _
    (Surfaces.Contraction.FormalNeighborhood.idealModuleIsoOfKernelEq_hom_inclusion _ _ h)
    (idealProductIso_hom_inclusion i j (ordinaryIdealPower_locallyRankOne A hd n))

/-- Multiplication on the full exceptional fibre is the pullback of this original product. -/
def exceptionalPowerProduct (hd : ringKrullDim A = 2) (n m : ℕ) :
    tensorSheaf (exceptionalCurve A hd) (exceptionalPower A hd n) (exceptionalPower A hd m) ⟶
      exceptionalPower A hd (n + m) :=
  Pullback.Tensor.pullbackTensorInverse (exceptionalCurveInclusion A hd)
      (ordinaryIdealPower A hd n) (ordinaryIdealPower A hd m) ≫
    (Modules.pullback (exceptionalCurveInclusion A hd)).map
      (ordinaryPowerProductIso A hd n m).hom

/-- The product of original exceptional sections, before any graded-ring packaging. -/
def exceptionalPowerSectionProduct (hd : ringKrullDim A = 2) (n m : ℕ)
    (s : exceptionalPowerSections A hd n) (t : exceptionalPowerSections A hd m) :
    exceptionalPowerSections A hd (n + m) :=
  (exceptionalPowerProduct A hd n m).val.app (op ⊤)
    (moduleTensorSection (exceptionalCurve A hd) (exceptionalPower A hd n)
      (exceptionalPower A hd m) ⊤ s t)

private theorem pullback_product_global {X E : Scheme.{u}} (i : E ⟶ X)
    {M N P : X.Modules} (π : tensorSheaf X M N ⟶ P) (s : Γ(M, ⊤)) (t : Γ(N, ⊤)) :
    (Pullback.Tensor.pullbackTensorInverse i M N ≫ (Modules.pullback i).map π).val.app (op ⊤)
      (moduleTensorSection E ((Modules.pullback i).obj M) ((Modules.pullback i).obj N) ⊤
        (((Modules.pullbackPushforwardAdjunction i).unit.app M).val.app (op ⊤) s)
        (((Modules.pullbackPushforwardAdjunction i).unit.app N).val.app (op ⊤) t)) =
      ((Modules.pullbackPushforwardAdjunction i).unit.app P).val.app (op ⊤)
        (π.val.app (op ⊤) (moduleTensorSection X M N ⊤ s t)) := by
  let F := Modules.pullback i
  let G := Modules.pushforward i
  let adj := Modules.pullbackPushforwardAdjunction i
  let c := pullbackTensorMap i M N
  let d := Pullback.Tensor.pullbackTensorInverse i M N
  let z := moduleTensorSection X M N ⊤ s t
  have hu : adj.unit.app (tensorSheaf X M N) ≫ G.map c =
      tensorSheafMap X (adj.unit.app M) (adj.unit.app N) ≫
        pushforwardTensorMap i (F.obj M) (F.obj N) :=
    (adj.homEquiv_unit _ _ c).symm.trans (pullbackTensorMap_adjoint i M N)
  have h₀ := congrArg (fun q : tensorSheaf X M N ⟶
      G.obj (tensorSheaf E (F.obj M) (F.obj N)) =>
    q.val.app (op ⊤) z) hu
  have h₁ := congrArg (fun q =>
      (pushforwardTensorMap i (F.obj M) (F.obj N)).val.app (op ⊤) q)
    (tensorSheafMap_tmul X (adj.unit.app M) (adj.unit.app N) (op ⊤) s t)
  have h₂ := pushforwardTensorMap_tmul i (F.obj M) (F.obj N) (op ⊤)
    ((adj.unit.app M).val.app (op ⊤) s) ((adj.unit.app N).val.app (op ⊤) t)
  have hc := congrArg (fun q : F.obj (tensorSheaf X M N) ⟶
      F.obj (tensorSheaf X M N) =>
    q.val.app (op ⊤) ((adj.unit.app (tensorSheaf X M N)).val.app (op ⊤) z))
      (Pullback.Tensor.pullbackTensorMap_inverse i M N)
  have hd := (congrArg (fun q => d.val.app (op ⊤) q) (h₀.trans (h₁.trans h₂))).symm.trans hc
  have hn := congrArg (fun q : tensorSheaf X M N ⟶ G.obj (F.obj P) =>
    q.val.app (op ⊤) z) (adj.unit.naturality π)
  exact (congrArg (fun q => (F.map π).val.app (op ⊤) q) hd).trans hn.symm

omit [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] in
/-- Original scalar power sections multiply to the original scalar product section. -/
theorem ordinaryPowerSectionValue_product (hd : ringKrullDim A = 2) (n m : ℕ)
    (a : ↥(IsLocalRing.maximalIdeal A ^ n)) (b : ↥(IsLocalRing.maximalIdeal A ^ m)) :
    (ordinaryPowerProductIso A hd n m).hom.val.app (op ⊤)
      (moduleTensorSection (source A hd) (ordinaryIdealPower A hd n)
        (ordinaryIdealPower A hd m) ⊤ (ordinaryPowerSectionValue A hd n a)
          (ordinaryPowerSectionValue A hd m b)) =
      ordinaryPowerSectionValue A hd (n + m)
        ⟨(a : A) * b, by rw [pow_add]; exact Ideal.mul_mem_mul a.property b.property⟩ := by
  let X := source A hd
  let i := ((exceptionalIdeal A hd) ^ n).subschemeι
  let j := ((exceptionalIdeal A hd) ^ m).subschemeι
  let k := ((exceptionalIdeal A hd) ^ (n + m)).subschemeι
  let s := ordinaryPowerSectionValue A hd n a
  let t := ordinaryPowerSectionValue A hd m b
  apply moduleHom_app_injective (idealInclusion k) ⊤
  have h₀ := congrArg (fun q : tensorSheaf X (idealModule i) (idealModule j) ⟶ originalUnit X =>
    q.val.app (op ⊤) (moduleTensorSection X (idealModule i) (idealModule j) ⊤ s t))
      (ordinaryPowerProductIso_inclusion A hd n m)
  have h₁ := idealMultiplication_section i j ⊤ s t
  have h₂ := congrArg₂ (fun x y : Γ(X, ⊤) => x * y)
    (ordinaryPowerSectionValue_inclusion A hd n a)
    (ordinaryPowerSectionValue_inclusion A hd m b)
  exact h₀.trans (h₁.trans (h₂.trans
    ((map_mul (ordinaryCoefficients A hd) (a : A) (b : A)).symm.trans
      (ordinaryPowerSectionValue_inclusion A hd (n + m)
        ⟨(a : A) * b, by rw [pow_add]; exact Ideal.mul_mem_mul a.property b.property⟩).symm)))

/-- The quotient equivalences preserve the original product on every original representative. -/
theorem exceptionalPowerTheta_product (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (n m : ℕ)
    (a : ↥(IsLocalRing.maximalIdeal A ^ n)) (b : ↥(IsLocalRing.maximalIdeal A ^ m)) :
    exceptionalPowerSectionProduct A hd n m
      (exceptionalPowerTheta A hd hA hRat n (exceptionalPowerClass A n a))
      (exceptionalPowerTheta A hd hA hRat m (exceptionalPowerClass A m b)) =
    exceptionalPowerTheta A hd hA hRat (n + m)
      (exceptionalPowerClass A (n + m)
        ⟨(a : A) * b, by rw [pow_add]; exact Ideal.mul_mem_mul a.property b.property⟩) := by
  let i := exceptionalCurveInclusion A hd
  have h₀ := congrArg₂ (exceptionalPowerSectionProduct A hd n m)
    (exceptionalPowerTheta_class A hd hA hRat n a)
    (exceptionalPowerTheta_class A hd hA hRat m b)
  have h₁ := pullback_product_global i (ordinaryPowerProductIso A hd n m).hom
    (ordinaryPowerSectionValue A hd n a) (ordinaryPowerSectionValue A hd m b)
  have h₂ := congrArg (fun s => ((Modules.pullbackPushforwardAdjunction i).unit.app
      (ordinaryIdealPower A hd (n + m))).val.app (op ⊤) s)
    (ordinaryPowerSectionValue_product A hd n m a b)
  exact h₀.trans (h₁.trans (h₂.trans
    (exceptionalPowerTheta_class A hd hA hRat (n + m)
      ⟨(a : A) * b, by rw [pow_add]; exact Ideal.mul_mem_mul a.property b.property⟩).symm))

end AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup
