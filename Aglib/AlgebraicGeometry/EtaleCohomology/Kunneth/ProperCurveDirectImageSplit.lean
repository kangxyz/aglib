/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.PairingBiproduct
public import Aglib.Algebra.Homology.DerivedCategory.Plus.ExtTransport
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure
public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.FieldDirectImageCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.DerivedFreeSplit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.ProperCurveCoordinates
public import Mathlib.LinearAlgebra.StdBasis

public import Aglib.CategoryTheory.Shift.AdjunctValue

/-! Graded splitting of the original proper curve constant direct image. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

open Scheme.OverField Scheme.OverField.Curve

universe u wS wX wE

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- The indices of the proper-curve cohomology basis in degrees zero through two. -/
abbrev ProperCurveGradeIndex (genus : ℕ) :=
  Σ q : Fin 3, Fin (properCurveConstantRank genus q.val)

/-- The integer cohomological degree of a proper-curve basis index. -/
def properCurveGradeDegree {genus : ℕ} (i : ProperCurveGradeIndex genus) : ℤ :=
  (i.1.val : ℤ)

private theorem properCurveConstantRank_eq_zero {g q : ℕ} (h : 3 ≤ q) :
    properCurveConstantRank g q = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm]
  rfl

private def properCurveGradeFiber (genus q : ℕ) :
    Fin (properCurveConstantRank genus q) ≃
      { i : ProperCurveGradeIndex genus // properCurveGradeDegree i = (q : ℤ) } := by
  by_cases h : q < 3
  · let i : Fin 3 := ⟨q, h⟩
    refine Equiv.ofBijective (fun x => ⟨⟨i, x⟩, rfl⟩) ⟨?_, ?_⟩
    · intro a b hab
      exact eq_of_heq (Sigma.mk.inj (congrArg Subtype.val hab)).2
    · rintro ⟨⟨j, x⟩, hj⟩
      have hj' : j = i := by
        apply Fin.ext
        change (j.val : ℤ) = (q : ℤ) at hj
        exact_mod_cast hj
      subst j
      exact ⟨x, rfl⟩
  · let : IsEmpty (Fin (properCurveConstantRank genus q)) := by
      rw [properCurveConstantRank_eq_zero (by omega : 3 ≤ q)]
      infer_instance
    let : IsEmpty { i : ProperCurveGradeIndex genus // properCurveGradeDegree i = (q : ℤ) } :=
      ⟨fun ⟨i, hi⟩ => by
        change (i.1.val : ℤ) = (q : ℤ) at hi
        have := i.1.isLt
        omega⟩
    exact Equiv.equivOfIsEmpty _ _

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  [HasDerivedCategory.{wS} (ModuleSheaf (Base k) (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wE} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]

/-- The original proper curve direct image of the native coefficient unit. -/
abbrev properCurveConstantDirectImage :
    DerivedCategory.Plus (ModuleSheaf (Base k) (ULift.{u + 1} (ZMod n))) :=
  let Λ := ULift.{u + 1} (ZMod n)
  (moduleDerivedDirectImage Λ X.hom).obj
    ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X.left Λ) 0).obj (moduleUnit X.left Λ))

/-- Sections of the homogeneous component of the same original direct image. -/
abbrev properCurveConstantDirectImageSections (q : ℤ) :
    ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)) :=
  let Λ := ULift.{u + 1} (ZMod n)
  (moduleGlobalSections (Base k) Λ).obj
    ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf (Base k) Λ) q).obj
      (properCurveConstantDirectImage (X := X) n))

/-- The coordinates of the original Ext transport to the actual proper direct image. -/
@[no_expose]
def properCurveConstantDirectImageSectionsLinearEquiv (q : ℕ) :
    let Λ := ULift.{u + 1} (ZMod n)
    (properCurveConstantDirectImageSections (X := X) n q) ≃ₗ[Λ]
      (Fin (properCurveConstantRank (coherentGenus k X) q) → Λ) := by
  let R := ZMod n
  let Λ := ULift.{u + 1} R
  let Z := properCurveConstantDirectImageSections (X := X) n q
  let I := Fin (properCurveConstantRank (coherentGenus k X) q)
  let e := (moduleFieldDirectImageHomologyAddEquiv k X.hom n
    (moduleUnit X.left Λ) q).symm.trans (properCurveConstantModuleExtAddEquiv hX n hn hunit q)
  let e' : Z ≃+ (I → Λ) :=
    e.trans (AddEquiv.piCongrRight (fun _ => AddEquiv.ulift.symm))
  let : Module Λ Z := Z.isModule
  let : Module R Z := Module.compHom Z (ULift.ringEquiv.symm : R ≃+* Λ).toRingHom
  let : Module R (I → Λ) :=
    Module.compHom (I → Λ) (ULift.ringEquiv.symm : R ≃+* Λ).toRingHom
  refine { e' with map_smul' := fun a z => ?_ }
  have h := (e'.toAddMonoidHom.toZModLinearMap n).map_smul a.down z
  exact h

/-- The original proper-curve degree table gives a basis of the actual direct-image sections. -/
@[no_expose]
def properCurveConstantDirectImageSectionsBasis (q : ℕ) :
    Module.Basis (Fin (properCurveConstantRank (coherentGenus k X) q))
      (ULift.{u + 1} (ZMod n)) (properCurveConstantDirectImageSections (X := X) n q) :=
  (Pi.basisFun _ _).map (properCurveConstantDirectImageSectionsLinearEquiv hX n hn hunit q).symm

omit [IsAlgClosed k] [HasExt (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))] in
/-- The original proper direct image of a degree-zero unit has no negative cohomology. -/
theorem properCurveConstantDirectImageSections_subsingleton_of_neg (q : ℤ) (hq : q < 0) :
    Subsingleton (properCurveConstantDirectImageSections (X := X) n q) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let F := moduleDirectImage X.hom Λ
  let K := (DerivedCategory.Plus.singleFunctor (ModuleSheaf X.left Λ) 0).obj (moduleUnit X.left Λ)
  let h := F.isZero_homology_rightDerivedFunctorPlus_of_isGE K 0 q hq
  exact ModuleCat.isZero_iff_subsingleton.mp ((moduleGlobalSections (Base k) Λ).map_isZero h)


/-- A basis in every integer degree of the original proper curve direct image. -/
@[no_expose]
def properCurveConstantDirectImageGradedBasis (q : ℤ) :
    Module.Basis {i : ProperCurveGradeIndex (coherentGenus k X) // properCurveGradeDegree i = q}
      (ULift.{u + 1} (ZMod n)) (properCurveConstantDirectImageSections (X := X) n q) := by
  by_cases hq : q < 0
  · let : Subsingleton (properCurveConstantDirectImageSections (X := X) n q) :=
      properCurveConstantDirectImageSections_subsingleton_of_neg (X := X) n q hq
    let : IsEmpty {i : ProperCurveGradeIndex (coherentGenus k X) // properCurveGradeDegree i = q} :=
      ⟨fun ⟨i, hi⟩ => by
        change (i.1.val : ℤ) = q at hi
        omega⟩
    exact Module.Basis.empty _
  · let m := q.toNat
    have hm : (m : ℤ) = q := Int.toNat_of_nonneg (le_of_not_gt hq)
    have b := (properCurveConstantDirectImageSectionsBasis hX n hn hunit m).reindex
      (properCurveGradeFiber (coherentGenus k X) m)
    exact hm ▸ b

/-- The selected bases split the original proper direct image into the original
shifted units by the original inverse unit evaluation on each basis vector. -/
@[no_expose]
def properCurveConstantDirectImageSplitIso :=
  let Λ := ULift.{u + 1} (ZMod n)
  let d : ProperCurveGradeIndex (coherentGenus k X) → ℤ := properCurveGradeDegree
  let K := properCurveConstantDirectImage (X := X) n
  let b := properCurveConstantDirectImageGradedBasis hX n hn hunit
  letI : IsIso (moduleFieldDerivedFreeSplitMap k Λ d K b) :=
    moduleFieldDerivedFreeSplitMap_isIso k Λ d K b
  asIso (moduleFieldDerivedFreeSplitMap k Λ d K b)

/-- The proper-curve splitting has the original graded basis map as its forward arrow. -/
theorem properCurveConstantDirectImageSplitIso_hom :
    let Λ := ULift.{u + 1} (ZMod n)
    let d : ProperCurveGradeIndex (coherentGenus k X) → ℤ := properCurveGradeDegree
    (properCurveConstantDirectImageSplitIso hX n hn hunit).hom =
      moduleFieldDerivedFreeSplitMap k Λ d (properCurveConstantDirectImage (X := X) n)
        (properCurveConstantDirectImageGradedBasis hX n hn hunit) := by
  unfold properCurveConstantDirectImageSplitIso
  rfl

section ExtBasis

attribute [local instance] moduleSheafExtZModModule

/-- The original proper-curve classes forming the selected graded basis. -/
@[no_expose]
def properCurveConstantModuleExtBasis (q : ℕ) :
    Module.Basis (Fin (properCurveConstantRank (coherentGenus k X) q))
      (ZMod n) (constantModuleExt.{u, wE} n X.left q) :=
  (Pi.basisFun _ _).map
    (AddEquiv.toZModLinearEquiv n (properCurveConstantModuleExtAddEquiv hX n hn hunit q)).symm

omit [HasDerivedCategory (ModuleSheaf (Base k) (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))] in
/-- The basis class is the inverse of the original proper-curve coordinate map on a unit vector. -/
theorem properCurveConstantModuleExtBasis_apply (q : ℕ)
    (i : Fin (properCurveConstantRank (coherentGenus k X) q)) :
    properCurveConstantModuleExtBasis hX n hn hunit q i =
      (properCurveConstantModuleExtAddEquiv hX n hn hunit q).symm (Pi.single i 1) := by
  unfold properCurveConstantModuleExtBasis
  rw [Module.Basis.map_apply, Pi.basisFun_apply]
  rfl

/-- The original direct-image basis is the transport of the original Ext basis. -/
theorem properCurveConstantDirectImageSectionsBasis_eq_extBasis (q : ℕ)
    (i : Fin (properCurveConstantRank (coherentGenus k X) q)) :
    properCurveConstantDirectImageSectionsBasis hX n hn hunit q i =
      moduleFieldDirectImageHomologyAddEquiv k X.hom n
        (moduleUnit X.left (ULift.{u + 1} (ZMod n))) q
        (properCurveConstantModuleExtBasis hX n hn hunit q i) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let e := moduleFieldDirectImageHomologyAddEquiv k X.hom n (moduleUnit X.left Λ) q
  let b := properCurveConstantModuleExtAddEquiv hX n hn hunit q
  apply (properCurveConstantDirectImageSectionsLinearEquiv hX n hn hunit q).injective
  unfold properCurveConstantDirectImageSectionsBasis
  rw [Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply,
    properCurveConstantModuleExtBasis_apply]
  unfold properCurveConstantDirectImageSectionsLinearEquiv
  change (Pi.single i (1 : Λ)) =
    (AddEquiv.piCongrRight (fun _ => AddEquiv.ulift.symm))
      (b (e.symm (e (b.symm (Pi.single i 1)))))
  rw [e.symm_apply_apply, b.apply_symm_apply]
  funext j
  by_cases h : j = i
  · subst j
    simp [Pi.single_eq_same]
    rfl
  · simp [Pi.single_eq_of_ne h]

private theorem properCurveGradeFiber_at_index {genus : ℕ} (i : ProperCurveGradeIndex genus) :
    properCurveGradeFiber genus i.1.val i.2 = ⟨i, rfl⟩ := by
  obtain ⟨q, a⟩ := i
  unfold properCurveGradeFiber
  rw [dite_eq_left q.isLt]
  rfl

/-- The full original graded basis uses the original Ext class at each actual index. -/
theorem properCurveConstantDirectImageGradedBasis_at_index
    (i : ProperCurveGradeIndex (coherentGenus k X)) :
    properCurveConstantDirectImageGradedBasis hX n hn hunit
        (properCurveGradeDegree i) ⟨i, rfl⟩ =
      moduleFieldDirectImageHomologyAddEquiv k X.hom n
        (moduleUnit X.left (ULift.{u + 1} (ZMod n))) i.1.val
          (properCurveConstantModuleExtBasis hX n hn hunit i.1.val i.2) := by
  let q := i.1.val
  have hq : ¬ properCurveGradeDegree i < 0 := by
    change ¬ (q : ℤ) < 0
    omega
  unfold properCurveConstantDirectImageGradedBasis
  rw [dite_eq_right hq]
  change ((properCurveConstantDirectImageSectionsBasis hX n hn hunit q).reindex
      (properCurveGradeFiber (coherentGenus k X) q)) ⟨i, rfl⟩ = _
  rw [Module.Basis.reindex_apply, ← properCurveGradeFiber_at_index i, Equiv.symm_apply_apply]
  exact properCurveConstantDirectImageSectionsBasis_eq_extBasis hX n hn hunit q i.2

/-- The field splitting component is the shifted adjunct of the original Ext basis class. -/
theorem properCurveConstantDirectImageSplitComponent_hom_value
    (i : ProperCurveGradeIndex (coherentGenus k X)) :
    let Λ := ULift.{u + 1} (ZMod n)
    let S := Base k
    let D := ModuleSheaf S Λ
    let I := moduleUnit S Λ
    let K := properCurveConstantDirectImage (X := X) n
    let F := moduleInverseImage X.hom Λ
    let q := i.1.val
    let u := F.rightDerivedFunctorPlusSingleIsoOfIso 0 (moduleUnitInverseImageIso X.hom n)
    let t := ((DerivedCategory.Plus.singleFunctors D).shiftIso (-(q : ℤ)) (q : ℤ) 0
      (by omega)).app I
    RegradedComponentValue (moduleDerivedAdjunction Λ X.hom) u t
      (properCurveConstantModuleExtBasis hX n hn hunit q i.2).homPlus
      (moduleFieldDerivedFreeSplitComponent k Λ properCurveGradeDegree K
        (properCurveConstantDirectImageGradedBasis hX n hn hunit) i) := by
  dsimp only [RegradedComponentValue]
  let Λ := ULift.{u + 1} (ZMod n)
  let K := properCurveConstantDirectImage (X := X) n
  let q := i.1.val
  let y := properCurveConstantModuleExtBasis hX n hn hunit q i.2
  let e := moduleFieldDirectImageHomologyAddEquiv k X.hom n (moduleUnit X.left Λ) q
  unfold moduleFieldDerivedFreeSplitComponent
  rw [properCurveConstantDirectImageGradedBasis_at_index]
  exact (moduleFieldDerivedUnitHomologyAddEquiv_symm_apply k Λ (q : ℤ) K (e y)).symm.trans
    (moduleFieldDirectImageHomologyAddEquiv_hom_value k X.hom n (moduleUnit X.left Λ) q y)

end ExtBasis

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
