/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Koszul.Ext.Quotient
public import Aglib.RingTheory.RegularLocalRing.FiniteLengthExt
public import Aglib.RingTheory.RegularLocalRing.FiniteProjectiveDimension
public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.RingTheory.Length

/-!
# Exact and faithful Ext-two on finite-length surface modules

Over a regular local ring of dimension two, native Ext into the ring is
concentrated in degree two on finite-length modules. Original Yoneda
precomposition is exact in that degree and preserves length. The residue-field
calculation is the original Koszul top-class comparison. Zero detection and
faithfulness follow without constructing biduality or an injective hull.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Abelian IsLocalRing

namespace IsRegularLocalRing

variable (R : Type u) [CommRing R]

/-- The actual native Ext-two group, with its original coefficient action. -/
abbrev extDualTwo (M : ModuleCat.{u} R) : Type u :=
  Ext M (ModuleCat.of R R) 2

/-- The contravariant map is original Yoneda precomposition. -/
def extDualTwoMap {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    extDualTwo R N →ₗ[R] extDualTwo R M :=
  (Ext.mk₀ f).precompOfLinear R (ModuleCat.of R R) (zero_add 2)

@[simp]
theorem extDualTwoMap_apply {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (x : extDualTwo R N) :
    extDualTwoMap R f x = (Ext.mk₀ f).comp x (zero_add 2) := rfl

@[simp]
theorem extDualTwoMap_id (M : ModuleCat.{u} R) :
    extDualTwoMap R (𝟙 M) = LinearMap.id := by
  ext x
  exact Ext.mk₀_id_comp x

theorem extDualTwoMap_comp {M N P : ModuleCat.{u} R} (f : M ⟶ N) (g : N ⟶ P) :
    (extDualTwoMap R f).comp (extDualTwoMap R g) = extDualTwoMap R (f ≫ g) := by
  ext x
  exact Ext.mk₀_comp_mk₀_assoc f g x

/-- Precomposition is linear in the original module morphism. -/
def extDualTwoMapLinear (M N : ModuleCat.{u} R) :
    (M ⟶ N) →ₗ[R] (extDualTwo R N →ₗ[R] extDualTwo R M) where
  toFun := extDualTwoMap R
  map_add' f g := by
    ext x
    change (Ext.mk₀ (f + g)).comp x (zero_add 2) =
      (Ext.mk₀ f).comp x (zero_add 2) + (Ext.mk₀ g).comp x (zero_add 2)
    rw [Ext.mk₀_add, Ext.add_comp]
  map_smul' r f := by
    ext x
    change (Ext.mk₀ (r • f)).comp x (zero_add 2) =
      r • (Ext.mk₀ f).comp x (zero_add 2)
    rw [Ext.mk₀_smul, Ext.smul_comp]

/-- Source isomorphisms act through the same native precomposition maps. -/
def extDualTwoCongr {M N : ModuleCat.{u} R} (e : M ≅ N) :
    extDualTwo R N ≃ₗ[R] extDualTwo R M where
  toLinearMap := extDualTwoMap R e.hom
  invFun := extDualTwoMap R e.inv
  left_inv x := by
    change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp x (zero_add 2)) (zero_add 2) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]
  right_inv x := by
    change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp x (zero_add 2)) (zero_add 2) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]

private def extDegreeCongr (M N : ModuleCat.{u} R) (i j : ℕ) (h : i = j) :
    Ext M N i ≃ₗ[R] Ext M N j := by
  subst j
  exact LinearEquiv.refl R _

variable [IsRegularLocalRing R] (hd : ringKrullDim R = (2 : ℕ))

include hd

/-- Native Ext into a regular local surface ring vanishes away from degree
two on every finite-length source. -/
theorem subsingleton_ext_of_isFiniteLength_ne_two (M : ModuleCat.{u} R)
    (hM : IsFiniteLength R M) (i : ℕ) (hi : i ≠ 2) :
    Subsingleton (Ext M (ModuleCat.of R R) i) := by
  by_cases hilow : i < 2
  · exact subsingleton_ext_of_isFiniteLength R M hM 2 hd i hilow
  · let : IsNoetherian R M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
    let : HasProjectiveDimensionLE M 2 := (projectiveDimension_le_iff M 2).mp
      (projectiveDimension_le_dimension 2 R hd M)
    exact HasProjectiveDimensionLT.subsingleton M 3 i (by omega) (ModuleCat.of R R)

/-- A finite-length short exact row gives an exact reversed Ext-two row,
with the actual original precomposition maps and both endpoint conditions. -/
theorem extDualTwo_exact (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (h₁ : IsFiniteLength R S.X₁) (h₃ : IsFiniteLength R S.X₃) :
    Function.Injective (extDualTwoMap R S.g) ∧
      Function.Exact (extDualTwoMap R S.g) (extDualTwoMap R S.f) ∧
      Function.Surjective (extDualTwoMap R S.f) := by
  let T := ModuleCat.of R R
  let : Subsingleton (Ext S.X₁ T 1) :=
    subsingleton_ext_of_isFiniteLength_ne_two R hd S.X₁ h₁ 1 (by decide)
  let : Subsingleton (Ext S.X₃ T 3) :=
    subsingleton_ext_of_isFiniteLength_ne_two R hd S.X₃ h₃ 3 (by decide)
  refine ⟨?_, ?_, ?_⟩
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₃ hS T x hx (n₀ := 1) rfl
    simpa only [Subsingleton.elim y 0, Ext.comp_zero] using hy.symm
  · intro x
    constructor
    · intro hx
      exact Ext.contravariant_sequence_exact₂ hS T x hx
    · rintro ⟨y, rfl⟩
      change (Ext.mk₀ S.f).comp ((Ext.mk₀ S.g).comp y (zero_add 2)) (zero_add 2) = 0
      rw [Ext.mk₀_comp_mk₀_assoc, S.zero, Ext.mk₀_zero, Ext.zero_comp]
  · intro x
    exact Ext.contravariant_sequence_exact₁ hS T x (n₁ := 3) rfl
      (Subsingleton.elim _ _)

/-- The actual Koszul top class identifies the residue field with Ext-two
after restriction to the original coefficient ring. -/
theorem nonempty_residueField_extDualTwo_linearEquiv :
    Nonempty (ResidueField R ≃ₗ[R] extDualTwo R (ModuleCat.of R (ResidueField R))) := by
  obtain ⟨rs, hlen, hreg, hspan⟩ := exists_regular_sequence_maximalIdeal R 2 hd
  let := Ext.quotientSourceModule (Ideal.ofList rs) (ModuleCat.of R R) rs.length
  let : IsScalarTower R (R ⧸ Ideal.ofList rs)
      (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (ModuleCat.of R R) rs.length) :=
    Module.IsTorsionBySet.isScalarTower
      (Ext.quotientSourceIsTorsionBySet (Ideal.ofList rs) (ModuleCat.of R R) rs.length)
  let e := (ChainComplex.Koszul.topExtRingQuotientLinearEquiv.{u,u}
    rs hreg.toIsWeaklyRegular).restrictScalars R
  let q : (R ⧸ Ideal.ofList rs) ≃ₗ[R] ResidueField R :=
    Submodule.quotEquivOfEq _ _ hspan
  let eDegree := extDegreeCongr R (ModuleCat.of R (R ⧸ Ideal.ofList rs))
    (ModuleCat.of R R) rs.length 2 hlen
  exact ⟨q.symm.trans (e.trans (eDegree.trans (extDualTwoCongr R q.toModuleIso).symm))⟩

private theorem length_extDualTwo_of_isSimple (M : Type u) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] : Module.length R (extDualTwo R (ModuleCat.of R M)) = 1 := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
    (inferInstance : IsSimpleModule R M)
  have hIm : I = maximalIdeal R := IsLocalRing.eq_maximalIdeal hI
  subst I
  let eM : ModuleCat.of R M ≅ ModuleCat.of R (ResidueField R) := e.toModuleIso
  obtain ⟨eK⟩ := nonempty_residueField_extDualTwo_linearEquiv R hd
  let : IsSimpleModule R (ResidueField R) := by
    change IsSimpleModule R (R ⧸ maximalIdeal R)
    exact (isSimpleModule_iff_isCoatom (R := R) (M := R)
      (m := (maximalIdeal R : Submodule R R))).mpr
        (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal R))
  calc
    Module.length R (extDualTwo R (ModuleCat.of R M)) =
        Module.length R (extDualTwo R (ModuleCat.of R (ResidueField R))) :=
      (extDualTwoCongr R eM).length_eq.symm
    _ = Module.length R (ResidueField R) := eK.length_eq.symm
    _ = 1 := Module.length_eq_one R (ResidueField R)

/-- Ext-two preserves the original R-length of every finite-length module. -/
theorem length_extDualTwo (M : Type u) [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) :
    Module.length R (extDualTwo R (ModuleCat.of R M)) = Module.length R M := by
  induction hM with
  | @of_subsingleton M _ _ _ =>
    let : HasProjectiveDimensionLT (ModuleCat.of R M) 0 :=
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of R M)).hasProjectiveDimensionLT_zero
    let : Subsingleton (extDualTwo R (ModuleCat.of R M)) :=
      HasProjectiveDimensionLT.subsingleton (ModuleCat.of R M) 0 2 (by omega)
        (ModuleCat.of R R)
    simp only [Module.length_eq_zero]
  | @of_simple_quotient M _ _ N hsimple hN ih =>
    let : IsSimpleModule R (M ⧸ N) := hsimple
    have hQ : IsFiniteLength R (M ⧸ N) :=
      isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
    let S := ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ
      (by ext x; exact (Submodule.Quotient.mk_eq_zero N).mpr x.property)
    have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
      (LinearMap.exact_subtype_mkQ N) N.subtype_injective N.mkQ_surjective
    obtain ⟨hinj, hexact, hsurj⟩ := extDualTwo_exact R hd S hS hN hQ
    have hlenD := Module.length_eq_add_of_exact
      (extDualTwoMap R S.g) (extDualTwoMap R S.f) hinj hsurj hexact
    have hlenM := Module.length_eq_add_of_exact N.subtype N.mkQ
      N.subtype_injective N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)
    change Module.length R (extDualTwo R (ModuleCat.of R M)) =
      Module.length R (extDualTwo R (ModuleCat.of R (M ⧸ N))) +
        Module.length R (extDualTwo R (ModuleCat.of R N)) at hlenD
    rw [hlenD, length_extDualTwo_of_isSimple R hd (M ⧸ N), ih, hlenM,
      Module.length_eq_one R (M ⧸ N), add_comm 1]

/-- The Ext-two dual remains a finite-length module over the same ring. -/
theorem isFiniteLength_extDualTwo (M : ModuleCat.{u} R) (hM : IsFiniteLength R M) :
    IsFiniteLength R (extDualTwo R M) := by
  apply Module.length_ne_top_iff.mp
  rw [length_extDualTwo R hd M hM]
  exact Module.length_ne_top_iff.mpr hM

/-- Ext-two detects the zero module on finite-length sources. -/
theorem subsingleton_extDualTwo_iff (M : ModuleCat.{u} R) (hM : IsFiniteLength R M) :
    Subsingleton (extDualTwo R M) ↔ Subsingleton M := by
  rw [← Module.length_eq_zero_iff (R := R) (M := extDualTwo R M),
    length_extDualTwo R hd M hM, Module.length_eq_zero_iff (R := R) (M := M)]

/-- A morphism of finite-length modules is zero exactly when its actual
Ext-two precomposition map is zero. -/
theorem extDualTwoMap_eq_zero_iff {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hM : IsFiniteLength R M) (hN : IsFiniteLength R N) :
    extDualTwoMap R f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    let I := LinearMap.range f.hom
    let p := f.hom.rangeRestrict
    let i : ModuleCat.of R I ⟶ N := ModuleCat.ofHom I.subtype
    let q : M ⟶ ModuleCat.of R I := ModuleCat.ofHom p
    have hI : IsFiniteLength R I := hN.of_injective I.subtype_injective
    let S₁ := p.shortComplexKer
    have hS₁ : S₁.ShortExact := LinearMap.shortExact_shortComplexKer
      f.hom.surjective_rangeRestrict
    have hker : IsFiniteLength R (LinearMap.ker p) :=
      hM.of_injective (Submodule.subtype_injective _)
    have hp := (extDualTwo_exact R hd S₁ hS₁ hker hI).1
    let S₂ := ModuleCat.shortComplexOfCompEqZero I.subtype I.mkQ
      (by ext x; exact (Submodule.Quotient.mk_eq_zero I).mpr x.property)
    have hS₂ : S₂.ShortExact := ModuleCat.shortComplex_shortExact S₂
      (LinearMap.exact_subtype_mkQ I) I.subtype_injective I.mkQ_surjective
    have hquot : IsFiniteLength R (N ⧸ I) := hN.of_surjective I.mkQ_surjective
    have hi := (extDualTwo_exact R hd S₂ hS₂ hI hquot).2.2
    have hcomp : q ≫ i = f := by ext x; rfl
    have hdualI : Subsingleton (extDualTwo R (ModuleCat.of R I)) := by
      have hz (z : extDualTwo R (ModuleCat.of R I)) : z = 0 := by
        obtain ⟨y, rfl⟩ := hi z
        apply hp
        change ((extDualTwoMap R q).comp (extDualTwoMap R i)) y =
          extDualTwoMap R q 0
        rw [extDualTwoMap_comp, hcomp, hf, map_zero]
        rfl
      exact ⟨fun z z' ↦ (hz z).trans (hz z').symm⟩
    let : Subsingleton I := (subsingleton_extDualTwo_iff R hd (ModuleCat.of R I) hI).mp hdualI
    ext x
    exact congrArg Subtype.val (Subsingleton.elim (p x) 0)
  · rintro rfl
    ext x
    change (Ext.mk₀ (0 : M ⟶ N)).comp x (zero_add 2) = 0
    rw [Ext.mk₀_zero, Ext.zero_comp]

/-- Native Ext-two precomposition is faithful on finite-length modules. -/
theorem extDualTwoMap_injective (M N : ModuleCat.{u} R)
    (hM : IsFiniteLength R M) (hN : IsFiniteLength R N) :
    Function.Injective (extDualTwoMapLinear R M N) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro f hf
  exact (extDualTwoMap_eq_zero_iff R hd f hM hN).mp hf

end IsRegularLocalRing
