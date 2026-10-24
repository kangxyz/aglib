/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.FiniteSource.Derived
public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.RegularList.Sheaf
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction.Principal
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Adjunction.Exact
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Linear
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Exact
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Stalk
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeExact
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Principal closed adjunction with an arbitrary coefficient

The original quotient action and finite-source resolution identify the actual
closed right adjoint of a quasicoherent coefficient regular along the principal
equation with its scalar quotient in degree one. The positive normalization is
the actual derived adjoint of the original coefficient extension class.

The raw Koszul and positive comparisons have separate names. Their equality
and compatibility of the positive comparison with the full derived open exchange
are not asserted. The localization statements below concern the original raw
resolution map and the actual restricted positive extension class. The current
consumer is the nonreduced CM-curve Cartier argument; no global Cartier or
CM-curve theorem is supplied here.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open HomologicalComplex CochainComplex
open ChainComplex.Koszul

private theorem principalConjugateZero
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] {N Q : C} (μ : N ⟶ N) (π : N ⟶ Q)
    (h : μ ≫ π = 0) {M Q' : D} (A : F.obj N ≅ M) (B : Q' ≅ F.obj Q) :
    (A.inv ≫ F.map μ ≫ A.hom) ≫ (A.inv ≫ F.map π ≫ B.inv) = 0 := by
  calc
    _ = A.inv ≫ (F.map μ ≫ F.map π) ≫ B.inv := by simp [Category.assoc]
    _ = A.inv ≫ F.map (μ ≫ π) ≫ B.inv := by rw [Functor.map_comp]
    _ = 0 := by rw [h, Functor.map_zero, zero_comp, comp_zero]

private theorem principalConjugateCompInv
    {C : Type*} [Category* C] {N M : C} (A : N ≅ M) (μ : N ⟶ N) :
    A.inv ≫ μ = (A.inv ≫ μ ≫ A.hom) ≫ A.inv := by
  simp [Category.assoc]

private theorem principalPostIsoCancel
    {C : Type*} [Category* C] {M N Q Q' : C} (x : M ⟶ N) (y : N ⟶ Q)
    (B : Q' ≅ Q) : x ≫ y = (x ≫ y ≫ B.inv) ≫ B.hom := by
  simp [Category.assoc]

private theorem principalTwoPreimageInv
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Full] [F.Faithful] [G.Full] [G.Faithful]
    {X Y : C} {Z : E} (e : G.obj (F.obj X) ≅ Z) (σ : G.obj (F.obj Y) ≅ Z) :
    σ.inv ≫ G.map (F.map (F.preimageIso (G.preimageIso (e ≪≫ σ.symm))).inv) = e.inv := by
  change σ.inv ≫ G.map (F.map (F.preimage
    (G.preimage (e ≪≫ σ.symm).inv))) = e.inv
  rw [F.map_preimage, G.map_preimage]
  simp

private def principalResolutionHom
    {C : Type*} [Category* C] [Abelian C] {M N : C} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) :
    InjectiveResolution.Hom I J f :=
  ⟨InjectiveResolution.desc f J I,
    HomologicalComplex.congr_hom (InjectiveResolution.desc_commutes f J I) 0⟩

private theorem principalExtHomNaturality
    {C : Type*} [Category* C] [Abelian C] [HasExt C] [HasDerivedCategory C]
    {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y')
    (x : Ext X Y 1) (y : Ext X' Y' 1)
    (h : x.comp (Ext.mk₀ g) (add_zero 1) = (Ext.mk₀ f).comp y (zero_add 1)) :
    x.hom ≫ (CategoryTheory.shiftFunctor (DerivedCategory C) (1 : ℤ)).map
        ((DerivedCategory.singleFunctor C 0).map g) =
      (DerivedCategory.singleFunctor C 0).map f ≫ y.hom :=
  (Ext.hom_comp_singleFunctor_map_shift x g).trans
    ((congrArg Ext.hom h).trans (Ext.singleFunctor_map_comp_hom f y).symm)

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] standardHasDerivedCategory

public local instance principalSheafHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} X.Modules := HasExt.standard _

public local instance principalModuleHasExt (R : CommRingCat.{u}) :
    HasExt.{u + 1} (ModuleCat.{u} R) := HasExt.standard _

public local instance principalTildeAdditive (R : CommRingCat.{u}) :
    (tilde.functor R).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The original scalar quotient, with the native principal quotient-ring action. -/
public def principalCoefficientQuotient {R : CommRingCat.{u}} (a : R)
    (M : (Spec R).Modules) : ModuleCat.{u} (CommRingCat.of (R ⧸ Ideal.span {a})) :=
  letI := singleQuotientModule a (moduleSpecΓFunctor.obj M)
  ModuleCat.of (R ⧸ Ideal.span {a}) (SingleQuotient (moduleSpecΓFunctor.obj M) a)

/-- The associated sheaf of the original quotient module. -/
public def principalCoefficientQuotientSheaf {R : CommRingCat.{u}} (a : R)
    (M : (Spec R).Modules) : (Spec (CommRingCat.of (R ⧸ Ideal.span {a}))).Modules :=
  tilde (principalCoefficientQuotient a M)

/-- Original affine sections of the installed quotient-adjoint resolution. -/
public abbrev principalResolutionSections {R : CommRingCat.{u}} (a : R)
    {M : (Spec R).Modules} (J : InjectiveResolution M) :
    CochainComplex (ModuleCat.{u} (R ⧸ Ideal.span {a})) ℤ :=
  ((moduleSpecΓFunctor (R := .of (R ⧸ Ideal.span {a}))).mapHomologicalComplex (.up ℤ)).obj
    (closedImmersionRightAdjointQuotientResolutionComplex (Ideal.span {a}) J)

section Homology

variable {R : CommRingCat.{u}} [IsNoetherianRing R] (a : R)
  (ha : IsSMulRegular R a) (M : (Spec R).Modules) [M.IsQuasicoherent]
  (J : InjectiveResolution M)

/-- Original resolution sections, native Ext, and the original principal Koszul class.
The coefficient is arbitrary; only the equation is regular on the ring here. -/
public def principalResolutionSectionsLinearEquiv :
    (principalResolutionSections a J).homology 1 ≃ₗ[R ⧸ Ideal.span {a}]
      principalCoefficientQuotient a M := by
  letI := singleQuotientModule a (moduleSpecΓFunctor.obj M)
  letI := Ext.quotientSourceModule (Ideal.span {a}) (moduleSpecΓFunctor.obj M) 1
  let E : (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {a}))).obj
      ((principalResolutionSections a J).homology 1) ≃ₗ[R]
      Ext.{u + 1} (ModuleCat.of R (R ⧸ Ideal.span {a})) (moduleSpecΓFunctor.obj M) 1 :=
    affineClosedRightAdjointResolutionExtLinearEquiv
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))) J 1
  let P := singleIdealExtOneQuotientLinearEquiv a ha (moduleSpecΓFunctor.obj M)
  refine {
    __ := E.toAddEquiv.trans P.symm.toAddEquiv
    map_smul' := ?_ }
  intro b x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hR : E (Ideal.Quotient.mk (Ideal.span {a}) r • x) = r • E x := E.map_smul r x
  have hq : Ideal.Quotient.mk (Ideal.span {a}) r • E x = r • E x :=
    Ext.quotientSourceModule_mk_smul (Ideal.span {a}) (moduleSpecΓFunctor.obj M) 1 r (E x)
  exact (congrArg P.symm hR).trans
    ((congrArg P.symm hq.symm).trans (P.symm.map_smul _ _))

omit [IsNoetherianRing R] in
/-- Each original quotient representative retains its original Koszul Ext class. -/
public theorem principalResolutionSectionsLinearEquiv_symm_mk
    (x : moduleSpecΓFunctor.obj M) :
    affineClosedRightAdjointResolutionExtAddEquiv (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span
      {a}))) J 1
      ((principalResolutionSectionsLinearEquiv a ha M J).symm (Submodule.Quotient.mk x)) =
        singleIdealExtOneClass a ha (moduleSpecΓFunctor.obj M) x := by
  let := singleQuotientModule a (moduleSpecΓFunctor.obj M)
  let := Ext.quotientSourceModule (Ideal.span {a}) (moduleSpecΓFunctor.obj M) 1
  change (affineClosedRightAdjointResolutionExtLinearEquiv (CommRingCat.ofHom (Ideal.Quotient.mk
    (Ideal.span {a}))) J 1)
    ((principalResolutionSectionsLinearEquiv a ha M J).symm (Submodule.Quotient.mk x)) = _
  let E : (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {a}))).obj
      ((principalResolutionSections a J).homology 1) ≃ₗ[R]
      Ext.{u + 1} (ModuleCat.of R (R ⧸ Ideal.span {a})) (moduleSpecΓFunctor.obj M) 1 :=
    affineClosedRightAdjointResolutionExtLinearEquiv
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))) J 1
  let P := singleIdealExtOneQuotientLinearEquiv a ha (moduleSpecΓFunctor.obj M)
  have h : P.symm (E ((principalResolutionSectionsLinearEquiv a ha M J).symm
      (Submodule.Quotient.mk x))) = Submodule.Quotient.mk x :=
    (principalResolutionSectionsLinearEquiv a ha M J).apply_symm_apply _
  have h' := (P.apply_symm_apply
    (E ((principalResolutionSectionsLinearEquiv a ha M J).symm
      (Submodule.Quotient.mk x)))).symm.trans (congrArg P h)
  exact h'.trans (singleIdealExtOneQuotientLinearEquiv_apply_mk
    a ha (moduleSpecΓFunctor.obj M) x)

/-- The actual derived homology, reconstructed through the original affine counit. -/
public def derivedClosedImmersionRightAdjointPrincipalKoszulHomologyIso :
    derivedClosedImmersionRightAdjointHomology (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (Ideal.span {a})))) M 1 ≅
      principalCoefficientQuotientSheaf a M :=
  derivedClosedImmersionRightAdjointQuotientHomologyIso (Ideal.span {a}) J 1 ≪≫
    (closedImmersionRightAdjointQuotientResolutionHomologyIso (Ideal.span {a}) J 1).symm ≪≫
    (tilde.functor (CommRingCat.of (R ⧸ Ideal.span {a}))).mapIso
      (principalResolutionSectionsLinearEquiv a ha M J).toModuleIso

/-- The homology arrow retains the original injective-model map and affine counit. -/
public theorem derivedClosedImmersionRightAdjointPrincipalKoszulHomologyIso_hom :
    (derivedClosedImmersionRightAdjointPrincipalKoszulHomologyIso a ha M J).hom =
      (derivedClosedImmersionRightAdjointQuotientHomologyIso (Ideal.span {a}) J 1).hom ≫
        (closedImmersionRightAdjointQuotientResolutionHomologyIso (Ideal.span {a}) J 1).inv ≫
          (tilde.functor (CommRingCat.of (R ⧸ Ideal.span {a}))).map
            (principalResolutionSectionsLinearEquiv a ha M J).toModuleIso.hom := rfl

omit [IsNoetherianRing R] in
include ha in
private theorem principalResolutionSections_isZero
    (hM : IsSMulRegular (moduleSpecΓFunctor.obj M) a)
    (q : ℤ) (hq : q ≠ 1) : IsZero ((principalResolutionSections a J).homology q) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  by_cases hneg : q < 0
  · exact ModuleCat.subsingleton_of_isZero
      (ShortComplex.isZero_homology_of_isZero_X₂ _
        ((moduleSpecΓFunctor (R := CommRingCat.of (R ⧸ Ideal.span {a}))).map_isZero
          ((closedImmersionRightAdjoint (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span
            {a}))))).map_isZero
            (J.cochainComplex.isZero_of_isStrictlyGE 0 q hneg))))
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    let E := affineClosedRightAdjointResolutionExtAddEquiv (CommRingCat.ofHom (Ideal.Quotient.mk
      (Ideal.span {a}))) J n
    refine ⟨fun x y => E.injective ?_⟩
    have hn : n ≠ 1 := by exact_mod_cast hq
    exact (singleIdealExt_eq_zero_of_ne_one a ha (moduleSpecΓFunctor.obj M) hM n hn
      (E x)).trans
      (singleIdealExt_eq_zero_of_ne_one a ha (moduleSpecΓFunctor.obj M) hM n hn
        (E y)).symm

include ha J in
/-- Coefficient regularity removes every degree except the native degree one. -/
public theorem derivedClosedImmersionRightAdjointPrincipalHomology_isZero
    (hM : IsSMulRegular (moduleSpecΓFunctor.obj M) a) (q : ℤ) (hq : q ≠ 1) :
    IsZero (derivedClosedImmersionRightAdjointHomology (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {a})))) M q) := by
  let : (tilde.functor (CommRingCat.of (R ⧸ Ideal.span {a}))).Additive :=
    principalTildeAdditive _
  have h := (tilde.functor (CommRingCat.of (R ⧸ Ideal.span {a}))).map_isZero
    (principalResolutionSections_isZero a ha M J hM q hq)
  exact h.of_iso
    (derivedClosedImmersionRightAdjointQuotientHomologyIso (Ideal.span {a}) J q ≪≫
      (closedImmersionRightAdjointQuotientResolutionHomologyIso (Ideal.span {a}) J q).symm)

include ha J in
/-- Lower bound for the original installed right-adjoint value. -/
public theorem derivedClosedImmersionRightAdjointPrincipal_isGE
    (hM : IsSMulRegular (moduleSpecΓFunctor.obj M) a) :
    ((derivedClosedImmersionRightAdjointPlus (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (Ideal.span {a}))))).obj
      ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj M)).IsGE 1 := by
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
  intro q hq
  exact derivedClosedImmersionRightAdjointPrincipalHomology_isZero a ha M J hM q
    (ne_of_lt hq)

include ha J in
/-- Upper bound for the original installed right-adjoint value. -/
public theorem derivedClosedImmersionRightAdjointPrincipal_isLE
    (hM : IsSMulRegular (moduleSpecΓFunctor.obj M) a) :
    ((derivedClosedImmersionRightAdjointPlus (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (Ideal.span {a}))))).obj
      ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj M)).IsLE 1 := by
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff, DerivedCategory.isLE_iff]
  intro q hq
  exact derivedClosedImmersionRightAdjointPrincipalHomology_isZero a ha M J hM q
    (ne_of_gt hq)

/-- The original Koszul-normalized sheaf purity value, before its counit formula. -/
public def derivedClosedImmersionRightAdjointPrincipalKoszulIso
    (hM : IsSMulRegular (moduleSpecΓFunctor.obj M) a) :
    (derivedClosedImmersionRightAdjointPlus (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (Ideal.span {a}))))).obj
      ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj M) ≅
        (DerivedCategory.Plus.singleFunctor (Spec (CommRingCat.of (R ⧸ Ideal.span {a}))).Modules
          1).obj
          (principalCoefficientQuotientSheaf a M) := by
  let K := (derivedClosedImmersionRightAdjointPlus (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
    (Ideal.span {a}))))).obj
    ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj M)
  let := derivedClosedImmersionRightAdjointPrincipal_isGE a ha M J hM
  let := derivedClosedImmersionRightAdjointPrincipal_isLE a ha M J hM
  exact DerivedCategory.Plus.isoSingleHomology K 1 ≪≫
    (DerivedCategory.Plus.singleFunctor (Spec (CommRingCat.of (R ⧸ Ideal.span {a}))).Modules
      1).mapIso
      (derivedClosedImmersionRightAdjointPrincipalKoszulHomologyIso a ha M J)

end Homology

end AlgebraicGeometry.Scheme.Modules

namespace CategoryTheory

section ScalarExtensionClass

variable {R : Type*} [CommRing R] {D : Type*} [Category* D] [Abelian D]
  [HasExt D] [Linear R D] (a : R) (M Q T : D) (g : M ⟶ Q)
  (hg : (a • 𝟙 M) ≫ g = 0)
  (hS : (ShortComplex.mk (a • 𝟙 M) g hg).ShortExact)
  (hT : a • 𝟙 T = 0)

omit [HasExt D] in
include hS hT in
private theorem scalarExtension_hom_eq_zero (f : T ⟶ M) : f = 0 := by
  let : Mono (a • 𝟙 M) := hS.mono_f
  apply (cancel_mono (a • 𝟙 M)).mp
  calc
    f ≫ (a • 𝟙 M) = (a • 𝟙 T) ≫ f := by
      simp only [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]
    _ = 0 ≫ f := by rw [hT]
    _ = (0 : T ⟶ M) ≫ (a • 𝟙 M) := by simp

include hT in
private theorem scalarExtension_ext_smul_eq_zero (x : Ext T M 1) :
    x.comp (Ext.mk₀ (a • 𝟙 M)) (add_zero 1) = 0 := by
  calc
    x.comp (Ext.mk₀ (a • 𝟙 M)) (add_zero 1) = a • x :=
      (Ext.smul_eq_comp_mk₀ x a).symm
    _ = (Ext.mk₀ (a • 𝟙 T)).comp x (zero_add 1) := by
      rw [Ext.mk₀_smul, Ext.smul_comp, Ext.mk₀_id_comp]
    _ = 0 := by rw [hT, Ext.mk₀_zero, Ext.zero_comp]

/-- The original positive coefficient-extension map, with no comparison premise. -/
def scalarExtensionHomExtMap : (T ⟶ Q) →+ Ext T M 1 where
  toFun f := (Ext.mk₀ f).comp hS.extClass (zero_add 1)
  map_zero' := by simp
  map_add' f g := by rw [Ext.mk₀_add, Ext.add_comp]

include hT in
/-- A regular coefficient equation killed on the source gives the actual Rees
bijection in degree one, by the native covariant exact sequence. -/
theorem scalarExtensionHomExtMap_bijective :
    Function.Bijective (scalarExtensionHomExtMap a M Q T g hg hS) := by
  constructor
  · intro f f' h
    have hz : (scalarExtensionHomExtMap a M Q T g hg hS) (f - f') = 0 := by
      rw [map_sub, h, sub_self]
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ T hS (Ext.mk₀ (f - f')) rfl hz
    have hz0 : z = 0 := by
      rw [← Ext.mk₀_addEquiv₀_apply z]
      rw [scalarExtension_hom_eq_zero a M Q T g hg hS hT (Ext.addEquiv₀ z), Ext.mk₀_zero]
    rw [hz0, Ext.zero_comp] at hz
    exact sub_eq_zero.mp ((Ext.mk₀_eq_zero_iff (f - f')).mp hz.symm)
  · intro x
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ T hS x
      (scalarExtension_ext_smul_eq_zero a M T hT x) rfl
    exact ⟨Ext.addEquiv₀ z, by simpa only [scalarExtensionHomExtMap,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk, Ext.mk₀_addEquiv₀_apply] using hz⟩

end ScalarExtensionClass

end CategoryTheory

namespace CategoryTheory.Adjunction

section PrincipalMate

variable {R : Type*} [CommRing R]
  {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
  [HasExt D] [EnoughInjectives D] [Linear R D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [F.PreservesMonomorphisms] [F.Full] [F.Faithful]
  (adj : F ⊣ G) (a : R) (M : D) (Q : C) (g : M ⟶ F.obj Q)
  (hg : (a • 𝟙 M) ≫ g = 0)
  (hS : (ShortComplex.mk (a • 𝟙 M) g hg).ShortExact)

/-- The actual derived adjoint of the original positive coefficient row. -/
def scalarExtensionMate :
    (DerivedCategory.singleFunctor C 0).obj Q ⟶
      (DerivedCategory.Plus.ι.obj
        (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor D 0).obj M)))⟦(1 : ℤ)⟧
          :=
  adj.singleDerivedHomEquivOfInjectiveResolution Q (injectiveResolution M) 1 hS.extClass.hom

/-- The original mate is an isomorphism once concentration identifies its target
with a degree-zero single. Its normalization is derived from the actual row. -/
theorem scalarExtensionMate_isIso
    (hkill : ∀ T : C, a • 𝟙 (F.obj T) = 0)
    (e : (DerivedCategory.Plus.ι.obj
      (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor D 0).obj M)))⟦(1 : ℤ)⟧ ≅
        (DerivedCategory.singleFunctor C 0).obj Q) :
    IsIso (scalarExtensionMate adj a M Q g hg hS) := by
  let η := scalarExtensionMate adj a M Q g hg hS
  let S := DerivedCategory.singleFunctor C 0
  let u : Q ⟶ Q := S.preimage (η ≫ e.hom)
  have hu : S.map u = η ≫ e.hom := S.map_preimage _
  have hbij (T : C) : Function.Bijective (fun f : T ⟶ Q => S.map f ≫ η) := by
    let eF : (T ⟶ Q) ≃ (F.obj T ⟶ F.obj Q) :=
      (Functor.FullyFaithful.ofFullyFaithful F).homEquiv
    let E₁ := AddEquiv.ofBijective (scalarExtensionHomExtMap a M (F.obj Q) (F.obj T) g hg hS)
      (scalarExtensionHomExtMap_bijective a M (F.obj Q) (F.obj T) g hg hS (hkill T))
    let E₂ := adj.singleDerivedHomEquivOfInjectiveResolution T (injectiveResolution M) 1
    let E := eF.trans (E₁.toEquiv.trans (Ext.homEquiv.trans E₂.toEquiv))
    have hE (f : T ⟶ Q) : E f = S.map f ≫ η := by
      change adj.singleDerivedHomEquivOfInjectiveResolution T (injectiveResolution M) 1
        (((Ext.mk₀ (F.map f)).comp hS.extClass (zero_add 1)).hom) = _
      rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp]
      change adj.singleDerivedHomEquivOfInjectiveResolution T (injectiveResolution M) 1
        ((DerivedCategory.singleFunctor D 0).map (F.map f) ≫ hS.extClass.hom) =
          (DerivedCategory.singleFunctor C 0).map f ≫
            adj.singleDerivedHomEquivOfInjectiveResolution Q (injectiveResolution M) 1
              hS.extClass.hom
      exact adj.singleDerivedHomEquivOfInjectiveResolution_naturality_left
        T (injectiveResolution M) 1 f hS.extClass.hom
    have heq : (fun f : T ⟶ Q => S.map f ≫ η) = E := by
      funext f
      exact (hE f).symm
    rw [heq]
    exact E.bijective
  have huIso : IsIso u := by
    apply isIso_of_yoneda_map_bijective u
    intro T
    constructor
    · intro f f' h
      apply (hbij T).1
      apply (cancel_mono e.hom).mp
      have h' := congrArg S.map h
      simpa only [Functor.map_comp, hu, Category.assoc] using h'
    · intro f
      obtain ⟨g', hg'⟩ := (hbij T).2 (S.map f ≫ e.inv)
      change S.map g' ≫ η = S.map f ≫ e.inv at hg'
      refine ⟨g', S.map_injective ?_⟩
      rw [Functor.map_comp, hu, ← Category.assoc, hg']
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let := huIso
  have : IsIso (η ≫ e.hom) := by rw [← hu]; infer_instance
  exact IsIso.of_isIso_comp_right η e.hom

omit [F.Full] [F.Faithful] in
/-- Inverting the original mate gives the actual positive counit normalization. -/
theorem scalarExtensionMate_counit :
    (adj.singleDerivedHomEquivOfInjectiveResolution Q (injectiveResolution M) 1).symm
      (scalarExtensionMate adj a M Q g hg hS) = hS.extClass.hom :=
  (adj.singleDerivedHomEquivOfInjectiveResolution Q (injectiveResolution M) 1).symm_apply_apply _

end PrincipalMate
end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] standardHasDerivedCategory principalSheafHasExt

/-- The `R`-linear structure on module sheaves over `Spec R`, induced by
its canonical global-section isomorphism. -/
public local instance principalAmbientLinear (R : CommRingCat.{u}) : Linear R (Spec R).Modules :=
  moduleCategoryLinearOfHom (Spec R) (Scheme.ΓSpecIso R).inv.hom

section CoefficientRow

variable {R : CommRingCat.{u}} (a : R) (M : (Spec R).Modules)

/-- Restricting the original quotient-ring action recovers the original R-module. -/
public def principalCoefficientQuotientRestrictionIso :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {a}))).obj
      (principalCoefficientQuotient a M) ≅
        ModuleCat.of R (SingleQuotient (moduleSpecΓFunctor.obj M) a) := by
  letI := singleQuotientModule a (moduleSpecΓFunctor.obj M)
  let e : (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {a}))).obj
      (principalCoefficientQuotient a M) ≃ₗ[R]
      SingleQuotient (moduleSpecΓFunctor.obj M) a := {
    toFun := fun x => (show SingleQuotient (moduleSpecΓFunctor.obj M) a from x)
    invFun := fun x =>
      (show (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {a}))).obj
        (principalCoefficientQuotient a M) from x)
    left_inv := fun x => rfl
    right_inv := fun x => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun r x => singleQuotientModule_mk_smul a (moduleSpecΓFunctor.obj M) r x }
  exact e.toModuleIso

/-- Actual closed pushforward and the original affine tilde comparison. -/
public def principalCoefficientQuotientPushforwardIso :
    (pushforward (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))))).obj
      (principalCoefficientQuotientSheaf a M) ≅
      tilde (ModuleCat.of R (SingleQuotient (moduleSpecΓFunctor.obj M) a)) :=
  (tildePushforwardIso (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))).app
    (principalCoefficientQuotient a M) ≪≫
    (tilde.functor R).mapIso (principalCoefficientQuotientRestrictionIso a M)

private def principalCoefficientModuleSequence : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk
    (ModuleCat.ofHom (LinearMap.lsmul R (moduleSpecΓFunctor.obj M) a))
    (singleAugmentationMap (moduleSpecΓFunctor.obj M) a)
    (ModuleCat.hom_ext
      (LinearMap.exact_map_mkQ_range (LinearMap.lsmul R (moduleSpecΓFunctor.obj M)
        a)).linearMap_comp_eq_zero)

private theorem principalCoefficientModuleSequence_shortExact
    (hM : IsSMulRegular (moduleSpecΓFunctor.obj M) a) :
    (principalCoefficientModuleSequence a M).ShortExact where
  exact := by
    simpa only [principalCoefficientModuleSequence, singleComplex_X_one,
      singleComplex_X_zero, singleComplex_d_one_zero] using
        singleAugmentation_exact (moduleSpecΓFunctor.obj M) a
  mono_f := (ModuleCat.mono_iff_injective _).mpr hM
  epi_g := by
    change Epi (singleAugmentationMap (moduleSpecΓFunctor.obj M) a)
    infer_instance

private theorem principalScalar_sections :
    (moduleSpecΓFunctor (R := R)).map (a • 𝟙 M) =
      a • 𝟙 ((moduleSpecΓFunctor (R := R)).obj M) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact moduleCategoryLinearOfHom_smul_app (Spec R) (Scheme.ΓSpecIso R).inv.hom
    (𝟙 M) a ⊤ x

variable [M.IsQuasicoherent]

private theorem principalScalar_conjugate :
    (asIso M.fromTildeΓ).inv ≫
        (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map (a • 𝟙 M)) ≫
          M.fromTildeΓ = a • 𝟙 M := by
  let A := asIso M.fromTildeΓ
  have h := (tilde.adjunction (R := R)).counit.naturality (a • 𝟙 M)
  change (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map (a • 𝟙 M)) ≫
    A.hom = A.hom ≫ (a • 𝟙 M) at h
  calc
    _ = A.inv ≫ (A.hom ≫ (a • 𝟙 M)) := congrArg (fun f => A.inv ≫ f) h
    _ = _ := by rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The original coefficient quotient, transported only by original affine counits. -/
public def principalCoefficientQuotientMap :
    M ⟶ (pushforward (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))))).obj
      (principalCoefficientQuotientSheaf a M) :=
  (asIso M.fromTildeΓ).inv ≫
    (tilde.functor R).map (singleAugmentationMap (moduleSpecΓFunctor.obj M) a) ≫
      (principalCoefficientQuotientPushforwardIso a M).inv

/-- The original quotient kills the original scalar multiplication. -/
public theorem principalCoefficientSequence_zero :
    (a • 𝟙 M) ≫ principalCoefficientQuotientMap a M = 0 := by
  let N : ModuleCat.{u} R := moduleSpecΓFunctor.obj M
  let Q : ModuleCat.{u} R := ModuleCat.of R (SingleQuotient N a)
  let μ : N ⟶ N := a • 𝟙 N
  let π : N ⟶ Q := singleAugmentationMap N a
  let F : ModuleCat.{u} R ⥤ (Spec R).Modules := tilde.functor R
  let : F.Additive := principalTildeAdditive R
  let : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent M
  let A := asIso M.fromTildeΓ
  let B := principalCoefficientQuotientPushforwardIso a M
  have hμΓ : (moduleSpecΓFunctor (R := R)).map (a • 𝟙 M) = μ :=
    principalScalar_sections a M
  have hμ : A.inv ≫ F.map μ ≫ A.hom = a • 𝟙 M :=
    (congrArg (fun f : N ⟶ N => A.inv ≫ F.map f ≫ A.hom) hμΓ).symm.trans
      (principalScalar_conjugate a M)
  have h0 : μ ≫ π = 0 := (principalCoefficientModuleSequence a M).zero
  have hz := principalConjugateZero F μ π h0 A B
  exact (congrArg (fun f : M ⟶ M => f ≫ principalCoefficientQuotientMap a M) hμ).symm.trans hz

/-- The actual multiplication and quotient row for the original coefficient. -/
public def principalCoefficientSequence : ShortComplex (Spec R).Modules :=
  ShortComplex.mk (a • 𝟙 M) (principalCoefficientQuotientMap a M)
    (principalCoefficientSequence_zero a M)

private def principalCoefficientSequenceIso :
    principalCoefficientSequence a M ≅
      (principalCoefficientModuleSequence a M).map (tilde.functor R) :=
  ShortComplex.isoMk (asIso M.fromTildeΓ).symm (asIso M.fromTildeΓ).symm
    (principalCoefficientQuotientPushforwardIso a M)
    (by
      let N : ModuleCat.{u} R := moduleSpecΓFunctor.obj M
      let μ : N ⟶ N := a • 𝟙 N
      let F : ModuleCat.{u} R ⥤ (Spec R).Modules := tilde.functor R
      let : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent M
      let A := asIso M.fromTildeΓ
      have hμΓ : (moduleSpecΓFunctor (R := R)).map (a • 𝟙 M) = μ :=
        principalScalar_sections a M
      have hc : A.inv ≫ F.map μ ≫ A.hom = a • 𝟙 M :=
        (congrArg (fun f : N ⟶ N => A.inv ≫ F.map f ≫ A.hom) hμΓ).symm.trans
          (principalScalar_conjugate a M)
      exact (principalConjugateCompInv A (F.map μ)).trans
        (congrArg (fun f : M ⟶ M => f ≫ A.inv) hc))
    (by
      exact principalPostIsoCancel (asIso M.fromTildeΓ).inv
        ((tilde.functor R).map (singleAugmentationMap (moduleSpecΓFunctor.obj M) a))
        (principalCoefficientQuotientPushforwardIso a M))

/-- Coefficient regularity gives the original short exact row. -/
public theorem principalCoefficientSequence_shortExact
    (hM : IsSMulRegular (moduleSpecΓFunctor.obj M) a) :
    (principalCoefficientSequence a M).ShortExact :=
  ShortComplex.shortExact_of_iso (principalCoefficientSequenceIso a M).symm
    ((principalCoefficientModuleSequence_shortExact a M hM).map_of_exact (tilde.functor R))

end CoefficientRow

private theorem scalarPushforward_zero_of_appTop_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Γ(Y, ⊤)) (hc : f.appTop c = 0)
    (T : X.Modules) : globalScalarEndomorphism Y ((pushforward f).obj T) c = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change (globalScalarEndomorphism Y ((pushforward f).obj T) c).val.app (op U) x = 0
  change Γ(T, f ⁻¹ᵁ U) at x
  have he := globalScalarEndomorphism_app Y ((pushforward f).obj T) c U x
  have hn := congrArg (fun q : Γ(Y, ⊤) ⟶ Γ(X, f ⁻¹ᵁ U) => q c)
    (f.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  change f.app U (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op c) =
    X.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤)).op (f.appTop c) at hn
  have hzero : f.app U (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op c) = 0 :=
    hn.trans (by rw [hc, map_zero])
  have hxzero : Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op c •
      (show Γ((pushforward f).obj T, U) from x) = 0 := by
    change f.app U (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op c) • x = 0
    exact (congrArg (fun r : Γ(X, f ⁻¹ᵁ U) => r • x) hzero).trans (zero_smul _ x)
  exact he.trans hxzero

/-- The original principal equation acts by zero on every actual closed pushforward. -/
public theorem principalScalar_pushforward_eq_zero {R : CommRingCat.{u}} (a : R)
    (T : (Spec (CommRingCat.of (R ⧸ Ideal.span {a}))).Modules) :
    a • 𝟙 ((pushforward (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))))).obj T) = 0 := by
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))
  have htop : i.appTop ((Scheme.ΓSpecIso R).inv a) = 0 := by
    have h := congrArg (fun f : R ⟶ Γ(Spec (CommRingCat.of (R ⧸ Ideal.span {a})), ⊤) => f a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))).symm
    change i.appTop ((Scheme.ΓSpecIso R).inv a) =
      (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {a}))).inv ((CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span {a}))) a) at h
    rw [h]
    have hz : (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton a))
    rw [hz, map_zero]
  rw [moduleCategoryLinearOfHom_smul_id]
  exact scalarPushforward_zero_of_appTop_zero i ((Scheme.ΓSpecIso R).inv a) htop T

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] standardHasDerivedCategory principalSheafHasExt principalAmbientLinear

section PositivePurity

variable {R : CommRingCat.{u}} [IsNoetherianRing R] (a : R)
  (ha : IsSMulRegular R a) (M : (Spec R).Modules) [M.IsQuasicoherent]
  (hM : IsSMulRegular (moduleSpecΓFunctor.obj M) a)

/-- The original installed principal closed-adjoint value at the coefficient single. -/
public abbrev principalDerivedObject :
    DerivedCategory.Plus (Spec (.of (R ⧸ Ideal.span {a}))).Modules :=
  (derivedClosedImmersionRightAdjointPlus
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))))).obj
    ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj M)

/-- The original single-functor shift from degree one to degree zero. -/
public def principalSingleShiftIso (Q : (Spec (CommRingCat.of (R ⧸ Ideal.span
  {a}))).Modules) :
    ((DerivedCategory.singleFunctor (Spec (CommRingCat.of (R ⧸ Ideal.span {a}))).Modules 1).obj
      Q)⟦(1 : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor (Spec (CommRingCat.of (R ⧸ Ideal.span {a}))).Modules 0).obj Q
        :=
  ((DerivedCategory.singleFunctors (Spec (CommRingCat.of (R ⧸ Ideal.span {a}))).Modules).shiftIso 1
    0 1 (by omega)).app
    Q

/-- The actual original extension class under the installed single-derived adjunction. -/
public def principalCoefficientExtensionMate :
    (DerivedCategory.singleFunctor (Spec (CommRingCat.of (R ⧸ Ideal.span {a}))).Modules 0).obj
      (principalCoefficientQuotientSheaf a M) ⟶
        (DerivedCategory.Plus.ι.obj (principalDerivedObject a M))⟦(1 : ℤ)⟧ :=
  (closedImmersionRightAdjunction (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span
    {a}))))).singleDerivedHomEquivOfInjectiveResolution
    (principalCoefficientQuotientSheaf a M) (injectiveResolution M) 1
      (principalCoefficientSequence_shortExact a M hM).extClass.hom

include ha in
/-- The actual extension mate is an isomorphism, proved by regularity and original
Ext exactness. No counit equality or purity isomorphism is an input. -/
public theorem principalCoefficientExtensionMate_isIso :
    IsIso (principalCoefficientExtensionMate a M hM) := by
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))
  let H := fullyFaithfulPushforwardOfClosedImmersion i
  let := H.full
  let := H.faithful
  let e : (DerivedCategory.Plus.ι.obj (principalDerivedObject a M))⟦(1 : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor (Spec (CommRingCat.of (R ⧸ Ideal.span {a}))).Modules 0).obj
        (principalCoefficientQuotientSheaf a M) :=
    (CategoryTheory.shiftFunctor (DerivedCategory (Spec (CommRingCat.of (R ⧸ Ideal.span
      {a}))).Modules) (1 : ℤ)).mapIso
      (DerivedCategory.Plus.ι.mapIso
        (derivedClosedImmersionRightAdjointPrincipalKoszulIso a ha M (injectiveResolution M) hM)) ≪≫
          principalSingleShiftIso a (principalCoefficientQuotientSheaf a M)
  exact CategoryTheory.Adjunction.scalarExtensionMate_isIso
    (closedImmersionRightAdjunction i) a M (principalCoefficientQuotientSheaf a M)
    (principalCoefficientQuotientMap a M) (principalCoefficientSequence_zero a M)
    (principalCoefficientSequence_shortExact a M hM)
    (principalScalar_pushforward_eq_zero a) e

/-- The positive degree-one purity comparison is the inverse actual extension mate. -/
public def derivedClosedImmersionRightAdjointPrincipalDegreeOneIso :
    (DerivedCategory.Plus.ι.obj (principalDerivedObject a M))⟦(1 : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor (Spec (CommRingCat.of (R ⧸ Ideal.span {a}))).Modules 0).obj
        (principalCoefficientQuotientSheaf a M) := by
  letI := principalCoefficientExtensionMate_isIso a ha M hM
  exact (asIso (principalCoefficientExtensionMate a M hM)).symm

/-- Native single and shift full faithfulness return the unshifted bounded-below value. -/
public def derivedClosedImmersionRightAdjointPrincipalIso :
    principalDerivedObject a M ≅
      (DerivedCategory.Plus.singleFunctor (Spec (CommRingCat.of (R ⧸ Ideal.span {a}))).Modules
        1).obj
        (principalCoefficientQuotientSheaf a M) :=
  (DerivedCategory.Plus.ι : DerivedCategory.Plus (Spec (CommRingCat.of (R ⧸ Ideal.span
    {a}))).Modules ⥤ _).preimageIso
    ((CategoryTheory.shiftFunctor (DerivedCategory (Spec (CommRingCat.of (R ⧸ Ideal.span
      {a}))).Modules) (1 : ℤ)).preimageIso
      (derivedClosedImmersionRightAdjointPrincipalDegreeOneIso a ha M hM ≪≫
        (principalSingleShiftIso a (principalCoefficientQuotientSheaf a M)).symm))

/-- The original positive homology comparison, with its genuine quotient-sheaf action. -/
public def derivedClosedImmersionRightAdjointPrincipalHomologyIso :
    derivedClosedImmersionRightAdjointHomology (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (Ideal.span {a})))) M 1 ≅
      principalCoefficientQuotientSheaf a M :=
  (DerivedCategory.Plus.homologyFunctor (Spec (CommRingCat.of (R ⧸ Ideal.span {a}))).Modules
    1).mapIso
    (derivedClosedImmersionRightAdjointPrincipalIso a ha M hM) ≪≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
        (C := (Spec (CommRingCat.of (R ⧸ Ideal.span {a}))).Modules) 1).app
          (principalCoefficientQuotientSheaf a M)

/-- The positive comparison retains exactly the original coefficient extension class
under the installed derived adjunction, including its sign. -/
public theorem derivedClosedImmersionRightAdjointPrincipalDegreeOneIso_counit :
    ((closedImmersionRightAdjunction (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span
      {a}))))).singleDerivedHomEquivOfInjectiveResolution
      (principalCoefficientQuotientSheaf a M) (injectiveResolution M) 1).symm
        (derivedClosedImmersionRightAdjointPrincipalDegreeOneIso a ha M hM).inv =
      (principalCoefficientSequence_shortExact a M hM).extClass.hom := by
  change ((closedImmersionRightAdjunction (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
    (Ideal.span {a}))))).singleDerivedHomEquivOfInjectiveResolution
    (principalCoefficientQuotientSheaf a M) (injectiveResolution M) 1).symm
      (principalCoefficientExtensionMate a M hM) = _
  exact ((closedImmersionRightAdjunction (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span
    {a}))))).singleDerivedHomEquivOfInjectiveResolution
    (principalCoefficientQuotientSheaf a M) (injectiveResolution M) 1).symm_apply_apply _

/-- The unshifted value has the same original positive degree-one normalization. -/
public theorem derivedClosedImmersionRightAdjointPrincipalIso_shift_inv :
    (principalSingleShiftIso a (principalCoefficientQuotientSheaf a M)).inv ≫
      (CategoryTheory.shiftFunctor (DerivedCategory (Spec (CommRingCat.of (R ⧸ Ideal.span
        {a}))).Modules) (1 :
        ℤ)).map
        (DerivedCategory.Plus.ι.map
          (derivedClosedImmersionRightAdjointPrincipalIso a ha M hM).inv) =
      (derivedClosedImmersionRightAdjointPrincipalDegreeOneIso a ha M hM).inv := by
  exact principalTwoPreimageInv
    (DerivedCategory.Plus.ι : DerivedCategory.Plus
      (Spec (CommRingCat.of (R ⧸ Ideal.span {a}))).Modules ⥤ _)
    (CategoryTheory.shiftFunctor
      (DerivedCategory (Spec (CommRingCat.of (R ⧸ Ideal.span {a}))).Modules) (1 : ℤ))
    (X := principalDerivedObject a M)
    (Y := (DerivedCategory.Plus.singleFunctor
      (Spec (CommRingCat.of (R ⧸ Ideal.span {a}))).Modules 1).obj
        (principalCoefficientQuotientSheaf a M))
    (derivedClosedImmersionRightAdjointPrincipalDegreeOneIso a ha M hM)
    (principalSingleShiftIso a (principalCoefficientQuotientSheaf a M))

/-- Actual counit of the unshifted installed right adjoint, with the original positive row. -/
public theorem derivedClosedImmersionRightAdjointPrincipalIso_counit :
    ((closedImmersionRightAdjunction (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span
      {a}))))).singleDerivedHomEquivOfInjectiveResolution
      (principalCoefficientQuotientSheaf a M) (injectiveResolution M) 1).symm
        ((principalSingleShiftIso a (principalCoefficientQuotientSheaf a M)).inv ≫
          (CategoryTheory.shiftFunctor (DerivedCategory (Spec (CommRingCat.of (R ⧸ Ideal.span
            {a}))).Modules) (1 :
            ℤ)).map
            (DerivedCategory.Plus.ι.map
              (derivedClosedImmersionRightAdjointPrincipalIso a ha M hM).inv)) =
      (principalCoefficientSequence_shortExact a M hM).extClass.hom := by
  let adj := closedImmersionRightAdjunction
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))))
  exact (congrArg
    (adj.singleDerivedHomEquivOfInjectiveResolution
      (principalCoefficientQuotientSheaf a M) (injectiveResolution M) 1).symm
    (derivedClosedImmersionRightAdjointPrincipalIso_shift_inv a ha M hM)).trans
      (derivedClosedImmersionRightAdjointPrincipalDegreeOneIso_counit a ha M hM)

omit [IsNoetherianRing R] in
/-- The actual section boundary is positive composition with the same original row class. -/
public theorem principalCoefficientSequence_connecting
    (x : Ext.{u + 1} (C := (Spec R).Modules)
      (SheafOfModules.unit (Spec R).ringCatSheaf) (principalCoefficientSequence a M).X₃ 0) :
    AlgebraicGeometry.Scheme.Cohomology.moduleExtCohomologyMap (Spec R) M 1
        (x.comp (principalCoefficientSequence_shortExact a M hM).extClass rfl) =
      AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyConnectingOfHom (Spec R)
        (Scheme.ΓSpecIso R).inv.hom (principalCoefficientSequence a M)
        (principalCoefficientSequence_shortExact a M hM) 0
        (AlgebraicGeometry.Scheme.Cohomology.moduleExtCohomologyMap (Spec R)
          (principalCoefficientSequence a M).X₃ 0 x) :=
  AlgebraicGeometry.Scheme.Cohomology.moduleExtCohomologyMap_connectingOfHom
    (Spec R) (Scheme.ΓSpecIso R).inv.hom (principalCoefficientSequence a M)
      (principalCoefficientSequence_shortExact a M hM) 0 x

end PositivePurity
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] standardHasDerivedCategory principalSheafHasExt principalAmbientLinear
  principalModuleHasExt

section CoefficientNaturality

variable {R : CommRingCat.{u}} (a b : R)
  (M N : (Spec R).Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
  (hM : IsSMulRegular (moduleSpecΓFunctor.obj M) a)
  (hN : IsSMulRegular (moduleSpecΓFunctor.obj N) b)
  (l r : M ⟶ N) (h : l ≫ (b • 𝟙 N) = (a • 𝟙 M) ≫ r)

/-- The map on the actual closed-pushforward quotient determined by the original row. -/
public def principalCoefficientRowQuotientMap :
    (principalCoefficientSequence a M).X₃ ⟶ (principalCoefficientSequence b N).X₃ := by
  let := (principalCoefficientSequence_shortExact a M hM).epi_g
  exact (principalCoefficientSequence_shortExact a M hM).exact.desc
    (r ≫ principalCoefficientQuotientMap b N) (by
      change (a • 𝟙 M) ≫ (r ≫ principalCoefficientQuotientMap b N) = 0
      rw [← Category.assoc, ← h, Category.assoc, principalCoefficientSequence_zero, comp_zero])

/-- The original quotient maps commute on every original coefficient section. -/
@[reassoc]
public theorem principalCoefficientRowQuotientMap_quotient :
    principalCoefficientQuotientMap a M ≫ principalCoefficientRowQuotientMap a b M N hM l r h =
      r ≫ principalCoefficientQuotientMap b N := by
  let := (principalCoefficientSequence_shortExact a M hM).epi_g
  exact (principalCoefficientSequence_shortExact a M hM).exact.g_desc _ _

/-- A map between the actual scalar rows, with no choice on the quotient. -/
public def principalCoefficientRowMap : principalCoefficientSequence a M ⟶
  principalCoefficientSequence b N where
  τ₁ := l
  τ₂ := r
  τ₃ := principalCoefficientRowQuotientMap a b M N hM l r h
  comm₁₂ := h
  comm₂₃ := (principalCoefficientRowQuotientMap_quotient a b M N hM l r h).symm

/-- The original positive extension class retains the original row naturality. -/
public theorem principalCoefficientRowMap_extClass :
    (principalCoefficientSequence_shortExact a M hM).extClass.comp (Ext.mk₀ l) (add_zero 1) =
      (Ext.mk₀ (principalCoefficientRowQuotientMap a b M N hM l r h)).comp
        (principalCoefficientSequence_shortExact b N hN).extClass (zero_add 1) :=
  ShortComplex.ShortExact.extClass_naturality
    (principalCoefficientSequence_shortExact a M hM)
    (principalCoefficientSequence_shortExact b N hN)
    (principalCoefficientRowMap a b M N hM l r h)

end CoefficientNaturality

section SameEquation

variable {R : CommRingCat.{u}} (a : R)
  {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
  (hM : IsSMulRegular (moduleSpecΓFunctor.obj M) a)
  (hN : IsSMulRegular (moduleSpecΓFunctor.obj N) a) (f : M ⟶ N)

omit [M.IsQuasicoherent] [N.IsQuasicoherent] in
private theorem principalCoefficientScalar_comm : f ≫ (a • 𝟙 N) = (a • 𝟙 M) ≫ f := by
  simp only [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]

/-- The native quotient-sheaf map descends through the fully faithful original pushforward. -/
public def principalCoefficientMap : principalCoefficientQuotientSheaf a M ⟶
  principalCoefficientQuotientSheaf a N :=
  (fullyFaithfulPushforwardOfClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
    (Ideal.span {a}))))).preimage
    (principalCoefficientRowQuotientMap a a M N hM f f (by
      simp only [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]))

/-- Descent retains exactly the actual quotient map. -/
public theorem principalCoefficientMap_pushforward :
    (pushforward (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))))).map
      (principalCoefficientMap a hM f) =
      principalCoefficientRowQuotientMap a a M N hM f f (by
        simp only [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]) :=
  (fullyFaithfulPushforwardOfClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
    (Ideal.span {a}))))).map_preimage _

/-- The positive original mate is natural for the original coefficient map and its quotient. -/
public theorem principalCoefficientExtensionMate_naturality :
    (DerivedCategory.singleFunctor (Spec (CommRingCat.of (R ⧸ Ideal.span {a}))).Modules 0).map
        (principalCoefficientMap a hM f) ≫ principalCoefficientExtensionMate a N hN =
      principalCoefficientExtensionMate a M hM ≫
        (CategoryTheory.shiftFunctor (DerivedCategory (Spec (CommRingCat.of (R ⧸ Ideal.span
          {a}))).Modules) (1 :
          ℤ)).map
          (DerivedCategory.Plus.ι.map
            ((derivedClosedImmersionRightAdjointPlus (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
              (Ideal.span {a}))))).map
              ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).map f))) := by
  let adj := closedImmersionRightAdjunction (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
    (Ideal.span {a}))))
  let I := injectiveResolution M
  let J := injectiveResolution N
  let φ : InjectiveResolution.Hom I J f := principalResolutionHom f I J
  let q := principalCoefficientMap a hM f
  let hS := principalCoefficientSequence_shortExact a M hM
  let hS' := principalCoefficientSequence_shortExact a N hN
  let F : (Spec (CommRingCat.of (R ⧸ Ideal.span {a}))).Modules ⥤ (Spec R).Modules :=
    pushforward (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))))
  let e : Ext.{u + 1} (F.obj (principalCoefficientQuotientSheaf a M)) M 1 := hS.extClass
  let e' : Ext.{u + 1} (F.obj (principalCoefficientQuotientSheaf a N)) N 1 := hS'.extClass
  let q₀ : F.obj (principalCoefficientQuotientSheaf a M) ⟶
      F.obj (principalCoefficientQuotientSheaf a N) :=
    principalCoefficientRowQuotientMap a a M N hM f f (principalCoefficientScalar_comm a f)
  have hrow : e.comp (Ext.mk₀ f) (add_zero 1) = (Ext.mk₀ q₀).comp e' (zero_add 1) :=
    principalCoefficientRowMap_extClass a a M N hM hN f f
      (principalCoefficientScalar_comm a f)
  have hq : F.map q = q₀ := principalCoefficientMap_pushforward a hM f
  have hext : e.comp (Ext.mk₀ f) (add_zero 1) = (Ext.mk₀ (F.map q)).comp e' (zero_add 1) :=
    hrow.trans (congrArg (fun k => (Ext.mk₀ k).comp e' (zero_add 1)) hq.symm)
  have hw : e.hom ≫
      (CategoryTheory.shiftFunctor (DerivedCategory (Spec R).Modules) (1 : ℤ)).map
        ((DerivedCategory.singleFunctor (Spec R).Modules 0).map f) =
      (DerivedCategory.singleFunctor (Spec R).Modules 0).map (F.map q) ≫ e'.hom :=
    principalExtHomNaturality (F.map q) f e e' hext
  calc
    _ = adj.singleDerivedHomEquivOfInjectiveResolution (principalCoefficientQuotientSheaf a M) J 1
        ((DerivedCategory.singleFunctor (Spec R).Modules 0).map
          ((pushforward (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))))).map q)
            ≫ hS'.extClass.hom) :=
      (adj.singleDerivedHomEquivOfInjectiveResolution_naturality_left
        (principalCoefficientQuotientSheaf a M) J 1 q hS'.extClass.hom).symm
    _ = adj.singleDerivedHomEquivOfInjectiveResolution (principalCoefficientQuotientSheaf a M) J 1
        (hS.extClass.hom ≫
          (CategoryTheory.shiftFunctor (DerivedCategory (Spec R).Modules) (1 : ℤ)).map
            ((DerivedCategory.singleFunctor (Spec R).Modules 0).map f)) :=
      congrArg (adj.singleDerivedHomEquivOfInjectiveResolution
        (principalCoefficientQuotientSheaf a M) J 1) hw.symm
    _ = _ := adj.singleDerivedHomEquivOfInjectiveResolution_naturality_right
      (principalCoefficientQuotientSheaf a M) I 1 φ hS.extClass.hom

end SameEquation

section ChangeEquation

variable {R : CommRingCat.{u}} (a : R) (u : Rˣ)
  (M : (Spec R).Modules) [M.IsQuasicoherent]
  (hM : IsSMulRegular (moduleSpecΓFunctor.obj M) a)

omit [M.IsQuasicoherent] in
include hM in
/-- The same actual coefficient remains regular under a unit change of equation. -/
public theorem principalCoefficientRegular_unit_mul :
    IsSMulRegular (moduleSpecΓFunctor.obj M) ((u : R) * a) :=
  (u.isSMulRegular (moduleSpecΓFunctor.obj M)).mul hM

omit [M.IsQuasicoherent] in
private theorem principalChangeEquation_square :
    (𝟙 M) ≫ (((u : R) * a) • 𝟙 M) = (a • 𝟙 M) ≫ ((u : R) • 𝟙 M) := by
  simp only [Linear.comp_smul, Category.comp_id, smul_smul]

/-- The actual change-of-equation map on the two closed-pushforward quotient coefficients.
It uses multiplication by u in the middle of the original row. -/
public def principalChangeEquationMap :
    (principalCoefficientSequence a M).X₃ ⟶
      (principalCoefficientSequence ((u : R) * a) M).X₃ :=
  principalCoefficientRowQuotientMap a ((u : R) * a) M M hM (𝟙 M) ((u : R) • 𝟙 M)
    (by simp only [Linear.comp_smul, Category.comp_id, smul_smul])

/-- Original quotient representatives are multiplied by the same unit. -/
@[reassoc]
public theorem principalChangeEquationMap_quotient :
    principalCoefficientQuotientMap a M ≫ principalChangeEquationMap a u M hM =
      ((u : R) • 𝟙 M) ≫ principalCoefficientQuotientMap ((u : R) * a) M :=
  principalCoefficientRowQuotientMap_quotient a ((u : R) * a) M M hM
    (𝟙 M) ((u : R) • 𝟙 M) (principalChangeEquation_square a u M)

/-- The positive extension class transforms by the original unit change of equation,
with no sign or arbitrary scalar introduced. -/
public theorem principalChangeEquationMap_extClass :
    (principalCoefficientSequence_shortExact a M hM).extClass =
      (Ext.mk₀ (principalChangeEquationMap a u M hM)).comp
        (principalCoefficientSequence_shortExact ((u : R) * a) M
          (principalCoefficientRegular_unit_mul a u M hM)).extClass (zero_add 1) := by
  exact (Ext.comp_mk₀_id (principalCoefficientSequence_shortExact a M hM).extClass).symm.trans
    (principalCoefficientRowMap_extClass a ((u : R) * a) M M hM
      (principalCoefficientRegular_unit_mul a u M hM) (𝟙 M) ((u : R) • 𝟙 M)
      (principalChangeEquation_square a u M))

/-- The equation change uses the literal canonical equality of the two principal ideals. -/
public theorem principalChangeEquation_ideal : Ideal.span {((u : R) * a)} = Ideal.span {a} :=
  Ideal.span_singleton_mul_left_unit u.isUnit a

end ChangeEquation

section Localization

variable {R : CommRingCat.{u}} [IsNoetherianRing R] (a : R)
  (ha : IsSMulRegular R a) (M : (Spec R).Modules) [M.IsQuasicoherent]
  (J : InjectiveResolution M) (t : R)

omit [IsNoetherianRing R] in
private theorem principalLocalization_flat :
    (algebraMap R (Localization.Away t)).Flat :=
  RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization.Away t) (Submonoid.powers t))

public local instance principalLocalization_preservesFiniteLimits :
    PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R (Localization.Away t))) :=
  ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ (principalLocalization_flat t)

public local instance principalLocalization_preservesFiniteColimits :
    PreservesFiniteColimits (ModuleCat.extendScalars (algebraMap R (Localization.Away t))) :=
  ModuleCat.extendScalars_preservesFiniteColimits_of_flat _ (principalLocalization_flat t)

omit [IsNoetherianRing R] in
public local instance principalLocalizedClosedImmersion :
    IsClosedImmersion (Spec.map
      (CommRingCat.ofHom (IsLocalization.Away.map (Localization.Away t)
        (Localization.Away (Ideal.Quotient.mk (Ideal.span {a}) t))
        (Ideal.Quotient.mk (Ideal.span {a})) t))) :=
  Scheme.isClosedImmersion_specMap_localizationAway
    (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))) t

omit [IsNoetherianRing R] in
/-- The original geometric principal-open restriction sends a quotient representative
to the original exact scalar-extension map of its Koszul class. -/
public theorem principalResolutionSections_localization_mk (x : moduleSpecΓFunctor.obj M) :
    affineClosedRightAdjointResolutionExtAddEquiv
        (CommRingCat.ofHom (IsLocalization.Away.map (Localization.Away t)
          (Localization.Away (Ideal.Quotient.mk (Ideal.span {a}) t))
          (Ideal.Quotient.mk (Ideal.span {a})) t))
        (affineOpenRestrictedInjectiveResolution
          (CommRingCat.ofHom (algebraMap R (Localization.Away t))) J) 1
        (closedImmersionQuotientLocalizationHomologyMap (Ideal.span {a}) t J 1
          ((principalResolutionSectionsLinearEquiv a ha M J).symm (Submodule.Quotient.mk x))) =
      ((Ext.mk₀ (closedImmersionQuotientLocalizationSourceIso (Ideal.span {a}) t).inv).comp
        ((singleIdealExtOneClass a ha (moduleSpecΓFunctor.obj M) x).mapExactFunctor
          (ModuleCat.extendScalars (algebraMap R (Localization.Away t)))) (zero_add 1)).comp
        (Ext.mk₀ (affineRestrictGlobalSectionsIso
          (CommRingCat.ofHom (algebraMap R (Localization.Away t))) M).hom) (add_zero 1) := by
  let z : principalCoefficientQuotient a M := Submodule.Quotient.mk x
  let y : (principalResolutionSections a J).homology 1 :=
    (principalResolutionSectionsLinearEquiv a ha M J).symm z
  have hloc := closedImmersionQuotientLocalizationHomologyMap_ext (Ideal.span {a}) t J 1 y
  have hclass : affineClosedRightAdjointResolutionExtAddEquiv
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))) J 1 y =
      singleIdealExtOneClass a ha (moduleSpecΓFunctor.obj M) x :=
    principalResolutionSectionsLinearEquiv_symm_mk a ha M J x
  exact hloc.trans (congrArg
    (fun e : Ext.{u + 1} (ModuleCat.of R (R ⧸ Ideal.span {a}))
        (moduleSpecΓFunctor.obj M) 1 =>
      ((Ext.mk₀ (closedImmersionQuotientLocalizationSourceIso (Ideal.span {a}) t).inv).comp
        (e.mapExactFunctor (ModuleCat.extendScalars (algebraMap R (Localization.Away t))))
          (zero_add 1)).comp
        (Ext.mk₀ (affineRestrictGlobalSectionsIso
          (CommRingCat.ofHom (algebraMap R (Localization.Away t))) M).hom) (add_zero 1)) hclass)

/-- Original principal-open restriction localizes every degree of the actual resolution. -/
public theorem principalResolutionSections_localization (q : ℤ) :
    IsLocalizedModule (Submonoid.powers (Ideal.Quotient.mk (Ideal.span {a}) t))
      (closedImmersionQuotientLocalizationHomologyMap (Ideal.span {a}) t J q).hom :=
  closedImmersionQuotientLocalizationHomologyMap_isLocalized (Ideal.span {a}) J t q

omit [IsNoetherianRing R] in
/-- The positive counit class localizes as the original row class, under the
actual exact sheaf restriction. -/
public theorem principalCoefficientSequence_localization_extClass
    (hM : IsSMulRegular (moduleSpecΓFunctor.obj M) a) :
    (principalCoefficientSequence_shortExact a M hM).extClass.mapExactFunctor
        (restrictFunctor (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t))))) =
      ((principalCoefficientSequence_shortExact a M hM).map_of_exact
        (restrictFunctor (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away
          t)))))).extClass :=
  Ext.mapExactFunctor_extClass _ _

end Localization
end AlgebraicGeometry.Scheme.Modules
