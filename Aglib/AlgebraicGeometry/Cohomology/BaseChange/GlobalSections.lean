/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.Flat.IsBaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
/-!
# Degree-zero base change by finite affine covers

For every quasi-compact separated F-scheme and every field extension K/F,
the existing canonical tensor map on actual H⁰ is bijective. In particular,
this proves the degree-zero proper-field specialization. The cohomology
objects, scalar actions and degree-zero comparison are those of
`FlatBaseChange`; no proper-cohomology supplier is assumed.

The proof uses the actual sheaf gluing equalizer for a finite affine cover,
the affine-open ring pushouts obtained by restricting the scheme pullback,
and preservation of finite products and kernels by flat scalar extension.
The homological input is mathlib's `IsBaseChange.of_left_exact`, and the
finite-product input is `TensorProduct.piRight`. No positive-degree affine
acyclicity or cohomology-finiteness theorem is used or proved here.

Source basis: project `914476dd55baa6feaef45710e946922ea011eb0c` with the frozen
`FlatBaseChange` and `AffineAcyclicity` leaves; mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.GlobalSectionsBaseChange` at R5Lab
  revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {F : Type u} [Field F]

attribute [local instance] globalSectionsModule

/-- The structural scalar action on sections over an arbitrary open. -/
abbrev openSectionsModule (X : FScheme F) (U : X.left.Opens) : Module F Γ(X.left, U) :=
  (constantSection X U).toModule

attribute [local instance] openSectionsModule

/-- Restriction between actual open-section modules. -/
def openSectionsRestriction (X : FScheme F) {U V : X.left.Opens} (h : U ≤ V) :
    Γ(X.left, V) →ₗ[F] Γ(X.left, U) where
  toFun := X.left.presheaf.map (homOfLE h).op
  map_add' := map_add _
  map_smul' a s := by
    change X.left.presheaf.map (homOfLE h).op (constantSection X V a * s) =
      constantSection X U a * X.left.presheaf.map (homOfLE h).op s
    rw [map_mul, map_constantSection]

/-- Restriction from the existing structural module on global sections. -/
def globalSectionsRestriction (X : FScheme F) (U : X.left.Opens) :
    Γ(X.left, ⊤) →ₗ[F] Γ(X.left, U) where
  toFun := X.left.presheaf.map (homOfLE le_top).op
  map_add' := map_add _
  map_smul' _ _ := map_mul _ _ _

/-- The first map in the global-section equalizer for an open family. -/
def globalSectionsToCover (X : FScheme F) {ι : Type u} (U : ι → X.left.Opens) :
    Γ(X.left, ⊤) →ₗ[F] ∀ i, Γ(X.left, U i) :=
  LinearMap.pi fun i ↦ globalSectionsRestriction X (U i)

/-- The difference of the two restrictions to pairwise intersections. -/
def coverSectionsDifference (X : FScheme F) {ι : Type u} (U : ι → X.left.Opens) :
    (∀ i, Γ(X.left, U i)) →ₗ[F] ∀ p : ι × ι, Γ(X.left, U p.1 ⊓ U p.2) :=
  LinearMap.pi fun p ↦
    (openSectionsRestriction X inf_le_left).comp (LinearMap.proj p.1) -
      (openSectionsRestriction X inf_le_right).comp (LinearMap.proj p.2)

/-- A section is determined by its restrictions to an actual open cover. -/
theorem globalSectionsToCover_injective (X : FScheme F) {ι : Type u}
    (U : ι → X.left.Opens) (hU : iSup U = ⊤) :
    Function.Injective (globalSectionsToCover X U) := by
  intro s t h
  exact X.left.sheaf.eq_of_locally_eq' U ⊤ (fun _ ↦ homOfLE le_top)
    hU.ge s t (fun i ↦ congrFun h i)

/-- Actual global sections are the kernel of the difference of restrictions.
This is the sheaf gluing condition, with the structural F-module actions. -/
theorem globalSectionsToCover_exact (X : FScheme F) {ι : Type u}
    (U : ι → X.left.Opens) (hU : iSup U = ⊤) :
    Function.Exact (globalSectionsToCover X U) (coverSectionsDifference X U) := by
  intro s
  constructor
  · intro hs
    have hc : TopCat.Presheaf.IsCompatible X.left.presheaf U s := by
      intro i j
      exact sub_eq_zero.mp (congrFun hs (i, j))
    obtain ⟨t, ht, _⟩ := X.left.sheaf.existsUnique_gluing' U ⊤
      (fun _ ↦ homOfLE le_top) hU.ge s hc
    exact ⟨t, funext ht⟩
  · rintro ⟨t, rfl⟩
    funext p
    change X.left.presheaf.map (homOfLE inf_le_left).op
        (X.left.presheaf.map (homOfLE le_top).op t) -
      X.left.presheaf.map (homOfLE inf_le_right).op
        (X.left.presheaf.map (homOfLE le_top).op t) = 0
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      ← X.left.presheaf.map_comp, ← X.left.presheaf.map_comp]
    exact sub_self _

section FieldBaseChange

variable (K : Type u) [Field K] [Algebra F K]

/-- The projection of the existing scheme field base change. -/
abbrev fieldBaseChangeProjection (X : FScheme F) : (fieldBaseChange K X).left ⟶ X.left :=
  pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap F K)))

/-- Restriction of the structural K-action on sections through F → K. -/
abbrev baseChangeOpenSectionsModule (X : FScheme F) (V : (fieldBaseChange K X).left.Opens) :
    Module F Γ((fieldBaseChange K X).left, V) :=
  Module.compHom _ (algebraMap F K)

attribute [local instance] baseChangeOpenSectionsModule baseChangeGlobalSectionsModule

instance baseChangeOpenSectionsScalarTower (X : FScheme F)
    (V : (fieldBaseChange K X).left.Opens) :
    IsScalarTower F K Γ((fieldBaseChange K X).left, V) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

/-- Pullback of actual sections over an arbitrary open along field base change. -/
def fieldBaseChangeOpenSectionsLinear (X : FScheme F) (U : X.left.Opens) :
    Γ(X.left, U) →ₗ[F] Γ((fieldBaseChange K X).left, fieldBaseChangeProjection K X ⁻¹ᵁ U) where
  toFun := (fieldBaseChangeProjection K X).app U
  map_add' := map_add _
  map_smul' a s := by
    change (fieldBaseChangeProjection K X).app U (constantSection X U a * s) =
      constantSection (fieldBaseChange K X) (fieldBaseChangeProjection K X ⁻¹ᵁ U)
        (algebraMap F K a) * (fieldBaseChangeProjection K X).app U s
    rw [map_mul]
    exact congrArg (fun z ↦ z * (fieldBaseChangeProjection K X).app U s)
      (app_constantSection_of_baseMap (algebraMap F K) (fieldBaseChange K X) X
        (fieldBaseChangeProjection K X) pullback.condition U a)

/-- The tensor comparison on actual sections over an arbitrary open. -/
def structureOpenSectionsBaseChangeMap (X : FScheme F) (U : X.left.Opens) :
    K ⊗[F] Γ(X.left, U) →ₗ[K]
      Γ((fieldBaseChange K X).left, fieldBaseChangeProjection K X ⁻¹ᵁ U) :=
  (fieldBaseChangeOpenSectionsLinear K X U).liftBaseChange K

theorem structureOpenSectionsBaseChangeMap_tmul (X : FScheme F) (U : X.left.Opens)
    (a : K) (s : Γ(X.left, U)) :
    structureOpenSectionsBaseChangeMap K X U (a ⊗ₜ[F] s) =
      a • (fieldBaseChangeProjection K X).app U s := rfl

/-- Finite products of actual base-change maps are again base-change maps. -/
theorem isBaseChange_pi {ι : Type*} [Finite ι] {M N : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)]
    [∀ i, Module F (M i)] [∀ i, Module F (N i)] [∀ i, Module K (N i)]
    [∀ i, IsScalarTower F K (N i)]
    (f : ∀ i, M i →ₗ[F] N i) (hf : ∀ i, IsBaseChange K (f i)) :
    IsBaseChange K (LinearMap.pi fun i ↦ (f i).comp (LinearMap.proj i)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  refine IsBaseChange.of_equiv
    ((TensorProduct.piRight F K K M).trans
      (LinearEquiv.piCongrRight fun i ↦ (hf i).equiv)) ?_
  intro s
  ext i
  change (hf i).equiv (1 ⊗ₜ[F] s i) = f i (s i)
  rw [IsBaseChange.equiv_tmul, one_smul]

/-- Restriction to an open agrees with its global-section identification. -/
@[reassoc]
theorem open_ι_appTop_topIso {Y : Scheme.{u}} (U : Y.Opens) :
    U.ι.appTop ≫ U.topIso.hom = Y.presheaf.map (homOfLE le_top).op := by
  simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Y.presheaf.map_comp]
  rfl

/-- Restricting a scheme morphism agrees with the actual map on open sections. -/
@[reassoc]
theorem morphismRestrict_appTop_topIso {Y Z : Scheme.{u}} (f : Y ⟶ Z) (U : Z.Opens) :
    (f ∣_ U).appTop ≫ (f ⁻¹ᵁ U).topIso.hom = U.topIso.hom ≫ f.app U := by
  simp only [morphismRestrict_appTop, Scheme.Opens.topIso_hom, Category.assoc,
    ← Y.presheaf.map_comp]
  exact (f.naturality (eqToHom U.ι_image_top.symm).op).symm

/-- The actual sections over an affine open and its field-base-change preimage
form the canonical ring pushout. -/
theorem baseChangeOpenSections_isPushout (X : FScheme F) (U : X.left.Opens)
    (hU : IsAffineOpen U) :
    IsPushout (CommRingCat.ofHom (constantSection X U))
      (CommRingCat.ofHom (algebraMap F K))
      ((pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap F K)))).app U)
      (CommRingCat.ofHom (constantSection (fieldBaseChange K X)
        ((pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap F K)))) ⁻¹ᵁ U))) := by
  let p := pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap F K)))
  let q := pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap F K)))
  let : IsAffine U.toScheme := hU
  have hp := (isPullback_morphismRestrict p U).paste_vert
    (IsPullback.of_hasPullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap F K))))
  have h := isPushout_appTop_of_isPullback hp
  refine h.of_iso (Scheme.ΓSpecIso (CommRingCat.of F)) U.topIso
    (Scheme.ΓSpecIso (CommRingCat.of K)) (p ⁻¹ᵁ U).topIso ?_ ?_ ?_ ?_
  · change (U.ι ≫ X.hom).appTop ≫ U.topIso.hom =
      (Scheme.ΓSpecIso (CommRingCat.of F)).hom ≫
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ X.hom.appTop) ≫
          X.left.presheaf.map (homOfLE le_top).op
    simp only [Scheme.Hom.comp_appTop, Category.assoc,
      open_ι_appTop_topIso, Iso.hom_inv_id_assoc]
  · exact Scheme.ΓSpecIso_naturality _
  · exact morphismRestrict_appTop_topIso p U
  · change ((p ⁻¹ᵁ U).ι ≫ q).appTop ≫ (p ⁻¹ᵁ U).topIso.hom =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appTop) ≫
          (fieldBaseChange K X).left.presheaf.map (homOfLE le_top).op
    simp only [Scheme.Hom.comp_appTop, Category.assoc,
      open_ι_appTop_topIso, Iso.hom_inv_id_assoc]
    rfl

/-- Affine-open base change for the actual section tensor map. -/
theorem structureOpenSectionsBaseChangeMap_bijective_of_isAffineOpen
    (X : FScheme F) (U : X.left.Opens) (hU : IsAffineOpen U) :
    Function.Bijective (structureOpenSectionsBaseChangeMap K X U) := by
  let : Algebra F Γ(X.left, U) := (constantSection X U).toAlgebra
  let h := (baseChangeOpenSections_isPushout K X U hU).flip
  let ht := CommRingCat.isPushout_tensorProduct F K Γ(X.left, U)
  let e : CommRingCat.of (K ⊗[F] Γ(X.left, U)) ≅
      Γ((fieldBaseChange K X).left, fieldBaseChangeProjection K X ⁻¹ᵁ U) :=
    ht.isoIsPushout _ _ h
  have hl (a : K) : e.hom.hom (a ⊗ₜ[F] (1 : Γ(X.left, U))) =
      constantSection (fieldBaseChange K X) (fieldBaseChangeProjection K X ⁻¹ᵁ U) a := by
    exact congrArg (fun q : CommRingCat.of K ⟶
      Γ((fieldBaseChange K X).left, fieldBaseChangeProjection K X ⁻¹ᵁ U) ↦ q.hom a)
      (IsPushout.inl_isoIsPushout_hom _ _ ht h)
  have hr (s : Γ(X.left, U)) : e.hom.hom ((1 : K) ⊗ₜ[F] s) =
      (fieldBaseChangeProjection K X).app U s := by
    exact congrArg (fun q : Γ(X.left, U) ⟶
      Γ((fieldBaseChange K X).left, fieldBaseChangeProjection K X ⁻¹ᵁ U) ↦ q.hom s)
      (IsPushout.inr_isoIsPushout_hom _ _ ht h)
  have he (z : K ⊗[F] Γ(X.left, U)) :
      structureOpenSectionsBaseChangeMap K X U z = e.hom.hom z := by
    induction z using TensorProduct.inductionOn with
    | tmul a s =>
      change constantSection (fieldBaseChange K X) (fieldBaseChangeProjection K X ⁻¹ᵁ U) a *
        (fieldBaseChangeProjection K X).app U s = _
      calc
        _ = e.hom.hom (a ⊗ₜ[F] (1 : Γ(X.left, U))) * e.hom.hom ((1 : K) ⊗ₜ[F] s) := by
          rw [hl, hr]
        _ = e.hom.hom ((a ⊗ₜ[F] (1 : Γ(X.left, U))) * ((1 : K) ⊗ₜ[F] s)) :=
          (map_mul _ _ _).symm
        _ = e.hom.hom (a ⊗ₜ[F] s) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  have hb := ConcreteCategory.bijective_of_isIso e.hom
  constructor
  · intro z w hzw
    exact hb.1 ((he z).symm.trans (hzw.trans (he w)))
  · intro s
    obtain ⟨z, hz⟩ := hb.2 s
    exact ⟨z, (he z).trans hz⟩

/-- The actual pullback of sections on an affine open is a module base change. -/
theorem fieldBaseChangeOpenSections_isBaseChange (X : FScheme F)
    (U : X.left.Opens) (hU : IsAffineOpen U) :
    IsBaseChange K (fieldBaseChangeOpenSectionsLinear K X U) := by
  change Function.Bijective (structureOpenSectionsBaseChangeMap K X U)
  exact structureOpenSectionsBaseChangeMap_bijective_of_isAffineOpen K X U hU

/-- Pullback on the family of actual open-section modules. -/
def coverSectionsPullback (X : FScheme F) {ι : Type u} (U : ι → X.left.Opens) :
    (∀ i, Γ(X.left, U i)) →ₗ[F]
      ∀ i, Γ((fieldBaseChange K X).left, fieldBaseChangeProjection K X ⁻¹ᵁ U i) :=
  LinearMap.pi fun i ↦ (fieldBaseChangeOpenSectionsLinear K X (U i)).comp (LinearMap.proj i)

/-- Pullback commutes with restriction from global sections to a cover. -/
theorem coverSectionsPullback_globalSectionsToCover (X : FScheme F) {ι : Type u}
    (U : ι → X.left.Opens) :
    (coverSectionsPullback K X U).comp (globalSectionsToCover X U) =
      ((globalSectionsToCover (fieldBaseChange K X)
        (fun i ↦ fieldBaseChangeProjection K X ⁻¹ᵁ U i)).restrictScalars F).comp
        (fieldBaseChangeSectionsLinear K X) := by
  ext s i
  exact congrArg (fun q : Γ(X.left, ⊤) ⟶
    Γ((fieldBaseChange K X).left, fieldBaseChangeProjection K X ⁻¹ᵁ U i) ↦ q.hom s)
    ((fieldBaseChangeProjection K X).naturality (homOfLE le_top).op)

/-- Pullback commutes with the difference of restrictions to intersections. -/
theorem coverSectionsPullback_difference (X : FScheme F) {ι : Type u}
    (U : ι → X.left.Opens) :
    (coverSectionsPullback K X (fun p : ι × ι ↦ U p.1 ⊓ U p.2)).comp
        (coverSectionsDifference X U) =
      ((coverSectionsDifference (fieldBaseChange K X)
        (fun i ↦ fieldBaseChangeProjection K X ⁻¹ᵁ U i)).restrictScalars F).comp
        (coverSectionsPullback K X U) := by
  ext s p
  change (fieldBaseChangeProjection K X).app (U p.1 ⊓ U p.2)
      (X.left.presheaf.map (homOfLE inf_le_left).op (s p.1) -
        X.left.presheaf.map (homOfLE inf_le_right).op (s p.2)) = _
  rw [map_sub]
  exact congrArg₂ (· - ·)
    (congrArg (fun q : Γ(X.left, U p.1) ⟶
      Γ((fieldBaseChange K X).left, fieldBaseChangeProjection K X ⁻¹ᵁ (U p.1 ⊓ U p.2)) ↦
        q.hom (s p.1)) ((fieldBaseChangeProjection K X).naturality (homOfLE inf_le_left).op))
    (congrArg (fun q : Γ(X.left, U p.2) ⟶
      Γ((fieldBaseChange K X).left, fieldBaseChangeProjection K X ⁻¹ᵁ (U p.1 ⊓ U p.2)) ↦
        q.hom (s p.2)) ((fieldBaseChangeProjection K X).naturality (homOfLE inf_le_right).op))

/-- Finite affine covers with affine pairwise intersections prove actual
global-section base change by the sheaf equalizer and flatness. -/
theorem fieldBaseChangeSections_isBaseChange_of_finite_affine_cover
    (X : FScheme F) {ι : Type u} [Finite ι] (U : ι → X.left.Opens)
    (hcover : iSup U = ⊤) (hU : ∀ i, IsAffineOpen (U i))
    (hinter : ∀ i j, IsAffineOpen (U i ⊓ U j)) :
    IsBaseChange K (fieldBaseChangeSectionsLinear K X) := by
  have hcover' : (⨆ i, fieldBaseChangeProjection K X ⁻¹ᵁ U i) = ⊤ :=
    (fieldBaseChangeProjection K X).iSup_preimage_eq_top hcover
  exact IsBaseChange.of_left_exact K (fieldBaseChangeSectionsLinear K X)
    (coverSectionsPullback K X U)
    (coverSectionsPullback K X (fun p : ι × ι ↦ U p.1 ⊓ U p.2))
    (coverSectionsPullback_globalSectionsToCover K X U)
    (coverSectionsPullback_difference K X U)
    (isBaseChange_pi K _ (fun i ↦ fieldBaseChangeOpenSections_isBaseChange K X (U i) (hU i)))
    (isBaseChange_pi K _ (fun p : ι × ι ↦
      fieldBaseChangeOpenSections_isBaseChange K X _ (hinter p.1 p.2)))
    (globalSectionsToCover_exact X U hcover) (globalSectionsToCover_injective X U hcover)
    (globalSectionsToCover_exact (fieldBaseChange K X) _ hcover')
    (globalSectionsToCover_injective (fieldBaseChange K X) _ hcover')

/-- Quasi-compact separated field schemes satisfy base change for their
actual global sections, by a finite affine cover and its affine intersections. -/
theorem structureSectionsBaseChangeMap_bijective_of_quasiCompact_of_isSeparated
    (X : FScheme F) [QuasiCompact X.hom] [IsSeparated X.hom] :
    Function.Bijective (structureSectionsBaseChangeMap K X) := by
  classical
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : X.left.IsSeparated := ⟨by
    rw [← terminal.comp_from X.hom]
    infer_instance⟩
  obtain ⟨s, hs, he⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (X := X.left) (U := ⊤)).mp (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X.left)))
  let : Fintype s := hs.fintype
  have hcover : (⨆ i : s, (i.val : X.left.Opens)) = ⊤ := by
    simpa only [iSup_subtype] using he.symm
  have hb := fieldBaseChangeSections_isBaseChange_of_finite_affine_cover K X
    (fun i : s ↦ (i.val : X.left.Opens)) hcover
    (fun i ↦ i.val.property) (fun i j ↦ i.val.property.inf j.val.property)
  change Function.Bijective (structureSectionsBaseChangeMap K X) at hb
  exact hb

/-- The exact canonical degree-zero cohomology tensor comparison is bijective
for every quasi-compact separated field scheme and every field extension. -/
theorem structureCohomologyBaseChangeMap_bijective_zero_of_quasiCompact_of_isSeparated
    (X : FScheme F) [QuasiCompact X.hom] [IsSeparated X.hom] :
    Function.Bijective (structureCohomologyBaseChangeMap K X 0) :=
  (structureCohomologyBaseChangeMap_bijective_iff K X).mpr
    (structureSectionsBaseChangeMap_bijective_of_quasiCompact_of_isSeparated K X)

/-- The degree-zero proper-field specialization, with no proper cohomology
base-change family assumed. -/
theorem structureCohomologyBaseChangeMap_bijective_zero_of_isProper
    (X : FScheme F) [IsProper X.hom] :
    Function.Bijective (structureCohomologyBaseChangeMap K X 0) :=
  structureCohomologyBaseChangeMap_bijective_zero_of_quasiCompact_of_isSeparated K X

/-- The degree-zero equivalence induced by the existing canonical tensor map. -/
def structureCohomologyBaseChangeEquiv₀
    (X : FScheme F) [QuasiCompact X.hom] [IsSeparated X.hom] :
    K ⊗[F] structureCohomology F X 0 ≃ₗ[K]
      structureCohomology K (fieldBaseChange K X) 0 :=
  LinearEquiv.ofBijective (structureCohomologyBaseChangeMap K X 0)
    (structureCohomologyBaseChangeMap_bijective_zero_of_quasiCompact_of_isSeparated K X)

end FieldBaseChange

end AlgebraicGeometry.Scheme.Cohomology
