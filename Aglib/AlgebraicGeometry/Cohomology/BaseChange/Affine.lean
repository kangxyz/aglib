/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Field
public import Aglib.AlgebraicGeometry.Cohomology.Injective.SectionCycles
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.Ring.Constructions
/-!
# Canonical degree-zero cohomology base change

The degree-zero comparison identifies the existing Ext pullback with the
actual map on global sections. The resulting linear commuting square retains
the constant-sheaf transport and structural scalar actions used by
`structureCohomologyBaseChangeMap`. Its bijectivity is equivalent to bijectivity
of the actual global-sections tensor comparison.

For affine field schemes the comparison is bijective, by the proved affine
pullback/global-sections pushout theorem and the tensor-product pushout.
Neither properness nor a cohomology base-change premise is used in that result.
Positive-degree affine acyclicity and the general proper base-change family
are not proved here.

Source basis: project revision `f1a725686388bcc5d2eb9c9ec0971d7400cf4c7a`,
continued against `914476dd55baa6feaef45710e946922ea011eb0c`, and mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The affine input is mathlib's
`isPushout_appTop_of_isPullback`; the algebraic input is
`CommRingCat.isPushout_tensorProduct`.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.FlatBaseChange` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- In degree zero the Ext construction is the actual composite of sheaf maps. -/
theorem zariskiCohomologyMap_addEquiv₀
    (A : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (a : (zariskiPullback f).obj A ⟶ B) (x : Sheaf.H.{u + 1} A 0) :
    Abelian.Ext.addEquiv₀ (zariskiCohomologyMap f A B a 0 x) =
      (constantPullbackIso f).inv.app (AddCommGrpCat.of (ULift.{u} ℤ)) ≫
        (zariskiPullback f).map (Abelian.Ext.addEquiv₀ x) ≫ a := by
  apply (Abelian.Ext.mk₀_bijective _ _).injective
  rw [Abelian.Ext.mk₀_addEquiv₀_apply]
  conv_lhs => rw [← Abelian.Ext.mk₀_addEquiv₀_apply x]
  change ((Abelian.Ext.mk₀ _).comp
    ((Abelian.Ext.mk₀ _).mapExactFunctor (zariskiPullback f)) (Nat.zero_add 0)).comp
      (Abelian.Ext.mk₀ a) (Nat.add_zero 0) = _
  simp only [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀, Category.assoc]

/-- Constant-sheaf transport was chosen by the global-sections adjunction,
so its effect on degree-zero classes is the actual adjoint coefficient map. -/
theorem zariskiCohomologyMap_equiv₀
    (A : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (a : (zariskiPullback f).obj A ⟶ B) (x : Sheaf.H.{u + 1} A 0) :
    Sheaf.H.equiv₀ B isTerminalTop (zariskiCohomologyMap f A B a 0 x) =
      (pushforwardSectionsIso f).hom.app B
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
          f.base).homEquiv A B a).hom.app (op ⊤))
          (Sheaf.H.equiv₀ A isTerminalTop x)) := by
  let adjY := constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
    isTerminalTop
  let adjX := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    isTerminalTop
  let adjf := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base
  let adj := (adjY.comp adjf).ofNatIsoRight (pushforwardSectionsIso f)
  change integerSheafHomEquiv B
    (Abelian.Ext.addEquiv₀ (zariskiCohomologyMap f A B a 0 x)) = _
  rw [zariskiCohomologyMap_addEquiv₀]
  change (AddCommGrpCat.uliftZMultiplesAddEquiv _)
    (adjX.homEquiv _ _ ((adj.leftAdjointUniq adjX).inv.app _ ≫
      (zariskiPullback f).map (Abelian.Ext.addEquiv₀ x) ≫ a)) = _
  rw [Adjunction.leftAdjointUniq_inv_app, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit,
    Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change (AddCommGrpCat.uliftZMultiplesAddEquiv _)
    (adjY.homEquiv _ _
      (adjf.homEquiv _ _ ((zariskiPullback f).map (Abelian.Ext.addEquiv₀ x) ≫ a)) ≫
        (pushforwardSectionsIso f).hom.app B) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  rfl

/-- In degree zero the constructed structure-sheaf pullback is the actual
ring map on global sections. -/
theorem structureCohomologyPullback_equiv₀
    (x : Sheaf.H.{u + 1} (structureAddSheaf Y) 0) :
    Sheaf.H.equiv₀ (structureAddSheaf X) isTerminalTop
        (structureCohomologyPullback f 0 x) =
      f.appTop (Sheaf.H.equiv₀ (structureAddSheaf Y) isTerminalTop x) := by
  rw [structureCohomologyPullback, zariskiCohomologyMap_equiv₀]
  simp only [structurePullbackMap, Equiv.apply_symm_apply]
  change (structureAddSheaf X).obj.map _
    (f.appTop (Sheaf.H.equiv₀ (structureAddSheaf Y) isTerminalTop x)) = _
  change (structureAddSheaf X).obj.map (𝟙 (op ⊤)) _ = _
  simp only [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

open AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct

universe u

variable {F : Type u} [Field F] (K : Type u) [Field K] [Algebra F K]

attribute [local instance] globalSectionsModule

/-- Restriction of scalars on the actual global sections after field base change. -/
abbrev baseChangeGlobalSectionsModule (X : FScheme F) :
    Module F Γ((fieldBaseChange K X).left, ⊤) :=
  Module.compHom _ (algebraMap F K)

attribute [local instance] baseChangeGlobalSectionsModule

instance baseChangeGlobalSectionsScalarTower (X : FScheme F) :
    IsScalarTower F K Γ((fieldBaseChange K X).left, ⊤) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

/-- The actual global-sections pullback along the field-base-change projection,
with its structural F-linear scalar action. -/
def fieldBaseChangeSectionsLinear (X : FScheme F) :
    Γ(X.left, ⊤) →ₗ[F] Γ((fieldBaseChange K X).left, ⊤) where
  toFun := (pullback.fst X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap F K)))).appTop
  map_add' := map_add _
  map_smul' a x := by
    change (pullback.fst X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap F K)))).appTop (constants X a * x) =
      constants (fieldBaseChange K X) (algebraMap F K a) *
        (show Γ((fieldBaseChange K X).left, ⊤) from
          (pullback.fst X.hom
            (Spec.map (CommRingCat.ofHom (algebraMap F K)))).appTop x)
    rw [map_mul]
    exact congrArg (fun z : Γ((fieldBaseChange K X).left, ⊤) ↦
      z * (show Γ((fieldBaseChange K X).left, ⊤) from
        (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap F K)))).appTop x))
      (map_constants_of_baseMap (algebraMap F K) (fieldBaseChange K X) X
        (pullback.fst _ _) pullback.condition a)

/-- The canonical tensor comparison on global sections, constructed from the
actual projection and structural constants. -/
def structureSectionsBaseChangeMap (X : FScheme F) :
    K ⊗[F] Γ(X.left, ⊤) →ₗ[K] Γ((fieldBaseChange K X).left, ⊤) :=
  (fieldBaseChangeSectionsLinear K X).liftBaseChange K

theorem structureSectionsBaseChangeMap_tmul (X : FScheme F) (a : K) (s : Γ(X.left, ⊤)) :
    structureSectionsBaseChangeMap K X (a ⊗ₜ[F] s) =
      a • (show Γ((fieldBaseChange K X).left, ⊤) from
        (pullback.fst X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap F K)))).appTop s) := rfl

/-- The exact existing Ext tensor comparison agrees with the actual
global-sections tensor comparison under the degree-zero linear equivalences. -/
theorem structureH0Equiv_baseChange (X : FScheme F) :
    (structureH0Equiv (fieldBaseChange K X)).toLinearMap.comp
        (structureCohomologyBaseChangeMap K X 0) =
      (structureSectionsBaseChangeMap K X).comp
        ((structureH0Equiv X).baseChange F K _ _).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      structureCohomologyBaseChangeMap_tmul, LinearEquiv.baseChange_tmul,
      structureSectionsBaseChangeMap_tmul, map_smul]
    exact congrArg (a • ·) (structureCohomologyPullback_equiv₀ _ x)
  | add x y hx hy =>
    simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Bijectivity of the actual H⁰ tensor comparison is exactly bijectivity
of the actual global-sections tensor comparison, for any field scheme. -/
theorem structureCohomologyBaseChangeMap_bijective_iff (X : FScheme F) :
    Function.Bijective (structureCohomologyBaseChangeMap K X 0) ↔
      Function.Bijective (structureSectionsBaseChangeMap K X) := by
  have hcomm : (structureH0Equiv (fieldBaseChange K X)) ∘
      (structureCohomologyBaseChangeMap K X 0) =
      (structureSectionsBaseChangeMap K X) ∘
        ((structureH0Equiv X).baseChange F K _ _) := by
    funext z
    exact LinearMap.congr_fun (structureH0Equiv_baseChange K X) z
  rw [← Function.Bijective.of_comp_iff' (structureH0Equiv (fieldBaseChange K X)).bijective,
    hcomm]
  exact Function.Bijective.of_comp_iff _ ((structureH0Equiv X).baseChange F K _ _).bijective

/-- The actual global sections of an affine field base change form the
pushout along the original constants map and the field extension. -/
theorem fieldBaseChangeSections_isPushout (X : FScheme F) [IsAffine X.left] :
    IsPushout (CommRingCat.ofHom (constants X))
      (CommRingCat.ofHom (algebraMap F K))
      (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap F K)))).appTop
      (CommRingCat.ofHom (constants (fieldBaseChange K X))) := by
  have h := isPushout_appTop_of_isPullback
    (IsPullback.of_hasPullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap F K))))
  refine h.of_iso (Scheme.ΓSpecIso (CommRingCat.of F)) (Iso.refl _)
    (Scheme.ΓSpecIso (CommRingCat.of K)) (Iso.refl _) ?_ ?_ ?_ ?_
  · change X.hom.appTop ≫ 𝟙 _ = (Scheme.ΓSpecIso (CommRingCat.of F)).hom ≫
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ X.hom.appTop
    simp
  · rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of F)).inv]
    simp only [← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
  · simp
  · change (fieldBaseChange K X).hom.appTop ≫ 𝟙 _ =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (fieldBaseChange K X).hom.appTop
    simp

/-- Affine degree-zero base change on actual global sections, proved from
the affine scheme pullback and the tensor-product pushout. -/
theorem structureSectionsBaseChangeMap_bijective_of_isAffine
    (X : FScheme F) [IsAffine X.left] :
    Function.Bijective (structureSectionsBaseChangeMap K X) := by
  let : Algebra F Γ(X.left, ⊤) := (constants X).toAlgebra
  let h := (fieldBaseChangeSections_isPushout K X).flip
  let ht := CommRingCat.isPushout_tensorProduct F K Γ(X.left, ⊤)
  let e : CommRingCat.of (K ⊗[F] Γ(X.left, ⊤)) ≅ Γ((fieldBaseChange K X).left, ⊤) :=
    ht.isoIsPushout _ _ h
  have hl (a : K) : e.hom.hom (a ⊗ₜ[F] (1 : Γ(X.left, ⊤))) =
      constants (fieldBaseChange K X) a := by
    exact congrArg (fun q : CommRingCat.of K ⟶ Γ((fieldBaseChange K X).left, ⊤) ↦ q.hom a)
      (IsPushout.inl_isoIsPushout_hom _ _ ht h)
  have hr (s : Γ(X.left, ⊤)) : e.hom.hom ((1 : K) ⊗ₜ[F] s) =
      (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap F K)))).appTop s := by
    exact congrArg (fun q : Γ(X.left, ⊤) ⟶ Γ((fieldBaseChange K X).left, ⊤) ↦ q.hom s)
      (IsPushout.inr_isoIsPushout_hom _ _ ht h)
  have he (z : K ⊗[F] Γ(X.left, ⊤)) :
      structureSectionsBaseChangeMap K X z = e.hom.hom z := by
    induction z using TensorProduct.inductionOn with
    | tmul a s =>
      change constants (fieldBaseChange K X) a *
        (show Γ((fieldBaseChange K X).left, ⊤) from
          (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap F K)))).appTop s) = _
      calc
        _ = e.hom.hom (a ⊗ₜ[F] (1 : Γ(X.left, ⊤))) * e.hom.hom ((1 : K) ⊗ₜ[F] s) := by
          rw [hl, hr]
        _ = e.hom.hom ((a ⊗ₜ[F] (1 : Γ(X.left, ⊤))) * ((1 : K) ⊗ₜ[F] s)) :=
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

/-- The existing canonical H⁰ tensor map is bijective for every affine field
scheme and every field extension. No proper base-change family is assumed. -/
theorem structureCohomologyBaseChangeMap_bijective_of_isAffine
    (X : FScheme F) [IsAffine X.left] :
    Function.Bijective (structureCohomologyBaseChangeMap K X 0) :=
  (structureCohomologyBaseChangeMap_bijective_iff K X).mpr
    (structureSectionsBaseChangeMap_bijective_of_isAffine K X)

end AlgebraicGeometry.Scheme.Cohomology
