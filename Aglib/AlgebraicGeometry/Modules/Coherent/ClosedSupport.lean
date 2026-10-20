/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Finiteness.ClosedSupport
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StalkScalars
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Support
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeProperty
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteType
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.Support

/-!
# Coherent stalks supported at closed points

The original structural scalar actions are preserved through actual
restrictions, tilde stalks, and module-sheaf isomorphisms. Closed support
points give maximal primes on any affine chart, without a Jacobson or
finite-type premise for that step. A locally finite-type field scheme
with the displayed affine finite-type module property then has finite
field-dimensional stalks at every point of such a module.

Source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.ProperCurveFiniteness`, R5 revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`. Existing declaration
namespaces, hypotheses, universes, objects, maps, and proofs are retained.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Coherent.ClosedSupport` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`045b9049b7f69dc492cdecbf895d84ca504017e59737b9b315e6a169c0adcca2`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme (constantSection constants map_constantSection)
open _root_.AlgebraicGeometry.Scheme.Cohomology
  (app_constantSection moduleAdditiveStalk moduleAdditiveStalkMap moduleAdditiveStalkModule
    moduleAdditiveStalk_smul_eq_constantGerm moduleScalar)
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)
/- Component: Scalars. All declaration bodies preserved. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Support
universe u
variable {K : Type u} [Field K]

theorem moduleStalk_smul_germ (X : FScheme K) (M : X.left.Modules)
    (x : X.left) (U : X.left.Opens) (hx : x ∈ U) (a : K) (s : M.val.obj (op U)) :
    a • (show moduleAdditiveStalk X M x from M.presheaf.germ U x hx s) =
      M.presheaf.germ U x hx (constantSection X U a • s) := by
  change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    (moduleScalar X M a).hom) (M.presheaf.germ U x hx s) = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rfl

theorem appIso_inv_constantSection {Y X : FScheme K} (f : Y ⟶ X)
    [IsOpenImmersion f.left] (U : Y.left.Opens) (a : K) :
    (f.left.appIso U).inv (constantSection Y U a) = constantSection X (f.left ''ᵁ U) a := by
  apply (ConcreteCategory.bijective_of_isIso (f.left.appIso U).hom).injective
  rw [Iso.inv_hom_id_apply]
  rw [Scheme.Hom.appIso_hom]
  change constantSection Y U a = Y.left.presheaf.map _ (f.left.app _ (constantSection X _ a))
  rw [app_constantSection]
  exact (map_constantSection Y _ a).symm

/-- The base-field-linear stalk equivalence for restriction along an open immersion over `K`. -/
def restrictModuleStalkEquiv {Y X : FScheme K} (f : Y ⟶ X) [IsOpenImmersion f.left]
    (M : X.left.Modules) (y : Y.left) :
    moduleAdditiveStalk Y (M.restrict f.left) y ≃ₗ[K]
      moduleAdditiveStalk X M (f.left y) where
  __ := Iso.addCommGroupIsoToAddEquiv ((Scheme.Modules.restrictStalkNatIso f.left y).app M)
  map_smul' a m := by
    obtain ⟨U, hy, s, rfl⟩ := (M.restrict f.left).presheaf.exists_germ_eq m
    have he (t : Γ(M.restrict f.left, U)) :
        (Scheme.Modules.restrictStalkNatIso f.left y).hom.app M
          ((M.restrict f.left).presheaf.germ U y hy t) =
        M.presheaf.germ (f.left ''ᵁ U) (f.left y) (by simpa) t :=
      ConcreteCategory.congr_hom (Scheme.Modules.germ_restrictStalkNatIso_hom_app
        f.left y M hy) t
    change (Scheme.Modules.restrictStalkNatIso f.left y).hom.app M
        (a • (show moduleAdditiveStalk Y (M.restrict f.left) y from
          (M.restrict f.left).presheaf.germ U y hy s)) =
      a • (show moduleAdditiveStalk X M (f.left y) from
        (Scheme.Modules.restrictStalkNatIso f.left y).hom.app M
          ((M.restrict f.left).presheaf.germ U y hy s))
    rw [moduleStalk_smul_germ]
    erw [he, he]
    rw [moduleStalk_smul_germ]
    congr 1
    change Γ(M, f.left ''ᵁ U) at s
    change (f.left.appIso U).inv (constantSection Y U a) • s = _
    rw [appIso_inv_constantSection]


/-- The base-field-linear equivalence of stalks induced by a module-sheaf isomorphism. -/
def moduleStalkIsoEquiv (X : FScheme K) {M N : X.left.Modules} (e : M ≅ N) (x : X.left) :
    moduleAdditiveStalk X M x ≃ₗ[K] moduleAdditiveStalk X N x :=
  LinearEquiv.ofBijective (moduleAdditiveStalkMap X e.hom x)
    (ConcreteCategory.bijective_of_isIso ((Scheme.Modules.stalkFunctor
        X.left x).map e.hom))

/-- The constants map from `K` to the affine coordinate ring defined by the structure morphism. -/
def affineConstants (R : CommRingCat.{u}) (p : Spec R ⟶ Spec (.of K)) : K →+* R :=
  (Scheme.ΓSpecIso R).hom.hom.comp (constants (Over.mk p))

theorem tildeStalkModule_eq (R : CommRingCat.{u}) (p : Spec R ⟶ Spec (.of K))
    (M : ModuleCat R) (x : Spec R) :
    moduleAdditiveStalkModule (Over.mk p) (tilde M) x =
      Module.compHom ((tilde M).presheaf.stalk x) (affineConstants R p) := by
  apply Module.ext'
  intro a m
  let : Module ((Spec R).presheaf.stalk x) ((tilde M).presheaf.stalk x) :=
    Scheme.Cohomology.nativeModuleStalkStructure (Spec R) (tilde M) x
  let : Module ((structurePresheafInCommRingCat R).stalk x) ((tilde M).presheaf.stalk x) :=
    inferInstanceAs (Module ((structurePresheafInCommRingCat R).stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := (Spec R).toTopCat)
        (moduleStructurePresheaf R M).presheaf x))
  rw [moduleAdditiveStalk_smul_eq_constantGerm]
  change (tilde M).presheaf.stalk x at m
  change (Spec R).presheaf.germ ⊤ x trivial (constants (Over.mk p) a) • m =
    StructureSheaf.toStalk R x (affineConstants R p a) • m
  congr 1
  change (Spec R).presheaf.germ ⊤ x trivial (constants (Over.mk p) a) =
    (Spec R).presheaf.germ ⊤ x trivial
      ((Scheme.ΓSpecIso R).inv ((Scheme.ΓSpecIso R).hom (constants (Over.mk p) a)))
  rw [Iso.hom_inv_id_apply]

end AlgebraicGeometry.Scheme.Modules.Coherent.Support

end

/- Component: ChartSupport. All declaration bodies preserved. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Support
universe u
variable {K : Type u} [Field K]

/-- The literal field map defined by the structural morphism on an affine chart is finite type. -/
theorem affineConstants_finiteType (R : CommRingCat.{u})
    (p : Spec R ⟶ Spec (.of K)) [LocallyOfFiniteType p] :
    RingHom.FiniteType ((Scheme.ΓSpecIso R).hom.hom.comp (constants (Over.mk p))) := by
  have hp : p.appTop.hom.FiniteType :=
    HasRingHomProperty.appTop @LocallyOfFiniteType p inferInstance
  exact (RingHom.FiniteType.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).surjective).comp
    (hp.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).surjective))

/-- Closed support points remain closed in every actual affine open chart, hence their
prime ideals are maximal. Neither finite type of the scheme nor Jacobsonness is required. -/
theorem affineChart_support_maximal (X : FScheme K) (M : X.left.Modules)
    (hM : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType X.left M)
    (hs : ∀ x ∈ Scheme.Modules.support M, IsClosed ({x} : Set X.left))
    (R : CommRingCat.{u}) (j : Spec R ⟶ X.left) [IsOpenImmersion j] :
    ∀ p ∈ Module.support R (moduleSpecΓFunctor.obj (M.restrict j)), p.asIdeal.IsMaximal := by
  let : (M.restrict j).IsQuasicoherent := (hM R j).1
  intro p hp
  have hsp : j p ∈ Scheme.Modules.support M := by
    rw [← Scheme.Modules.support_eq_support_globalSections,
      Scheme.Modules.support_restrict] at hp
    exact hp
  apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp
  have hclosed := (hs (j p) hsp).preimage j.continuous
  have heq : j ⁻¹' ({j p} : Set X.left) = ({p} : Set (Spec R)) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact j.isOpenEmbedding.injective.eq_iff
  rw [heq] at hclosed
  exact hclosed

end AlgebraicGeometry.Scheme.Modules.Coherent.Support

end

/- Component: FiniteStalk. All declaration bodies preserved. -/
noncomputable section
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Support
universe u
variable {K : Type u} [Field K]

theorem tildeStalk_finite (R : CommRingCat.{u}) (p : Spec R ⟶ Spec (.of K))
    (M : ModuleCat R) (x : Spec R)
    (hM : letI := Module.compHom M (affineConstants R p); Module.Finite K M) :
    Module.Finite K (moduleAdditiveStalk (Over.mk p) (tilde M) x) := by
  change @Module.Finite K ((tilde M).presheaf.stalk x) _ _
    (moduleAdditiveStalkModule (Over.mk p) (tilde M) x)
  rw [tildeStalkModule_eq]
  letI := (affineConstants R p).toAlgebra
  letI := Module.compHom M (affineConstants R p)
  letI := Module.compHom ((tilde M).presheaf.stalk x) (affineConstants R p)
  letI : IsScalarTower K R M := IsScalarTower.of_compHom K R M
  letI : IsScalarTower K R ((tilde M).presheaf.stalk x) := IsScalarTower.of_compHom K R _
  letI := hM
  exact Module.localizedModule_finite x.asIdeal.primeCompl (tilde.toStalk M x).hom


theorem affineChartStalk_finite (X : FScheme K) [LocallyOfFiniteType X.hom]
    (M : X.left.Modules) (hM :
        Scheme.Modules.QuasiCoherent.affineLocallyFiniteType X.left M)
    (hs : ∀ x ∈ Scheme.Modules.support M, IsClosed ({x} : Set X.left))
    (R : CommRingCat.{u}) (j : Spec R ⟶ X.left) [IsOpenImmersion j] (y : Spec R) :
    Module.Finite K (moduleAdditiveStalk X M (j y)) := by
  let p := j ≫ X.hom
  let A : FScheme K := Over.mk p
  let a : A ⟶ X := Over.homMk j rfl
  letI : IsOpenImmersion a.left := inferInstanceAs (IsOpenImmersion j)
  let N := M.restrict j
  let G := moduleSpecΓFunctor.obj N
  have hN := hM R j
  letI : N.IsQuasicoherent := hN.1
  letI : Module.Finite R G := hN.2
  letI := (affineConstants R p).toAlgebra
  letI := Module.compHom G (affineConstants R p)
  letI : IsScalarTower K R G := IsScalarTower.of_compHom K R G
  letI : Algebra.FiniteType K R := affineConstants_finiteType R p
  letI : Module.Finite K G := Module.finite_over_field_of_support_maximal
    (affineChart_support_maximal X M hM hs R j)
  letI : Module.Finite K (moduleAdditiveStalk A (tilde G) y) :=
    tildeStalk_finite R p G y inferInstance
  letI : IsIso N.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  letI : Module.Finite K (moduleAdditiveStalk A
      (tilde ((modulesSpecToSheaf.obj N).presheaf.obj (op ⊤))) y) :=
    inferInstanceAs (Module.Finite K (moduleAdditiveStalk A (tilde G) y))
  letI : Module.Finite K (moduleAdditiveStalk A N y) :=
    Module.Finite.equiv (moduleStalkIsoEquiv A (asIso N.fromTildeΓ) y)
  letI : Module.Finite K (moduleAdditiveStalk A (M.restrict a.left) y) :=
    inferInstanceAs (Module.Finite K (moduleAdditiveStalk A N y))
  exact Module.Finite.equiv (restrictModuleStalkEquiv a M y)

theorem coherent_stalk_finite (X : FScheme K) [LocallyOfFiniteType X.hom]
    (M : X.left.Modules) (hM :
        Scheme.Modules.QuasiCoherent.affineLocallyFiniteType X.left M)
    (hs : ∀ x ∈ Scheme.Modules.support M, IsClosed ({x} : Set X.left))
        (x : X.left) :
    Module.Finite K (moduleAdditiveStalk X M x) := by
  obtain ⟨y, hy⟩ := X.left.affineOpenCover.covers x
  rw [← hy]
  exact affineChartStalk_finite X M hM hs _ _ y

end AlgebraicGeometry.Scheme.Modules.Coherent.Support

end
