/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Tensor
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeRestriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback
public import Mathlib.RingTheory.PicardGroup

/-!
# The Picard group of an affine scheme

A line bundle has singleton local bases, so it is finite locally free and
quasicoherent on every scheme. On `Spec R`, for an arbitrary commutative ring `R`,
the module of global sections of a line bundle is an invertible `R`-module: global
sections of a tensor of quasicoherent sheaves are the module tensor of global
sections, and the dual evaluation becomes `Γ(L^∨) ⊗ Γ(L) ≅ R`. Conversely, `tilde`
of an invertible module is locally rank one, because an invertible module becomes
free after localization at finitely many elements generating the unit ideal
(Mathlib's `Module.Invertible.exists_finset_free_localization`).

`picardGroupEquivCommRingPic R : PicardGroup (Spec R) ≃+ Additive (CommRing.Pic R)`
sends the class of a line bundle `L` to the class of its global sections. The
target is Mathlib's ring Picard group, written additively; no Noetherian, domain or
finiteness hypothesis on `R` is used. The equivalence is natural: pullback along `Spec.map φ`
corresponds to Mathlib's `CommRing.Pic.mapRingHom φ.hom`, through the actual
`Scheme.Modules.tildePullbackIso` (`picardGroupEquivCommRingPic_pullbackClass`).
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped MonoidalCategory ModuleCat.Algebra

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

section General

variable {X : Scheme.{u}}

/-- Local rank one gives finite local freeness, witnessed by the same singleton local bases. -/
theorem isFiniteLocallyFree_of_isLocallyRankOne {M : X.Modules} (h : IsLocallyRankOne X M) :
    IsFiniteLocallyFree X M := by
  obtain ⟨q, hq, hr⟩ := h
  exact ⟨⟨q, hq, ⟨fun i => ⟨Finite.of_equiv _ (hr i).some.symm⟩⟩⟩⟩

instance lineBundle_isFiniteLocallyFree (L : LineBundle X) : IsFiniteLocallyFree X L.val :=
  isFiniteLocallyFree_of_isLocallyRankOne L.property

-- The instance chain finite local freeness → finite presentation → quasicoherence runs
-- through the `X.Modules`/`SheafOfModules` abbreviations, which instance search unfolds
-- only with relaxed transparency.
set_option backward.isDefEq.respectTransparency false in
/-- Every line bundle is quasicoherent. -/
instance lineBundle_isQuasicoherent (L : LineBundle X) : L.val.IsQuasicoherent :=
  inferInstance

end General

section Affine

variable {R : CommRingCat.{u}}

/-- Global sections of the tensor of two quasicoherent sheaves on `Spec R` are the module
tensor of their global sections. -/
def globalSectionsTensorIso (M N : (Spec R).Modules) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    moduleSpecΓFunctor.obj (tensorSheaf (Spec R) M N) ≅
      moduleSpecΓFunctor.obj M ⊗ moduleSpecΓFunctor.obj N :=
  moduleSpecΓFunctor.mapIso (tensorSheafIso (Spec R) (asIso M.fromTildeΓ).symm
      (asIso N.fromTildeΓ).symm ≪≫ tildeTensorIso _ _) ≪≫
    (tilde.toTildeΓNatIso.app (moduleSpecΓFunctor.obj M ⊗ moduleSpecΓFunctor.obj N)).symm

/-- Global sections of the structure sheaf of `Spec R` are `R`. -/
def globalSectionsUnitIso :
    moduleSpecΓFunctor.obj (SheafOfModules.unit (Spec R).ringCatSheaf) ≅ ModuleCat.of R R :=
  (tilde.toTildeΓNatIso.app (ModuleCat.of R R)).symm

/-- The global sections of a line bundle on `Spec R` form an invertible `R`-module. -/
instance invertible_globalSections (L : LineBundle (Spec R)) :
    Module.Invertible R (moduleSpecΓFunctor.obj L.val) :=
  Module.Invertible.right (M := moduleSpecΓFunctor.obj (dualLineBundle (Spec R) L).val)
    ((globalSectionsTensorIso _ _).symm ≪≫
      moduleSpecΓFunctor.mapIso (dualEvaluationIso (Spec R) L) ≪≫
        globalSectionsUnitIso).toLinearEquiv

-- The principal-open restriction uses `Localization.Away` module instances that agree
-- with the restricted sections only up to instance unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- `tilde` of an invertible module is locally rank one. -/
theorem tilde_isLocallyRankOne (M : ModuleCat.{u} R) [Module.Invertible R M] :
    IsLocallyRankOne (Spec R) (tilde M) := by
  rw [isLocallyRankOne_iff_restrict_unit]
  intro x
  obtain ⟨s, hs, hfree⟩ := Module.Invertible.exists_finset_free_localization R M
  obtain ⟨r, hrs, hxr⟩ : ∃ r ∈ s, x ∈ PrimeSpectrum.basicOpen r := by
    by_contra! h
    have hle : Ideal.span (s : Set R) ≤ x.asIdeal := by
      refine Ideal.span_le.mpr fun r hr => ?_
      have hr' := h r hr
      rw [PrimeSpectrum.mem_basicOpen, not_not] at hr'
      exact hr'
    exact x.isPrime.ne_top (top_le_iff.mp (hs ▸ hle))
  refine ⟨PrimeSpectrum.basicOpen r, hxr, ⟨?_⟩⟩
  have := hfree r hrs
  let e := (Module.Invertible.free_iff_linearEquiv.mp this).some
  let F := (Scheme.Modules.restrictFunctor (QuasiCoherent.principalOpen R r)).obj (tilde M)
  let eN : LocalizedModule.Away r M ≃ₗ[Localization.Away r]
      QuasiCoherent.restrictionGlobalSections R r M :=
    (IsLocalizedModule.linearEquiv (Submonoid.powers r)
      (LocalizedModule.mkLinearMap (Submonoid.powers r) M)
      (QuasiCoherent.toRestrictionGlobalSections R r M)).extendScalarsOfIsLocalization
        (Submonoid.powers r) (Localization.Away r)
  let eΓ : moduleSpecΓFunctor.obj F ≅
      ModuleCat.of (Localization.Away r) (Localization.Away r) :=
    (eN.symm ≪≫ₗ e).toModuleIso
  let eF : F ≅ SheafOfModules.unit (Spec (CommRingCat.of (Localization.Away r))).ringCatSheaf :=
    (asIso F.fromTildeΓ).symm ≪≫ (tilde.functor _).mapIso eΓ
  let a := (basicOpenIsoSpecAway r).hom
  exact ((Scheme.Modules.restrictFunctorComp a (QuasiCoherent.principalOpen R r)).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (basicOpenIsoSpecAway_hom_SpecMap r)).symm.app
        (tilde M) ≪≫
    (Scheme.Modules.restrictFunctor a).mapIso eF ≪≫ Scheme.Modules.restrictUnitIso a

-- `isIso_fromTildeΓ_of_isQuasicoherent` is stated for `(Spec R).Modules`; matching it with the
-- quasicoherence instance of `L.val` needs relaxed instance transparency.
set_option backward.isDefEq.respectTransparency false in
/-- A line bundle on `Spec R` is `tilde` of its global sections. -/
def tildeGlobalSectionsIso (L : LineBundle (Spec R)) :
    tilde (moduleSpecΓFunctor.obj L.val) ≅ L.val :=
  asIso (Scheme.Modules.fromTildeΓ L.val)

/-- The line bundle `tilde M` of an invertible module `M`. -/
def tildeLineBundle (M : ModuleCat.{u} R) [Module.Invertible R M] : LineBundle (Spec R) :=
  ⟨tilde M, tilde_isLocallyRankOne M⟩

/-- The class in `Pic(R)` of the global sections of a line bundle on `Spec R`. -/
def globalSectionsPic (L : LineBundle (Spec R)) : CommRing.Pic R :=
  CommRing.Pic.mk R (moduleSpecΓFunctor.obj L.val)

theorem globalSectionsPic_eq_of_iso {L M : LineBundle (Spec R)} (e : L.val ≅ M.val) :
    globalSectionsPic L = globalSectionsPic M :=
  CommRing.Pic.mk_eq_mk_iff.mpr ⟨(moduleSpecΓFunctor.mapIso e).toLinearEquiv⟩

theorem globalSectionsPic_tensor (L M : LineBundle (Spec R)) :
    globalSectionsPic (tensorLineBundle (Spec R) L M) =
      globalSectionsPic L * globalSectionsPic M := by
  rw [globalSectionsPic, globalSectionsPic, globalSectionsPic, ← CommRing.Pic.mk_tensor]
  exact CommRing.Pic.mk_eq_mk_iff.mpr ⟨(globalSectionsTensorIso L.val M.val).toLinearEquiv⟩

/-- Global sections on classes, `Pic(Spec R) → Pic(R)`, written additively. -/
def toCommRingPic : PicardGroup (Spec R) →+ Additive (CommRing.Pic R) :=
  AddMonoidHom.mk' (fun a => Quotient.liftOn a (fun L => Additive.ofMul (globalSectionsPic L))
    (fun _ _ ⟨e⟩ => congrArg Additive.ofMul (globalSectionsPic_eq_of_iso e))) (by
      intro a b
      induction a using Quotient.inductionOn with | h L =>
      induction b using Quotient.inductionOn with | h M =>
      exact congrArg Additive.ofMul (globalSectionsPic_tensor L M))

@[simp]
theorem toCommRingPic_classOf (L : LineBundle (Spec R)) :
    toCommRingPic (classOf (Spec R) L) =
      Additive.ofMul (CommRing.Pic.mk R (moduleSpecΓFunctor.obj L.val)) := rfl

theorem toCommRingPic_injective : Function.Injective (toCommRingPic (R := R)) := by
  intro a b h
  induction a using Quotient.inductionOn with | h L =>
  induction b using Quotient.inductionOn with | h M =>
  obtain ⟨e⟩ := CommRing.Pic.mk_eq_mk_iff.mp (Additive.ofMul.injective h)
  exact Quotient.sound ⟨(tildeGlobalSectionsIso L).symm ≪≫
    (tilde.functor R).mapIso e.toModuleIso ≪≫ tildeGlobalSectionsIso M⟩

theorem toCommRingPic_tildeLineBundle (M : ModuleCat.{u} R) [Module.Invertible R M] :
    toCommRingPic (classOf (Spec R) (tildeLineBundle M)) =
      Additive.ofMul (CommRing.Pic.mk R M) :=
  congrArg Additive.ofMul (CommRing.Pic.mk_eq_mk_iff.mpr
    ⟨(tilde.toTildeΓNatIso.app M).symm.toLinearEquiv⟩)

theorem toCommRingPic_surjective : Function.Surjective (toCommRingPic (R := R)) := by
  intro P
  refine ⟨classOf (Spec R)
    (tildeLineBundle (ModuleCat.of R (CommRing.Pic.AsModule (Additive.toMul P)))), ?_⟩
  rw [toCommRingPic_tildeLineBundle]
  exact congrArg Additive.ofMul CommRing.Pic.mk_eq_self

/-- The Picard group of `Spec R` is the Picard group of the commutative ring `R`: a line
bundle corresponds to its invertible module of global sections. -/
def picardGroupEquivCommRingPic (R : CommRingCat.{u}) :
    PicardGroup (Spec R) ≃+ Additive (CommRing.Pic R) :=
  AddEquiv.ofBijective toCommRingPic ⟨toCommRingPic_injective, toCommRingPic_surjective⟩

@[simp]
theorem picardGroupEquivCommRingPic_classOf (L : LineBundle (Spec R)) :
    picardGroupEquivCommRingPic R (classOf (Spec R) L) =
      Additive.ofMul (CommRing.Pic.mk R (moduleSpecΓFunctor.obj L.val)) := rfl

/-- Global sections of the pullback of a line bundle along `Spec.map φ` are the base change of
its global sections. -/
def globalSectionsPullbackLinearEquiv {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (L : LineBundle (Spec R)) :
    letI := φ.hom.toAlgebra
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj L.val) ≃ₗ[S]
      TensorProduct R S (moduleSpecΓFunctor.obj L.val) :=
  letI := φ.hom.toAlgebra
  (moduleSpecΓFunctor.mapIso ((Scheme.Modules.pullback (Spec.map φ)).mapIso
      (tildeGlobalSectionsIso L).symm ≪≫
        (Scheme.Modules.tildePullbackIso φ).app (moduleSpecΓFunctor.obj L.val)) ≪≫
    (tilde.toTildeΓNatIso.app
      ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj L.val))).symm).toLinearEquiv ≪≫ₗ
    LinearEquiv.refl S (TensorProduct R S (moduleSpecΓFunctor.obj L.val))

/-- The affine comparison is natural: pullback along `Spec.map φ` is Mathlib's
`CommRing.Pic.mapRingHom φ.hom`. -/
theorem picardGroupEquivCommRingPic_pullbackClass {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (a : PicardGroup (Spec R)) :
    picardGroupEquivCommRingPic S (pullbackClass (Spec.map φ) a) =
      Additive.ofMul (CommRing.Pic.mapRingHom φ.hom
        (Additive.toMul (picardGroupEquivCommRingPic R a))) := by
  induction a using Quotient.inductionOn with | h L =>
  let := φ.hom.toAlgebra
  change Additive.ofMul (CommRing.Pic.mk S
      (moduleSpecΓFunctor.obj (pullbackLineBundle (Spec.map φ) L).val)) =
    Additive.ofMul (CommRing.Pic.mapAlgebra R S
      (CommRing.Pic.mk R (moduleSpecΓFunctor.obj L.val)))
  rw [CommRing.Pic.mapAlgebra_apply]
  exact congrArg Additive.ofMul (CommRing.Pic.mk_eq_mk_iff.mpr
    ⟨globalSectionsPullbackLinearEquiv φ L ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
        (CommRing.Pic.mk.linearEquiv R _).symm⟩)

end Affine

end AlgebraicGeometry.Scheme.Modules.Invertible
