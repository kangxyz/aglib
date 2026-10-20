/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.StalkFiltration
public import Aglib.AlgebraicGeometry.Stalk.CodimensionOneTriangle
public import Aglib.AlgebraicGeometry.Modules.Coherent.Localization.Stalk
public import Aglib.CategoryTheory.Abelian.SerreClass.Exact
public import Aglib.CategoryTheory.SmallModel.Functoriality

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Support.CodimensionOneStalk` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`1838079b38f98de03e7b8cc2c5600581dc6cabb490db7c5411a6f8085eec6edf`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules.Coherent (coherentExactPullback coherentPullback
    coherentPullbackCompIso)
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] Scheme.fromSpecStalk_flat
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Support
universe u
local instance canonicalQuotientAbelian {C : Type u} [Category.{u} C] [Abelian C]
    (P : ObjectProperty C) [P.IsSerreClass] : Abelian P.isoModSerre.Localization :=
  ObjectProperty.SerreClassLocalization.abelian P.isoModSerre.Q P
open AlgebraicGeometry.Scheme.Modules.Coherent.Support
variable (X : Scheme.{u}) [IsNoetherian X] [IsIntegral X]

local instance (x : CodimensionOnePoint X) :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap x.localRing X.functionField))) := by
  apply Flat.SpecMap_iff.mpr
  exact RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat X.functionField (nonZeroDivisors x.localRing))

abbrev localFraction (x : CodimensionOnePoint X) :=
  coherentExactPullback
    (Spec.map (CommRingCat.ofHom (algebraMap x.localRing X.functionField)))

abbrev smallLocalFraction (x : CodimensionOnePoint X) :=
  _root_.CategoryTheory.SmallModel.mapAbelianExactFunctor.{u + 1} (localFraction X x)

def localSupport (x : CodimensionOnePoint X) : ObjectProperty (Coh (Spec x.localRing)) :=
  (smallLocalFraction X x).toFunctor.kernel

instance localSupport_serre (x : CodimensionOnePoint X) : (localSupport X x).IsSerreClass :=
  CategoryTheory.ObjectProperty.exactKernelSerre (smallLocalFraction X x)

/-- The canonical SmallModel composition comparison and the actual scheme
generic triangle identify the two exact pullback composites. -/
def smallLocalTriangle (x : CodimensionOnePoint X) :
    (stalkPullback X x.1).toFunctor ⋙ (smallLocalFraction X x).toFunctor ≅
      (stalkPullback X (genericPoint X)).toFunctor :=
  (_root_.CategoryTheory.ExactCategory.ExactFunctor.smallModelCompIso.{u + 1}
    (coherentExactPullback (X.fromSpecStalk x.1)) (localFraction X x)).symm ≪≫
  _root_.CategoryTheory.ExactCategory.ExactFunctor.smallModelNatIso.{u + 1}
    ((coherentPullbackCompIso
      (Spec.map (CommRingCat.ofHom (algebraMap x.localRing X.functionField)))
      (X.fromSpecStalk x.1)).symm ≪≫
      eqToIso (by rw [Scheme.CodimensionOnePoint.generic_triangle x]; rfl))

theorem positiveStalk_lands (x : CodimensionOnePoint X) (M : CohOne X) :
    localSupport X x ((positiveStalkPullback X x.1).toFunctor.obj M) :=
  M.property.of_iso ((smallLocalTriangle X x).app M.obj)

/-- Literal supported local pullback, with its support landing proved from
the same generic-stalk triangle. -/
def supportedStalk (x : CodimensionOnePoint X) : _root_.CategoryTheory.ExactCategory.ExactFunctor
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (CohOne X))
    (_root_.CategoryTheory.ObjectProperty.subcategoryExactStructure (localSupport X x)) where
  toFunctor := (localSupport X x).lift (positiveStalkPullback X x.1).toFunctor
    (positiveStalk_lands X x)
  additive := {
    map_add := by
      intros
      apply ObjectProperty.hom_ext
      exact (positiveStalkPullback X x.1).toFunctor.map_add }
  map_conflation S h := by
    have he := (positiveStalkPullback X x.1).map_conflation S h
    exact { exact := Functor.reflects_exact_of_faithful (localSupport X x).ι _ he.exact
            mono_f := (localSupport X x).ι.mono_of_mono_map he.mono_f
            epi_g := (localSupport X x).ι.epi_of_epi_map he.epi_g }

instance supportedStalk_preservesFiniteLimits (x : CodimensionOnePoint X) :
    PreservesFiniteLimits (supportedStalk X x).toFunctor := by
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).mpr
  intro S h
  exact ⟨((supportedStalk X x).map_conflation S h).exact,
    ((supportedStalk X x).map_conflation S h).mono_f⟩

instance supportedStalk_preservesFiniteColimits (x : CodimensionOnePoint X) :
    PreservesFiniteColimits (supportedStalk X x).toFunctor := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).mpr
  intro S h
  exact ⟨((supportedStalk X x).map_conflation S h).exact,
    ((supportedStalk X x).map_conflation S h).epi_g⟩

theorem secondSupport_le_localKernel (x : CodimensionOnePoint X) :
    secondSupport X ≤ (supportedStalk X x).toFunctor.kernel := by
  intro M hM
  exact IsZero.of_full_of_faithful_of_isZero (localSupport X x).ι _ (hM x)

theorem supportedStalk_inverts (x : CodimensionOnePoint X) :
    (secondSupport X).isoModSerre.IsInvertedBy (supportedStalk X x).toFunctor := by
  intro M N f hf
  have hk : ((supportedStalk X x).toFunctor.kernel).isoModSerre f :=
    ⟨secondSupport_le_localKernel X x _ hf.1,
      secondSupport_le_localKernel X x _ hf.2⟩
  rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms] at hk
  exact hk

/-- The actual supported local stalk on the SAME quotient used by SupportLift. -/
def quotientSupportedStalk (x : CodimensionOnePoint X) :
    (secondSupport X).isoModSerre.Localization ⥤
      (localSupport X x).FullSubcategory :=
  Localization.Construction.lift (supportedStalk X x).toFunctor
    (supportedStalk_inverts X x)

theorem quotientSupportedStalk_fac (x : CodimensionOnePoint X) :
    (secondSupport X).isoModSerre.Q ⋙ quotientSupportedStalk X x =
      (supportedStalk X x).toFunctor := Localization.Construction.fac _ _

instance quotientSupportedStalk_additive (x : CodimensionOnePoint X) :
    (quotientSupportedStalk X x).Additive := by
  apply (Localization.functor_additive_iff (secondSupport X).isoModSerre.Q
    (secondSupport X).isoModSerre _).mpr
  rw [quotientSupportedStalk_fac]
  infer_instance

instance quotientSupportedStalk_preservesFiniteLimits (x : CodimensionOnePoint X) :
    PreservesFiniteLimits (quotientSupportedStalk X x) := by
  apply (ObjectProperty.SerreClassLocalization.preservesFiniteLimits_comp_iff
    (secondSupport X).isoModSerre.Q (secondSupport X) _).mp
  rw [quotientSupportedStalk_fac]
  infer_instance

instance quotientSupportedStalk_preservesFiniteColimits (x : CodimensionOnePoint X) :
    PreservesFiniteColimits (quotientSupportedStalk X x) := by
  apply (ObjectProperty.SerreClassLocalization.preservesFiniteColimits_comp_iff
    (secondSupport X).isoModSerre.Q (secondSupport X) _).mp
  rw [quotientSupportedStalk_fac]
  infer_instance

def quotientSupportedStalkExact (x : CodimensionOnePoint X) :
    _root_.CategoryTheory.ExactCategory.ExactFunctor
    ((_root_.CategoryTheory.ExactCategory.abelianExactStructure
      (secondSupport X).isoModSerre.Localization))
    (_root_.CategoryTheory.ObjectProperty.subcategoryExactStructure (localSupport X x)) where
  toFunctor := quotientSupportedStalk X x
  map_conflation _ h := h.map_of_exact _

end AlgebraicGeometry.Scheme.Modules.Coherent.Support
