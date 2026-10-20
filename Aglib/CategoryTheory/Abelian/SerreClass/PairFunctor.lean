/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.Abelian.SerreClass.ExactKernels
public import Aglib.CategoryTheory.Abelian.SerreClass.FiniteProducts

/-!
# Restriction and Gabriel-quotient functors induced by an actual exact functor preserving a pair
of Serre classes.

Source: `lean/R5Lab/Aglib/CategoryTheory/Abelian/SerreClass/PairFunctor.lean`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `c08d5e04292c912ef371b15273b12d0f82e33eac435d3551c93575e972484d22`.
Native objects and canonical maps are reused; provenance does not select declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ExactCategory
open _root_.CategoryTheory.ExactCategory (ExactFunctor abelianExactStructure)
namespace CategoryTheory.ObjectProperty.SerrePair
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
local instance canonicalAbelian {C : Type u} [Category.{u} C] [Abelian C]
    (P : ObjectProperty C) [P.IsSerreClass] : Abelian P.isoModSerre.Localization :=
  ObjectProperty.SerreClassLocalization.abelian P.isoModSerre.Q P
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Abelian C] [Abelian D]
  (P : ObjectProperty C) [P.IsSerreClass]
  (Q : ObjectProperty D) [Q.IsSerreClass]
  (F : CategoryTheory.ExactCategory.ExactFunctor
    (abelianExactStructure C) (abelianExactStructure D))
  (hF : ∀ X, P X → Q (F.toFunctor.obj X))

/-- Restrict the given exact functor, with no new functor or K-map input. -/
def restrictedExact : CategoryTheory.ExactCategory.ExactFunctor
    (ObjectProperty.subcategoryExactStructure P)
    (ObjectProperty.subcategoryExactStructure Q) where
  toFunctor := Q.lift (P.ι ⋙ F.toFunctor) (fun M => hF M.obj M.property)
  additive := {
    map_add := by
      intros
      apply ObjectProperty.hom_ext
      exact (P.ι ⋙ F.toFunctor).map_add }
  map_conflation S h := by
    have he := ((ObjectProperty.exactInclusion P).comp F).map_conflation S h
    exact { exact := Functor.reflects_exact_of_faithful Q.ι _ he.exact
            mono_f := Q.ι.mono_of_mono_map he.mono_f
            epi_g := Q.ι.epi_of_epi_map he.epi_g }

/-- The inclusion square commutes on the literal underlying functors. -/
theorem restrictedExact_fac :
    (restrictedExact P Q F hF).toFunctor ⋙ Q.ι = P.ι ⋙ F.toFunctor := rfl

omit [P.IsSerreClass] in
include hF in
theorem quotientComposite_kills :
    P ≤ (F.toFunctor ⋙ Q.isoModSerre.Q).kernel := by
  intro X hX
  exact (CategoryTheory.ObjectProperty.SerreClassLocalization.isZero_obj_iff
    Q.isoModSerre.Q Q _).mpr (hF X hX)

include hF in
theorem quotientComposite_inverts :
    P.isoModSerre.IsInvertedBy (F.toFunctor ⋙ Q.isoModSerre.Q) := by
  let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits Q.isoModSerre.Q Q
  let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits Q.isoModSerre.Q Q
  exact (P.isoModSerre_isInvertedBy_iff _).mpr (quotientComposite_kills P Q F hF)

/-- The actual Gabriel-quotient lift of the original exact pair functor. -/
def quotientFunctor : P.isoModSerre.Localization ⥤ Q.isoModSerre.Localization :=
  Localization.Construction.lift (F.toFunctor ⋙ Q.isoModSerre.Q)
    (quotientComposite_inverts P Q F hF)

theorem quotientFunctor_fac :
    P.isoModSerre.Q ⋙ quotientFunctor P Q F hF = F.toFunctor ⋙ Q.isoModSerre.Q :=
  Localization.Construction.fac _ _

instance quotientFunctor_additive : (quotientFunctor P Q F hF).Additive := by
  apply (Localization.functor_additive_iff P.isoModSerre.Q P.isoModSerre _).mpr
  rw [quotientFunctor_fac]
  infer_instance

instance quotientFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (quotientFunctor P Q F hF) := by
  apply (ObjectProperty.SerreClassLocalization.preservesFiniteLimits_comp_iff
    P.isoModSerre.Q P _).mp
  rw [quotientFunctor_fac]
  let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits Q.isoModSerre.Q Q
  infer_instance

instance quotientFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (quotientFunctor P Q F hF) := by
  apply (ObjectProperty.SerreClassLocalization.preservesFiniteColimits_comp_iff
    P.isoModSerre.Q P _).mp
  rw [quotientFunctor_fac]
  let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits Q.isoModSerre.Q Q
  infer_instance

/-- The induced quotient functor is exact, proved from the original exactness. -/
def quotientExact : CategoryTheory.ExactCategory.ExactFunctor
    ((abelianExactStructure
      P.isoModSerre.Localization))
    ((abelianExactStructure
      Q.isoModSerre.Localization)) where
  toFunctor := quotientFunctor P Q F hF
  map_conflation _ h := h.map_of_exact _

end CategoryTheory.ObjectProperty.SerrePair
