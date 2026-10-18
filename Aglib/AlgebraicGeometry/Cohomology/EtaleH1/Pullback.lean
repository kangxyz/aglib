/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.AlgebraicGeometry.Limits
public import Aglib.CategoryTheory.Functor.Flat
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Base change of the actual small étale site

Construction prerequisite for `K2-018#eq:k2018-pointed-character`, frozen
interface basis `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleH1
universe u v

/-- Actual scheme pullback on the small étale categories. -/
abbrev siteBaseChange {X S : Scheme.{u}} (f : S ⟶ X) : X.Etale ⥤ S.Etale :=
  MorphismProperty.Over.pullback @Etale ⊤ f

instance {X S : Scheme.{u}} (f : S ⟶ X) :
    PreservesFiniteLimits (siteBaseChange f) := by
  exact inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback (@Etale :
    MorphismProperty Scheme.{u}) ⊤ f))

/-- Base change carries small-étale covering sieves to covering sieves. -/
theorem siteBaseChange_coverPreserving {X S : Scheme.{u}} (f : S ⟶ X) :
    CoverPreserving (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
      (siteBaseChange f) where
  cover_preserve {U} {R} hR := by
    apply Functor.mem_restrictedTopology_of_functorPushforward_mem
    rw [← Sieve.functorPushforward_comp]
    change R.functorPushforward
      (MorphismProperty.Over.forget @Etale ⊤ X ⋙ CategoryTheory.Over.pullback f)
        ∈ (Scheme.etaleTopology.over S) _
    rw [Sieve.functorPushforward_comp]
    apply (CategoryTheory.GrothendieckTopology.coverPreserving_overPullback Scheme.etaleTopology
      f).cover_preserve
    exact (Functor.coverPreserving_restrictedTopology
      (MorphismProperty.Over.forget @Etale ⊤ X) (Scheme.etaleTopology.over X)).cover_preserve hR

/-- Actual base change is a continuous morphism of small étale sites. -/
instance {X S : Scheme.{u}} (f : S ⟶ X) :
    (siteBaseChange f).IsContinuous (Scheme.smallEtaleTopology X)
      (Scheme.smallEtaleTopology S) := by
  let := flat_of_preservesFiniteLimits (siteBaseChange f)
  exact Functor.isContinuous_iff_coverPreserving.mpr
    (siteBaseChange_coverPreserving f)

/-- Actual inverse image on abelian sheaves, constructed as sheafification of
left Kan extension, in a value universe large enough for this site. -/
def inverseImage {X S : Scheme.{u}} (f : S ⟶ X) :
    AbelianSheaf.{u, u + 1} X ⥤ AbelianSheaf.{u, u + 1} S := by
  let := hasSheafifyLarge X
  let := hasSheafifyLarge S
  exact (siteBaseChange f).sheafPullback AddCommGrpCat.{u + 1}
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)

instance inverseImage_preservesFiniteLimits {X S : Scheme.{u}} (f : S ⟶ X) :
    PreservesFiniteLimits (inverseImage f) := by
  let := hasSheafifyLarge X
  let := hasSheafifyLarge S
  let := flat_of_preservesFiniteLimits (siteBaseChange f)
  let := CategoryTheory.Functor.LargePresheaf.lan_preservesFiniteLimits (siteBaseChange f)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits
    (siteBaseChange f) AddCommGrpCat.{u + 1}
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)

instance inverseImage_isLeftAdjoint {X S : Scheme.{u}} (f : S ⟶ X) :
    (inverseImage f).IsLeftAdjoint := by
  let := hasSheafifyLarge X
  let := hasSheafifyLarge S
  exact ((siteBaseChange f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)).isLeftAdjoint

instance inverseImage_preservesColimits {X S : Scheme.{u}} (f : S ⟶ X) :
    PreservesColimits (inverseImage f) := by infer_instance

instance inverseImage_additive {X S : Scheme.{u}} (f : S ⟶ X) :
    (inverseImage f).Additive := by
  let := hasSheafifyLarge X
  let := hasSheafifyLarge S
  exact Functor.additive_of_preserves_binary_products _

/-- Inverse image preserves constant sheaves, by the two actual adjunctions
and preservation of the terminal étale object. -/
def inverseImageConstantIso {X S : Scheme.{u}} (f : S ⟶ X) :
    let := hasSheafifyLarge X
    let := hasSheafifyLarge S
    constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1} ⋙
      inverseImage f ≅
    constantSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1} := by
  let := hasSheafifyLarge X
  let := hasSheafifyLarge S
  let hT := MorphismProperty.Over.mkIdTerminal (@Etale : MorphismProperty Scheme.{u}) X
  exact ((constantSheafAdj (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1} hT).comp
    ((siteBaseChange f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S))).leftAdjointUniq
    (constantSheafAdj (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}
      (hT.isTerminalObj (siteBaseChange f)))

section Cohomology
universe w w'
variable {X S : Scheme.{u}}
variable [HasSheafify (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}]
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
variable [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- Contravariant scheme pullback on actual Ext-based H¹. It is induced by
the exact inverse-image functor and the canonical constant-ℤ transport. -/
def h1Pullback (f : S ⟶ X) (L : AbelianSheaf.{u, u + 1} X) :
    H1Etale X L →+ H1Etale S ((inverseImage f).obj L) :=
  ((Abelian.Ext.mk₀ (((inverseImageConstantIso f).app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)).precomp _ (zero_add 1)).comp
      ((inverseImage f).mapExtAddHom _ L 1)

/-- Scheme pullback commutes with every additive coefficient morphism. -/
theorem h1Pullback_coefficientMap (f : S ⟶ X)
    {L M : AbelianSheaf.{u, u + 1} X} (q : L ⟶ M) (a : H1Etale X L) :
    h1Pullback f M (coefficientMap q a) =
      coefficientMap ((inverseImage f).map q) (h1Pullback f L a) := by
  change (Abelian.Ext.mk₀ _).comp
      ((a.comp (Abelian.Ext.mk₀ q) (add_zero 1)).mapExactFunctor (inverseImage f))
        (zero_add 1) =
    ((Abelian.Ext.mk₀ _).comp (a.mapExactFunctor (inverseImage f))
      (zero_add 1)).comp (Abelian.Ext.mk₀ ((inverseImage f).map q)) (add_zero 1)
  rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
  exact (Abelian.Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) rfl).symm

end Cohomology

end AlgebraicGeometry.Scheme.EtaleH1

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 32f591c1eb828bfffc154fac1a803e951a05f2c96561e96b78857954bd8660aa.
Definitions, hypotheses and universes are retained modulo native names. -/
