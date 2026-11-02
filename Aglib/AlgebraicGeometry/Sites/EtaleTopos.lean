/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Over
public import Aglib.CategoryTheory.Functor.FlatKanExtension
public import Aglib.CategoryTheory.Topos.Grothendieck
public import Aglib.CategoryTheory.Topos.SheafMorphism

/-!
# The actual small-etale topos and its geometric morphism

The category is the original sheaf category with values in Type (u + 1).
A scheme morphism uses the original site base change, continuous Set direct
image, native inverse image and their original adjunction. The source-map
primitives retain their public names for existing cohomology clients.
No coefficient-category realization or higher-topos assertion is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section OriginalEtaleSiteMap

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u v

/-- The original etale predicate with its native categorical Hom binders explicit. -/
abbrev etaleMorphismProperty : MorphismProperty AlgebraicGeometry.Scheme.{u} :=
  fun {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) => AlgebraicGeometry.Etale f

/-- The typed view has exactly the original etale predicate, without changing its values. -/
theorem etaleMorphismProperty_eq_native :
    etaleMorphismProperty.{u} =
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty AlgebraicGeometry.Scheme.{u}) := rfl

/-- Actual scheme pullback on the small étale categories. -/
abbrev siteBaseChange {X S : Scheme.{u}} (f : S ⟶ X) : X.Etale ⥤ S.Etale :=
  MorphismProperty.Over.pullback
    etaleMorphismProperty.{u} (⊤ : MorphismProperty Scheme.{u}) f

instance {X S : Scheme.{u}} (f : S ⟶ X) :
    PreservesFiniteLimits (siteBaseChange f) := by
  exact inferInstanceAs (PreservesFiniteLimits
    (MorphismProperty.Over.pullback
      etaleMorphismProperty.{u} (⊤ : MorphismProperty Scheme.{u}) f))

/-- Forgetting the site map is exactly the original native pullback of schemes over the base. -/
theorem siteBaseChange_comp_forget_eq_original {X S : Scheme.{u}} (f : S ⟶ X) :
    siteBaseChange f ⋙ Scheme.Etale.forget S =
      Scheme.Etale.forget X ⋙ CategoryTheory.Over.pullback f := rfl

/-- Base change carries small-étale covering sieves to covering sieves. -/
theorem siteBaseChange_coverPreserving {X S : Scheme.{u}} (f : S ⟶ X) :
    CoverPreserving (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
      (siteBaseChange f) where
  cover_preserve {U} {R} hR := by
    let P (H : X.Etale ⥤ CategoryTheory.Over S) : Prop :=
      R.functorPushforward H ∈ (Scheme.etaleTopology.over S) (H.obj U)
    have hnative : P (Scheme.Etale.forget X ⋙ CategoryTheory.Over.pullback f) := by
      let : (Scheme.Etale.forget X).LocallyCoverDense (Scheme.etaleTopology.over X) :=
        AlgebraicGeometry.Scheme.locallyCoverDense_of_le
          (P := etaleMorphismProperty.{u}) (Q := etaleMorphismProperty.{u}) X le_rfl
      change R.functorPushforward
        (Scheme.Etale.forget X ⋙ CategoryTheory.Over.pullback f) ∈
          (Scheme.etaleTopology.over S)
            ((Scheme.Etale.forget X ⋙ CategoryTheory.Over.pullback f).obj U)
      rw [Sieve.functorPushforward_comp]
      apply (CategoryTheory.GrothendieckTopology.coverPreserving_overPullback
        Scheme.etaleTopology f).cover_preserve
      exact (Functor.coverPreserving_restrictedTopology
        (Scheme.Etale.forget X) (Scheme.etaleTopology.over X)).cover_preserve hR
    have hsite : P (siteBaseChange f ⋙ Scheme.Etale.forget S) :=
      Eq.mpr (congrArg P (siteBaseChange_comp_forget_eq_original f)) hnative
    let Q (T : Sieve ((siteBaseChange f ⋙ Scheme.Etale.forget S).obj U)) : Prop :=
      T ∈ (Scheme.etaleTopology.over S)
        ((siteBaseChange f ⋙ Scheme.Etale.forget S).obj U)
    have he :
        R.functorPushforward (siteBaseChange f ⋙ Scheme.Etale.forget S) =
          (R.functorPushforward (siteBaseChange f)).functorPushforward
            (Scheme.Etale.forget S) :=
      Sieve.functorPushforward_comp (siteBaseChange f) (Scheme.Etale.forget S) R
    have hfixed : Q ((R.functorPushforward (siteBaseChange f)).functorPushforward
        (Scheme.Etale.forget S)) := Eq.mp (congrArg Q he) hsite
    have hpush :
        (R.functorPushforward (siteBaseChange f)).functorPushforward
            (Scheme.Etale.forget S) ∈
          (Scheme.etaleTopology.over S)
            ((Scheme.Etale.forget S).obj ((siteBaseChange f).obj U)) := by
      exact hfixed
    exact (Scheme.Etale.forget S).mem_restrictedTopology_of_functorPushforward_mem hpush

/-- Actual base change is a continuous morphism of small étale sites. -/
instance {X S : Scheme.{u}} (f : S ⟶ X) :
    (siteBaseChange f).IsContinuous (Scheme.smallEtaleTopology X)
      (Scheme.smallEtaleTopology S) := by
  let := flat_of_preservesFiniteLimits (siteBaseChange f)
  exact Functor.isContinuous_iff_coverPreserving.mpr
    (siteBaseChange_coverPreserving f)


end AlgebraicGeometry.Scheme.EtaleCohomology

end OriginalEtaleSiteMap

namespace AlgebraicGeometry.Scheme

universe u

/-- The actual small-etale topos, in the native value world above schemes. -/
abbrev EtaleTopos (X : Scheme.{u}) :=
  Sheaf X.smallEtaleTopology (Type (u + 1))

/-- The same actual category admits the native bounded small-site presentation.
Only existence is retained; no operational small model replaces its sheaves. -/
instance etaleToposIsGrothendieckTopos (X : Scheme.{u}) :
    Topos.IsGrothendieckTopos.{u + 1} (EtaleTopos X) := by
  let : EssentiallySmall.{u + 1} X.Etale :=
    essentiallySmallSelf.{u + 1} X.Etale
  exact Topos.sheaf_isGrothendieckTopos X.smallEtaleTopology

/-- The original Set inverse image is left exact, by the native flat Kan proof. -/
instance etaleSetPullback_preservesFiniteLimits {X S : Scheme.{u}} (f : S ⟶ X) :
    PreservesFiniteLimits
      ((EtaleCohomology.siteBaseChange f).sheafPullback (Type (u + 1))
        X.smallEtaleTopology S.smallEtaleTopology) := by
  let F := EtaleCohomology.siteBaseChange f
  let : RepresentablyFlat F := flat_of_preservesFiniteLimits F
  let : PreservesFiniteLimits
      (F.op.lan : (X.Etaleᵒᵖ ⥤ Type (u + 1)) ⥤ S.Etaleᵒᵖ ⥤ Type (u + 1)) :=
    Functor.lan_preservesFiniteLimits_of_flat_of_shapes (E := Type (u + 1)) (F := F)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits F (Type (u + 1))
    X.smallEtaleTopology S.smallEtaleTopology

/-- The actual geometric morphism of small-etale topoi induced by the scheme map. -/
def etaleToposMorphism {X S : Scheme.{u}} (f : S ⟶ X) :
    Topos.GeometricMorphism (EtaleTopos S) (EtaleTopos X) := by
  let L : EtaleTopos X ⥤ EtaleTopos S :=
    (EtaleCohomology.siteBaseChange f).sheafPullback (Type (u + 1))
      X.smallEtaleTopology S.smallEtaleTopology
  let R : EtaleTopos S ⥤ EtaleTopos X :=
    (EtaleCohomology.siteBaseChange f).sheafPushforwardContinuous (Type (u + 1))
      X.smallEtaleTopology S.smallEtaleTopology
  let adj : L ⊣ R :=
    (EtaleCohomology.siteBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
      X.smallEtaleTopology S.smallEtaleTopology
  let : PreservesFiniteLimits L := etaleSetPullback_preservesFiniteLimits f
  exact LeftExactAdjunction.ofAdjunction adj

/-- The site-functor factory uses exactly this original native adjunction. -/
theorem etaleToposMorphism_eq_native {X S : Scheme.{u}} (f : S ⟶ X) :
    etaleToposMorphism f =
      LeftExactAdjunction.ofAdjunction
        ((EtaleCohomology.siteBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
          X.smallEtaleTopology S.smallEtaleTopology) := rfl

/-- Inverse image is the original native chosen Set-sheaf pullback. -/
theorem etaleToposMorphism_inverseImage {X S : Scheme.{u}} (f : S ⟶ X) :
    Topos.GeometricMorphism.inverseImage (etaleToposMorphism f) =
      (EtaleCohomology.siteBaseChange f).sheafPullback (Type (u + 1))
        X.smallEtaleTopology S.smallEtaleTopology := rfl

/-- Direct image is the original continuous Set-sheaf pushforward. -/
theorem etaleToposMorphism_directImage {X S : Scheme.{u}} (f : S ⟶ X) :
    Topos.GeometricMorphism.directImage (etaleToposMorphism f) =
      (EtaleCohomology.siteBaseChange f).sheafPushforwardContinuous (Type (u + 1))
        X.smallEtaleTopology S.smallEtaleTopology := rfl

/-- The adjunction is the original native adjunction, without a new choice. -/
theorem etaleToposMorphism_adjunction {X S : Scheme.{u}} (f : S ⟶ X) :
    Topos.GeometricMorphism.adjunction (etaleToposMorphism f) =
      (EtaleCohomology.siteBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
        X.smallEtaleTopology S.smallEtaleTopology := rfl

/-- The whole Set unit is the original native unit. -/
theorem etaleToposMorphism_unit {X S : Scheme.{u}} (f : S ⟶ X) :
    (Topos.GeometricMorphism.adjunction (etaleToposMorphism f)).unit =
      ((EtaleCohomology.siteBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
        X.smallEtaleTopology S.smallEtaleTopology).unit := rfl

/-- The whole Set counit is the original native counit. -/
theorem etaleToposMorphism_counit {X S : Scheme.{u}} (f : S ⟶ X) :
    (Topos.GeometricMorphism.adjunction (etaleToposMorphism f)).counit =
      ((EtaleCohomology.siteBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
        X.smallEtaleTopology S.smallEtaleTopology).counit := rfl

/-- A direct-image section is evaluated at the original base-changed test object. -/
theorem etaleToposMorphism_directImage_obj_obj {X S : Scheme.{u}} (f : S ⟶ X)
    (P : EtaleTopos S) (U : X.Etaleᵒᵖ) :
    ((Topos.GeometricMorphism.directImage (etaleToposMorphism f)).obj P).obj.obj U =
      P.obj.obj ((EtaleCohomology.siteBaseChange f).op.obj U) := rfl

/-- Direct image retains the original coefficient morphism on every test object. -/
theorem etaleToposMorphism_directImage_map_app {X S : Scheme.{u}} (f : S ⟶ X)
    {P Q : EtaleTopos S} (a : P ⟶ Q) (U : X.Etaleᵒᵖ) :
    ((Topos.GeometricMorphism.directImage (etaleToposMorphism f)).map a).hom.app U =
      a.hom.app ((EtaleCohomology.siteBaseChange f).op.obj U) := rfl

end AlgebraicGeometry.Scheme
