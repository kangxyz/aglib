/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Topology.Sober
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# Closed support and actual sheaf cohomology

Closed topological direct image is exact, and a sheaf supported on the image
is identified through the actual inverse-image adjunction unit. The resulting
comparison uses the original constant-integer Ext definition of Sheaf.H in
universe u + 1. No Noetherian assumption is required.

Source: `R5Lab.CategoryTheory.Sheaves.NoetherianCohomology` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`. Closed-embedding, inverse-image-unit and
  closed-support comparison declarations only.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits TopologicalSpace Opposite TopCat.Presheaf
namespace TopCat.Sheaf
universe u
variable {X Z : TopCat.{u}} (i : Z ⟶ X)

instance additivePullback_preservesFiniteLimits :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} i) := by
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits
    (Opens.map i) AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)

instance additivePullback_additive : (TopCat.Sheaf.pullback AddCommGrpCat.{u} i).Additive :=
  Functor.additive_of_preserves_binary_products _

instance additivePushforward_additive : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).Additive :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).right_adjoint_additive

/-- Constant abelian sheaves commute with inverse image. -/
def constantSheafPullbackIso :
    constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      TopCat.Sheaf.pullback AddCommGrpCat.{u} i ≅
    constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} := by
  let adj := (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    isTerminalTop).comp (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i)
  exact (adj.ofNatIsoRight (Iso.refl _)).leftAdjointUniq
    (constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{u} isTerminalTop)

/-- A closed embedding has zero pushforward stalks off its image. -/
theorem pushforward_stalk_isZero (hi : Topology.IsClosedEmbedding i)
    (F : TopCat.Sheaf AddCommGrpCat.{u} Z) (x : X) (hx : x ∉ Set.range i) :
    IsZero (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj F).presheaf.stalk x) := by
  let V : Opens X := ⟨(Set.range i)ᶜ, hi.isClosed_range.isOpen_compl⟩
  have hV : (Opens.map i).obj V = ⊥ := by
    ext z
    simp [V]
  let G := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj F
  refine @AddCommGrpCat.isZero_of_subsingleton _ ?_
  apply subsingleton_of_forall_eq (0 : G.presheaf.stalk x)
  intro t
  obtain ⟨U, hUV, hxU, s, rfl⟩ := G.presheaf.exists_le_germ_eq t (V := V) hx
  have hU : (Opens.map i).obj U = ⊥ := le_antisymm
    (hV ▸ (Opens.map i).monotone hUV) bot_le
  have hz : IsZero (G.obj.obj (op U)) :=
    (isZero_zero AddCommGrpCat.{u}).of_iso
      ((TopCat.Sheaf.isTerminalOfEqEmpty F hU).uniqueUpToIso
        (isZero_zero AddCommGrpCat.{u}).isTerminal)
  have := AddCommGrpCat.subsingleton_of_isZero hz
  rw [Subsingleton.elim s 0, map_zero]

/-- Naturality of the stalk comparison for direct image. -/
theorem stalkPushforward_naturality {F G : TopCat.Presheaf AddCommGrpCat.{u} Z}
    (φ : F ⟶ G) (z : Z) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (i z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map φ) ≫
      G.stalkPushforward AddCommGrpCat.{u} i z =
    F.stalkPushforward AddCommGrpCat.{u} i z ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map φ := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hz
  simp only [TopCat.Presheaf.stalkFunctor_map_germ_assoc,
    TopCat.Presheaf.stalkPushforward_germ,
    TopCat.Presheaf.stalkPushforward_germ_assoc,
    TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

/-- Direct image under a closed embedding preserves epimorphisms of abelian sheaves. -/
theorem closedEmbedding_pushforward_preservesEpimorphisms
    (hi : Topology.IsClosedEmbedding i) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).PreservesEpimorphisms where
  preserves {F G} φ hφ := by
    apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
    apply (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mpr
    intro x
    apply (AddCommGrpCat.epi_iff_surjective _).mp
    by_cases hx : x ∈ Set.range i
    · obtain ⟨z, rfl⟩ := hx
      have : IsIso (F.presheaf.stalkPushforward AddCommGrpCat.{u} i z) :=
        TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
          AddCommGrpCat.{u} hi.isEmbedding.isInducing F.obj z
      have : IsIso (G.presheaf.stalkPushforward AddCommGrpCat.{u} i z) :=
        TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
          AddCommGrpCat.{u} hi.isEmbedding.isInducing G.obj z
      have : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map φ.hom) :=
        (TopCat.Sheaf.forget AddCommGrpCat.{u} Z ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map_epi φ
      have hnat := stalkPushforward_naturality i φ.hom z
      have : Epi (F.presheaf.stalkPushforward AddCommGrpCat.{u} i z ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map φ.hom) := inferInstance
      rw [← hnat] at this
      exact (epi_comp_iff_of_isIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (i z)).map
          ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map φ.hom))
        (G.presheaf.stalkPushforward AddCommGrpCat.{u} i z)).mp this
    · exact (pushforward_stalk_isZero i hi G x hx).epi _

/-- Direct image under a closed embedding is exact. -/
theorem closedEmbedding_pushforward_preservesFiniteColimits
    (hi : Topology.IsClosedEmbedding i) :
    PreservesFiniteColimits (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i) := by
  let := closedEmbedding_pushforward_preservesEpimorphisms i hi
  let := Functor.preservesHomology_of_preservesEpis_and_kernels
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- The unit of inverse image, expressed through the explicit sheafification construction. -/
theorem pullback_unit_construction (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app F) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).map
        ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} i).hom.app F)).hom =
    (TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app F.obj ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map
        (toSheafify (Opens.grothendieckTopology Z)
          ((TopCat.Presheaf.pullback AddCommGrpCat.{u} i).obj F.obj)) := by
  change (TopCat.Sheaf.forget AddCommGrpCat.{u} X).map
    (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app F) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).map
        ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} i).hom.app F)) = _
  rw [show (TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} i) =
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).leftAdjointUniq
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map i)
        AddCommGrpCat.{u} (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)) from rfl,
    Adjunction.unit_leftAdjointUniq_hom_app]
  change (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map i)
      AddCommGrpCat.{u} (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Z)).unit.app F) = _
  unfold Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  simp [Adjunction.comp_unit_app, TopCat.Presheaf.pullbackPushforwardAdjunction]
  rfl

/-- On an inducing map, inverse image's unit is an isomorphism on stalks in the image. -/
theorem pullback_unit_stalk_isIso (hi : Topology.IsInducing i)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (z : Z) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (i z)).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app F).hom) := by
  classical
  let P := (TopCat.Presheaf.pullback AddCommGrpCat.{u} i).obj F.obj
  let S : TopCat.Sheaf AddCommGrpCat.{u} Z := (presheafToSheaf (Opens.grothendieckTopology Z)
    AddCommGrpCat.{u}).obj P
  let γ := toSheafify (Opens.grothendieckTopology Z) P
  let e := (TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} i).app F
  let η := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app F
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (i z)
  have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map γ) :=
    Adjunction.isIso_map_unit_of_isLeftAdjoint_comp (sheafificationAdjunction _ AddCommGrpCat.{u})
      (skyscraperSheafForgetAdjunction z)
  have : IsIso (S.presheaf.stalkPushforward AddCommGrpCat.{u} i z) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat.{u} hi S.obj z
  have hc : T.map η.hom ≫
      (T.map ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).map e.hom).hom ≫
        S.presheaf.stalkPushforward AddCommGrpCat.{u} i z) =
      (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} i F.obj z).hom ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map γ := by
    rw [← Category.assoc, ← T.map_comp]
    change T.map (η ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).map e.hom).hom ≫ _ = _
    have hu : (η ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).map e.hom).hom =
        (TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app F.obj ≫
          (TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map γ :=
      pullback_unit_construction i F
    rw [hu, T.map_comp, Category.assoc]
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (i z)).map
        ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app F.obj) ≫
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (i z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map γ) ≫
          S.presheaf.stalkPushforward AddCommGrpCat.{u} i z) = _
    rw [stalkPushforward_naturality i γ z, ← Category.assoc]
    rfl
  apply (isIso_comp_right_iff (T.map η.hom)
    (T.map ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).map e.hom).hom ≫
      S.presheaf.stalkPushforward AddCommGrpCat.{u} i z)).mp
  rw [hc]
  infer_instance

/-- A sheaf whose stalks vanish off a closed subspace is the direct image of its inverse image. -/
theorem closedSupport_unit_isIso (hi : Topology.IsClosedEmbedding i)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : ∀ x : X, x ∉ Set.range i → IsZero (F.presheaf.stalk x)) :
    IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app F) := by
  have : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app F).hom) := by
    intro x
    by_cases hx : x ∈ Set.range i
    · obtain ⟨z, rfl⟩ := hx
      exact pullback_unit_stalk_isIso i hi.isEmbedding.isInducing F z
    · exact isIso_of_source_target_iso_zero _ (hF x hx).isoZero
        (pushforward_stalk_isZero i hi
          ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj F) x hx).isoZero
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso _

/-- The closed-support identification uses the actual adjunction unit. -/
def closedSupportIso (hi : Topology.IsClosedEmbedding i)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : ∀ x : X, x ∉ Set.range i → IsZero (F.presheaf.stalk x)) :
    F ≅ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj F) := by
  haveI := closedSupport_unit_isIso i hi F hF
  exact asIso ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app F)

section Cohomology
local instance (Y : TopCat.{u}) : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} Y) :=
  HasExt.standard _
local instance (Y : TopCat.{u}) :
    HasExt.{u + 1} (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) :=
  HasExt.standard _

/-- Actual Ext-defined sheaf cohomology commutes with direct image by a closed embedding. -/
def closedEmbeddingCohomologyEquiv (hi : Topology.IsClosedEmbedding i)
    (F : TopCat.Sheaf AddCommGrpCat.{u} Z) (n : ℕ) :
    Sheaf.H.{u + 1} F n ≃+
      Sheaf.H.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj F) n := by
  letI := closedEmbedding_pushforward_preservesFiniteColimits i hi
  exact (((Abelian.extFunctor.{u + 1} n).mapIso
    ((constantSheafPullbackIso i).app (AddCommGrpCat.of (ULift.{u} ℤ))).op).app
      F).addCommGroupIsoToAddEquiv |>.trans
        (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).extEquiv

/-- Cohomology on a closed support, using the original constant-integer Ext definition. -/
def closedSupportCohomologyEquiv (hi : Topology.IsClosedEmbedding i)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : ∀ x : X, x ∉ Set.range i → IsZero (F.presheaf.stalk x)) (n : ℕ) :
    Sheaf.H.{u + 1} F n ≃+
      Sheaf.H.{u + 1} ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj F) n :=
  (((Abelian.extFunctorObj.{u + 1}
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) n).mapIso (closedSupportIso i hi F
        hF)).addCommGroupIsoToAddEquiv).trans
    (closedEmbeddingCohomologyEquiv i hi
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj F) n).symm

end Cohomology
end TopCat.Sheaf
