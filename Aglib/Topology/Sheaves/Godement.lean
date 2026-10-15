/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.Topology.Sheaves.FilteredColimits
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
# Godement embeddings and flasque abelian sheaves

The product of stalk skyscrapers gives the actual functorial Godement
monomorphism and its cokernel short exact sequence, also for diagrams. Products
of flasque sheaves are flasque. Filtered-colimit flasqueness retains its
Noetherian hypothesis. No commutation of stalks with infinite products is used,
and this file does not assert positive cohomological vanishing.

Source: `R5Lab.CategoryTheory.Sheaves.NoetherianCohomology` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`. Godement, product/filtered-colimit flasqueness and
  diagram-sequence declarations only.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits TopologicalSpace Opposite TopCat
namespace TopCat.Sheaf
universe u
variable {X : TopCat.{u}}

lemma isFlasque_of_iso {P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    (e : P ≅ Q) [TopCat.Presheaf.IsFlasque (X := X) P] :
    TopCat.Presheaf.IsFlasque (X := X) Q where
  epi {U V} i := by
    have : Epi (P.map i ≫ e.hom.app V) := inferInstance
    exact epi_of_epi_fac (e.hom.naturality i).symm

lemma filtered_colimit_isFlasque [NoetherianSpace X]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [∀ i, TopCat.Presheaf.IsFlasque (X := X) (D.obj i).obj] :
    TopCat.Presheaf.IsFlasque (X := X) (colimit D).obj := by
  let P := D ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  have : TopCat.Presheaf.IsFlasque (X := X) (P.flip ⋙ colim) := {
    epi := fun {U V} i => by
      have : ∀ j, Epi ((P.flip.map i).app j) := fun j =>
        inferInstanceAs (Epi ((D.obj j).obj.map i))
      have : Epi (P.flip.map i) := NatTrans.epi_of_epi_app _
      exact Functor.map_epi colim (P.flip.map i) }
  let hc := isColimitOfPreserves
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (colimit.isColimit D)
  let e : (colimit D).obj ≅ P.flip ⋙ colim :=
    hc.coconePointUniqueUpToIso (pointwiseIsColimit P)
  exact isFlasque_of_iso e.symm

lemma product_isFlasque {ι : Type u}
    (F : ι → CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [∀ i, TopCat.Presheaf.IsFlasque (X := X) (F i).obj] :
    TopCat.Presheaf.IsFlasque (X := X) (∏ᶜ F).obj := by
  let D := Discrete.functor F ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  have : TopCat.Presheaf.IsFlasque (X := X) (D.flip ⋙ lim) := {
    epi := fun {U V} i => by
      have : ∀ j, Epi ((D.flip.map i).app j) := fun j =>
        inferInstanceAs (Epi ((F j.as).obj.map i))
      have : Epi (D.flip.map i) := NatTrans.epi_of_epi_app _
      exact Functor.map_epi lim (D.flip.map i) }
  let e : (∏ᶜ F).obj ≅ D.flip ⋙ lim :=
    preservesLimitIso (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (Discrete.functor F) ≪≫ limitIsoFlipCompLim D
  exact isFlasque_of_iso e.symm

/-- Local classical decidability of membership in an open, for stalk adjunctions. -/
local instance decidablePointMemOpen (x : X) : ∀ U : Opens X, Decidable (x ∈ U) :=
  fun _ => Classical.propDecidable _

/-- The stalk functor on additive sheaves of the topological space. -/
abbrev abelianStalk (x : X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

/-- The stalk functor followed by the skyscraper functor at the same point. -/
def godementFactor (x : X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  abelianStalk x ⋙ skyscraperSheafFunctor x

/-- The product of the skyscrapers of all stalks of an additive sheaf. -/
def godementFunctor :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} where
  obj F := ∏ᶜ (fun x : X => (godementFactor x).obj F)
  map f := Limits.Pi.map (fun x => (godementFactor x).map f)
  map_id F := by simp
  map_comp f g := by simp [Limits.Pi.map_comp_map]

/-- The map to the product of stalk skyscrapers induced by the adjunction units. -/
def godementUnit : 𝟭 _ ⟶ godementFunctor (X := X) where
  app F := Pi.lift (fun x : X => (stalkSkyscraperSheafAdjunction x).unit.app F)
  naturality {F G} f := by
    apply Pi.hom_ext
    intro x
    simp only [godementFunctor, Limits.Pi.lift_comp_π, Category.assoc, Pi.map_π,
      Limits.Pi.lift_comp_π_assoc, Functor.id_map]
    exact (stalkSkyscraperSheafAdjunction x).unit.naturality f

lemma godementUnit_mono (F : CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}) : Mono (godementUnit.app F) := by
  apply (TopCat.Presheaf.mono_iff_stalk_mono _).mpr
  intro x
  let a := stalkSkyscraperSheafAdjunction (C := AddCommGrpCat.{u}) x
  let L := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have : IsIso (a.counit.app (L.obj F)) := by
    change IsIso (skyscraperPresheafStalkOfSpecializes x _ specializes_rfl).hom
    infer_instance
  have : IsIso (L.map (a.unit.app F)) :=
    isIso_of_comp_hom_eq_id _ (a.left_triangle_components F)
  have heq : L.map (godementUnit.app F) ≫
      L.map (Pi.π (fun x : X => (godementFactor x).obj F) x) = L.map (a.unit.app F) := by
    rw [← L.map_comp]
    congr 1
    exact Limits.Pi.lift_comp_π _ x
  exact mono_of_mono_fac heq

lemma godementFunctor_isFlasque (F : CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    TopCat.Presheaf.IsFlasque (X := X) (godementFunctor.obj F).obj := by
  have : ∀ x : X, TopCat.Presheaf.IsFlasque (X := X) ((godementFactor x).obj F).obj :=
    fun x => _root_.isFlasque_skyscraperSheaf_of_hasZeroObject x _
  exact product_isFlasque _

end TopCat.Sheaf

namespace TopCat.Sheaf
universe u
variable {X : TopCat.{u}}

/-- The objectwise Godement embedding of a diagram of additive sheaves. -/
def godementDiagramUnit {I : Type u} [SmallCategory I]
    (D : I ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    D ⟶ D ⋙ godementFunctor :=
  D.rightUnitor.inv ≫ Functor.whiskerLeft D godementUnit

instance godementDiagramUnit_mono {I : Type u} [SmallCategory I]
    (D : I ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Mono (godementDiagramUnit D) := by
  have : ∀ i, Mono ((godementDiagramUnit D).app i) := fun i =>
    godementUnit_mono (D.obj i)
  exact NatTrans.mono_of_mono_app _

/-- The Godement embedding and its cokernel as a short complex of diagrams. -/
def godementDiagramSequence {I : Type u} [SmallCategory I]
    (D : I ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ShortComplex (I ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ShortComplex.mk (godementDiagramUnit D) (cokernel.π (godementDiagramUnit D))
    (cokernel.condition _)

lemma godementDiagramSequence_shortExact {I : Type u} [SmallCategory I]
    (D : I ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (godementDiagramSequence D).ShortExact := by
  dsimp only [godementDiagramSequence]
  exact { exact := ShortComplex.exact_cokernel (godementDiagramUnit D) }

end TopCat.Sheaf
