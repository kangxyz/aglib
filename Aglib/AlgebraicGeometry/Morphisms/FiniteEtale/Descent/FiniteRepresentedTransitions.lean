/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteRepresentedRestriction
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.RepresentedTorsor

/-! Actual scheme transition maps from local represented set-sheaf isomorphisms. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)

namespace AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

universe u

/-- Restriction to etale charts composes by the actual postcomposition functors. -/
def setEtaleRestrictionComp {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
    [Etale f] [Etale g] :
    Scheme.EtaleH1.setEtaleRestriction f ⋙ Scheme.EtaleH1.setEtaleRestriction g ≅
      Scheme.EtaleH1.setEtaleRestriction (g ≫ f) := by
  let e : Scheme.EtaleH1.siteEtalePostcompose g ⋙ Scheme.EtaleH1.siteEtalePostcompose f ≅
    Scheme.EtaleH1.siteEtalePostcompose (g ≫ f) :=
    (MorphismProperty.Over.mapComp (P := @Etale) (Q := ⊤)
      (inferInstance : Etale g) (inferInstance : Etale f)).symm
  exact Functor.sheafPushforwardContinuousComp' e
    (Type (u + 1)) (Scheme.smallEtaleTopology T)
      (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X)

variable {X : Scheme.{u}} {F : Scheme.EtaleH1.SetSheaf X} {Y Z W : Scheme.FiniteEtale X}

/-- A common represented sheaf produces an actual isomorphism over the base. -/
def finiteRepresentedTransition (eY : Scheme.EtaleH1.finiteRepresentedSetSheaf Y ≅ F)
    (eZ : Scheme.EtaleH1.finiteRepresentedSetSheaf Z ≅ F) : Y.obj ≅ Z.obj :=
  Scheme.EtaleH1.finiteRepresentedSetSheafIso (eY ≪≫ eZ.symm)

@[simp] lemma finiteRepresentedTransition_map
    (eY : Scheme.EtaleH1.finiteRepresentedSetSheaf Y ≅ F) (eZ :
      Scheme.EtaleH1.finiteRepresentedSetSheaf Z ≅ F) :
    Scheme.EtaleH1.finiteRepresentedSetSheafMap (finiteRepresentedTransition eY eZ).hom = eY.hom
      ≫ eZ.inv :=
  Scheme.EtaleH1.finiteRepresentedSetSheafMap_preimage _

/-- The transition scheme morphisms satisfy the actual cocycle equation. -/
lemma finiteRepresentedTransition_comp
    (eY : Scheme.EtaleH1.finiteRepresentedSetSheaf Y ≅ F) (eZ :
      Scheme.EtaleH1.finiteRepresentedSetSheaf Z ≅ F)
    (eW : Scheme.EtaleH1.finiteRepresentedSetSheaf W ≅ F) :
    (finiteRepresentedTransition eY eZ).hom ≫ (finiteRepresentedTransition eZ eW).hom =
      (finiteRepresentedTransition eY eW).hom := by
  apply (Scheme.EtaleH1.finiteRepresentedSetSheafHomEquiv Y W).injective
  change Scheme.EtaleH1.finiteRepresentedSetSheafMap _ =
    Scheme.EtaleH1.finiteRepresentedSetSheafMap _
  rw [Scheme.EtaleH1.finiteRepresentedSetSheafMap_comp]
  simp

@[simp] lemma finiteRepresentedTransition_self (eY : Scheme.EtaleH1.finiteRepresentedSetSheaf Y ≅
  F) :
    (finiteRepresentedTransition eY eY).hom = 𝟙 Y.obj := by
  apply (Scheme.EtaleH1.finiteRepresentedSetSheafHomEquiv Y Y).injective
  change Scheme.EtaleH1.finiteRepresentedSetSheafMap _ =
    Scheme.EtaleH1.finiteRepresentedSetSheafMap _
  simp [Scheme.EtaleH1.finiteRepresentedSetSheafMap_id]

/-- Pull a chart representative to a common etale test scheme and identify its
actual represented sheaf with the restriction of the original sheaf. -/
def finiteRepresentedCommonChartIso {S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (k : T ⟶ X) [Etale f] [Etale g] [Etale k]
    (h : g ≫ f = k) (Y : Scheme.FiniteEtale S)
    (eY : Scheme.EtaleH1.finiteRepresentedSetSheaf Y ≅ (Scheme.EtaleH1.setEtaleRestriction f).obj
      F) :
    Scheme.EtaleH1.finiteRepresentedSetSheaf ((baseChange g).obj Y) ≅
      (Scheme.EtaleH1.setEtaleRestriction k).obj F := by
  subst k
  exact (finiteRepresentedRestrictionIso g Y).symm ≪≫
    (Scheme.EtaleH1.setEtaleRestriction g).mapIso eY ≪≫ (setEtaleRestrictionComp f g).app F

end AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 ac4fea07b7ca958320faff2522cd4b8f4e2afe810e0462a12d3e180cf6099ba6.
Definitions, hypotheses and universes are retained modulo native names. -/
