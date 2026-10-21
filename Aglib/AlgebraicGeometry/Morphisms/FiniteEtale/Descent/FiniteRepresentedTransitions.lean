/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteRepresentedRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedTorsor

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
    Scheme.EtaleCohomology.setEtaleRestriction f ⋙ Scheme.EtaleCohomology.setEtaleRestriction g ≅
      Scheme.EtaleCohomology.setEtaleRestriction (g ≫ f) := by
  let e : Scheme.EtaleCohomology.siteEtalePostcompose g ⋙
    Scheme.EtaleCohomology.siteEtalePostcompose f ≅
    Scheme.EtaleCohomology.siteEtalePostcompose (g ≫ f) :=
    (MorphismProperty.Over.mapComp (P := @Etale) (Q := ⊤)
      (inferInstance : Etale g) (inferInstance : Etale f)).symm
  exact Functor.sheafPushforwardContinuousComp' e
    (Type (u + 1)) (Scheme.smallEtaleTopology T)
      (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X)

variable {X : Scheme.{u}} {F : Scheme.EtaleCohomology.SetSheaf X} {Y Z W : Scheme.FiniteEtale X}

/-- A common represented sheaf produces an actual isomorphism over the base. -/
def finiteRepresentedTransition (eY : Scheme.EtaleCohomology.finiteRepresentedSetSheaf Y ≅ F)
    (eZ : Scheme.EtaleCohomology.finiteRepresentedSetSheaf Z ≅ F) : Y.obj ≅ Z.obj :=
  Scheme.EtaleCohomology.finiteRepresentedSetSheafIso (eY ≪≫ eZ.symm)

@[simp] lemma finiteRepresentedTransition_map
    (eY : Scheme.EtaleCohomology.finiteRepresentedSetSheaf Y ≅ F) (eZ :
      Scheme.EtaleCohomology.finiteRepresentedSetSheaf Z ≅ F) :
    Scheme.EtaleCohomology.finiteRepresentedSetSheafMap (finiteRepresentedTransition eY eZ).hom =
      eY.hom
      ≫ eZ.inv :=
  Scheme.EtaleCohomology.finiteRepresentedSetSheafMap_preimage _

/-- The transition scheme morphisms satisfy the actual cocycle equation. -/
lemma finiteRepresentedTransition_comp
    (eY : Scheme.EtaleCohomology.finiteRepresentedSetSheaf Y ≅ F) (eZ :
      Scheme.EtaleCohomology.finiteRepresentedSetSheaf Z ≅ F)
    (eW : Scheme.EtaleCohomology.finiteRepresentedSetSheaf W ≅ F) :
    (finiteRepresentedTransition eY eZ).hom ≫ (finiteRepresentedTransition eZ eW).hom =
      (finiteRepresentedTransition eY eW).hom := by
  apply (Scheme.EtaleCohomology.finiteRepresentedSetSheafHomEquiv Y W).injective
  change Scheme.EtaleCohomology.finiteRepresentedSetSheafMap _ =
    Scheme.EtaleCohomology.finiteRepresentedSetSheafMap _
  rw [Scheme.EtaleCohomology.finiteRepresentedSetSheafMap_comp]
  simp

@[simp] lemma finiteRepresentedTransition_self (eY :
  Scheme.EtaleCohomology.finiteRepresentedSetSheaf Y ≅
  F) :
    (finiteRepresentedTransition eY eY).hom = 𝟙 Y.obj := by
  apply (Scheme.EtaleCohomology.finiteRepresentedSetSheafHomEquiv Y Y).injective
  change Scheme.EtaleCohomology.finiteRepresentedSetSheafMap _ =
    Scheme.EtaleCohomology.finiteRepresentedSetSheafMap _
  simp [Scheme.EtaleCohomology.finiteRepresentedSetSheafMap_id]

/-- Pull a chart representative to a common etale test scheme and identify its
actual represented sheaf with the restriction of the original sheaf. -/
def finiteRepresentedCommonChartIso {S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (k : T ⟶ X) [Etale f] [Etale g] [Etale k]
    (h : g ≫ f = k) (Y : Scheme.FiniteEtale S)
    (eY : Scheme.EtaleCohomology.finiteRepresentedSetSheaf Y ≅
      (Scheme.EtaleCohomology.setEtaleRestriction f).obj
      F) :
    Scheme.EtaleCohomology.finiteRepresentedSetSheaf ((baseChange g).obj Y) ≅
      (Scheme.EtaleCohomology.setEtaleRestriction k).obj F := by
  subst k
  exact (finiteRepresentedRestrictionIso g Y).symm ≪≫
    (Scheme.EtaleCohomology.setEtaleRestriction g).mapIso eY ≪≫ (setEtaleRestrictionComp f g).app F

end AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 ac4fea07b7ca958320faff2522cd4b8f4e2afe810e0462a12d3e180cf6099ba6.
Definitions, hypotheses and universes are retained modulo native names. -/
