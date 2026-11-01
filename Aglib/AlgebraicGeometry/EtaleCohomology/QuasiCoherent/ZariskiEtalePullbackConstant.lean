/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiPullbackConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiComparison

/-! # The whole original constant square for Zariski--étale inverse image

The right square is proved on actual terminal étale objects. Native adjunction
conjugacy transports it to the original constant-integer source square.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Sheaf.Hypercohomology

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] hasSheafifyLarge

/-- Actual raised Zariski global sections. -/
abbrev zariskiGlobalSections (X : Scheme.{u}) :=
  (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1}).obj (op ⊤)

/-- The original constant adjunction at the terminal open, at raised values. -/
abbrev zariskiConstantAdjunction (X : Scheme.{u}) :=
  constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1} isTerminalTop

/-- Restriction preserves global sections via the actual terminal étale iso. -/
def zariskiRestrictionGlobalSectionsIso (X : Scheme.{u}) :
    zariskiRestriction X ⋙ zariskiGlobalSections X ≅ globalSections X :=
  continuousDirectImageTerminalSectionsIso.{u, u, u + 1, u, u + 1} (opensToEtale X)
    (Opens.grothendieckTopology X) (smallEtaleTopology X)
    ⊤ (opensToEtaleTopIsTerminal X) (etaleTerminal X) (etaleTerminalIsTerminal X)

/-- The full native constant comparison for restriction to the Zariski site. -/
def zariskiInverseImageConstantIso (X : Scheme.{u}) :
    constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1} ⋙
      zariskiInverseImage X ≅ constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  (((zariskiConstantAdjunction X).comp (zariskiEtaleAdjunction X)).ofNatIsoRight
    (zariskiRestrictionGlobalSectionsIso X)).leftAdjointUniq (constantAdjunction X)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Direct image on opens preserves raised global sections by terminal transport. -/
def opensDirectImageGlobalSectionsIso :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u + 1} f.base ⋙ zariskiGlobalSections Y ≅
      zariskiGlobalSections X :=
  continuousDirectImageTerminalSectionsIso.{u, u, u, u, u + 1} (Opens.map f.base)
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
    ⊤ (opensMapTopIsTerminal f) ⊤ isTerminalTop

/-- Raised Zariski inverse image preserves constants via its original adjunction. -/
def opensInverseImageConstantIso :
    constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u + 1} ⋙
      (Opens.map f.base).sheafPullback AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) ≅
      constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1} :=
  (((zariskiConstantAdjunction Y).comp
    ((Opens.map f.base).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))).ofNatIsoRight
        (opensDirectImageGlobalSectionsIso f)).leftAdjointUniq (zariskiConstantAdjunction X)

/-- The actual direct-image square respects global sections: both paths are
maps induced by the unique arrow between the same terminal étale objects. -/
theorem zariskiRestrictionDirectImageIso_globalSections :
    Functor.isoWhiskerRight (zariskiRestrictionDirectImageIso f) (zariskiGlobalSections Y) ≪≫
      Functor.associator (zariskiRestriction X)
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u + 1} f.base) (zariskiGlobalSections Y) ≪≫
      Functor.isoWhiskerLeft (zariskiRestriction X) (opensDirectImageGlobalSectionsIso f) ≪≫
      zariskiRestrictionGlobalSectionsIso X =
    Functor.associator (directImage f) (zariskiRestriction Y) (zariskiGlobalSections Y) ≪≫
      Functor.isoWhiskerLeft (directImage f) (zariskiRestrictionGlobalSectionsIso Y) ≪≫
      directImageGlobalSectionsIso f := by
  apply Iso.ext
  apply NatTrans.ext
  funext F
  change F.obj.map ((opensToEtaleBaseChangeIso f).inv.app ⊤).op ≫
      F.obj.map ((opensToEtale X).map
        ((opensMapTopIsTerminal f).uniqueUpToIso isTerminalTop).inv).op ≫
      F.obj.map ((opensToEtaleTopIsTerminal X).uniqueUpToIso
        (etaleTerminalIsTerminal X)).inv.op =
    F.obj.map ((siteBaseChange f).map ((opensToEtaleTopIsTerminal Y).uniqueUpToIso
      (etaleTerminalIsTerminal Y)).inv).op ≫
      F.obj.map (siteBaseChangeTerminalIso f).inv.op
  rw [← F.obj.map_comp, ← F.obj.map_comp, ← F.obj.map_comp]
  apply congrArg F.obj.map
  apply congrArg Quiver.Hom.op
  exact ((opensToEtaleTopIsTerminal Y).isTerminalObj (siteBaseChange f)).hom_ext _ _

/-- Native constant comparisons respect the whole geometric inverse-image
square, before specialization to the integer source. -/
theorem zariskiInverseImagePullbackIso_constant (A : AddCommGrpCat.{u + 1}) :
    (inverseImage f).map ((zariskiInverseImageConstantIso Y).hom.app A) ≫
      (inverseImageConstantIso f).hom.app A =
    (zariskiInverseImagePullbackIso f).hom.app
        ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u + 1}).obj A) ≫
      (zariskiInverseImage X).map ((opensInverseImageConstantIso f).hom.app A) ≫
      (zariskiInverseImageConstantIso X).hom.app A := by
  let ao := (Opens.map f.base).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  let σ := (Functor.associator
      (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u + 1})
      (zariskiInverseImage Y) (inverseImage f)).symm ≪≫
    Functor.isoWhiskerRight (zariskiInverseImageConstantIso Y) (inverseImage f) ≪≫
    inverseImageConstantIso f
  let E := Functor.associator (directImage f) (zariskiRestriction Y)
      (zariskiGlobalSections Y) ≪≫
    Functor.isoWhiskerLeft (directImage f) (zariskiRestrictionGlobalSectionsIso Y) ≪≫
    directImageGlobalSectionsIso f
  have hz := conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
    ((zariskiConstantAdjunction Y).comp (zariskiEtaleAdjunction Y))
    (constantAdjunction Y) (zariskiRestrictionGlobalSectionsIso Y)
  change conjugateEquiv (constantAdjunction Y)
    ((zariskiConstantAdjunction Y).comp (zariskiEtaleAdjunction Y))
      (zariskiInverseImageConstantIso Y).hom = (zariskiRestrictionGlobalSectionsIso Y).inv at hz
  have hf : conjugateEquiv (constantAdjunction X)
      ((constantAdjunction Y).comp (inverseImageAdjunction f))
      (inverseImageConstantIso f).hom = (directImageGlobalSectionsIso f).inv := by
    rw [← inverseImageConstantCanonicalIso_eq]
    change (conjugateEquiv (constantAdjunction X)
      ((constantAdjunction Y).comp (inverseImageAdjunction f)))
        ((conjugateEquiv (constantAdjunction X)
          ((constantAdjunction Y).comp (inverseImageAdjunction f))).symm
            (directImageGlobalSectionsIso f).inv) = _
    exact Equiv.apply_symm_apply _ _
  have ht : conjugateEquiv (constantAdjunction X)
      ((zariskiConstantAdjunction Y).comp
        ((zariskiEtaleAdjunction Y).comp (inverseImageAdjunction f))) σ.hom = E.inv := by
    dsimp only [σ, E]
    simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom]
    rw [← conjugateEquiv_comp _
        (((zariskiConstantAdjunction Y).comp (zariskiEtaleAdjunction Y)).comp
          (inverseImageAdjunction f)),
      ← conjugateEquiv_comp _ ((constantAdjunction Y).comp (inverseImageAdjunction f)),
      conjugateEquiv_associator_inv, conjugateEquiv_whiskerRight, hz, hf]
    simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, Category.assoc]
  have h := adjunctionComparison_comp_of_conjugate
    (constantAdjunction X) (zariskiConstantAdjunction X) (zariskiConstantAdjunction Y)
    ao (zariskiEtaleAdjunction X)
    ((zariskiEtaleAdjunction Y).comp (inverseImageAdjunction f))
    (opensInverseImageConstantIso f) (zariskiInverseImageConstantIso X) σ
    (opensDirectImageGlobalSectionsIso f) (zariskiRestrictionGlobalSectionsIso X) E
    (zariskiInverseImagePullbackIso f) (zariskiRestrictionDirectImageIso f)
    (conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _)
    (conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _) ht
    (conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _)
    (zariskiRestrictionDirectImageIso_globalSections f).symm
  have hA := congrArg (fun e => e.hom.app A) h
  simpa only [σ, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.id_comp, Iso.symm_hom] using hA

/-- The original continuous-site integer comparison for Zariski restriction. -/
abbrev zariskiInverseImageIntegerIso (X : Scheme.{u}) :=
  pullbackConstantIntegerIso.{u, u, u + 1, u, u + 1} (opensToEtale X)
    (Opens.grothendieckTopology X) (smallEtaleTopology X)
    ⊤ isTerminalTop (opensToEtaleTopIsTerminal X)

/-- The original continuous-site integer comparison for raised opens pullback. -/
abbrev opensInverseImageIntegerIso :=
  pullbackConstantIntegerIso.{u, u, u, u, u + 1} (Opens.map f.base)
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
    ⊤ isTerminalTop (opensMapTopIsTerminal f)

/-- Original Zariski--étale integer comparison, normalized at the chosen
terminal étale object through its actual terminal isomorphism. -/
theorem zariskiInverseImageIntegerIso_eq (X : Scheme.{u}) :
    zariskiInverseImageIntegerIso X =
      (zariskiInverseImageConstantIso X).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) := by
  apply Iso.ext
  exact pullbackConstantIntegerIso_hom_eq_terminalComparison.{u, u, u + 1, u, u + 1}
    (opensToEtale X) (Opens.grothendieckTopology X) (smallEtaleTopology X)
    ⊤ isTerminalTop (opensToEtaleTopIsTerminal X) (etaleTerminal X)
    (etaleTerminalIsTerminal X)

/-- Raised opens source normalization uses its native source, not a fictitious
universe-polymorphic version of the small native Zariski source. -/
theorem opensInverseImageIntegerIso_eq :
    opensInverseImageIntegerIso f =
      (opensInverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) := by
  apply Iso.ext
  exact pullbackConstantIntegerIso_hom_eq_terminalComparison.{u, u, u, u, u + 1}
    (Opens.map f.base) (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
    ⊤ isTerminalTop (opensMapTopIsTerminal f) ⊤ isTerminalTop

/-- The whole original integer-source square for geometric pullback. -/
theorem zariskiInverseImagePullbackIso_integer :
    (inverseImage f).map (zariskiInverseImageIntegerIso Y).hom ≫
      (inverseImageConstantIso f).hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) =
    (zariskiInverseImagePullbackIso f).hom.app
        ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫
      (zariskiInverseImage X).map (opensInverseImageIntegerIso f).hom ≫
      (zariskiInverseImageIntegerIso X).hom := by
  rw [zariskiInverseImageIntegerIso_eq, zariskiInverseImageIntegerIso_eq,
    opensInverseImageIntegerIso_eq]
  exact zariskiInverseImagePullbackIso_constant f _

/-- The inverse-source law in the exact orientation used by original
`extPrecompMap` composites; no cohomology group is silently identified. -/
theorem zariskiInverseImagePullbackIso_integer_inv :
    (inverseImageConstantIso f).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫
      (inverseImage f).map (zariskiInverseImageIntegerIso Y).inv ≫
      (zariskiInverseImagePullbackIso f).hom.app
        ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) =
    (zariskiInverseImageIntegerIso X).inv ≫
      (zariskiInverseImage X).map (opensInverseImageIntegerIso f).inv := by
  let a := (inverseImage f).mapIso (zariskiInverseImageIntegerIso Y)
  let b := (inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let c := (zariskiInverseImagePullbackIso f).app
    ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  let d := (zariskiInverseImage X).mapIso (opensInverseImageIntegerIso f)
  let e := zariskiInverseImageIntegerIso X
  have h : a.hom ≫ b.hom = c.hom ≫ d.hom ≫ e.hom :=
    zariskiInverseImagePullbackIso_integer f
  change b.inv ≫ a.inv ≫ c.hom = e.inv ≫ d.inv
  apply (cancel_mono (d.hom ≫ e.hom)).mp
  simp only [Category.assoc]
  rw [← h, a.inv_hom_id_assoc, b.inv_hom_id, d.inv_hom_id_assoc, e.inv_hom_id]

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
