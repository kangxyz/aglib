/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.ZariskiEtale
public import Aglib.AlgebraicGeometry.Sites.EtaleTopos

/-! # Actual base change of the Zariski--étale site comparison

The preimage open and the original small-site base change are identified by the
native pullback square of the restricted morphism. Naturality is proved on the
actual maps over the source scheme, not supplied as a cohomology hypothesis.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The original pullback of an open chart is the native preimage open. -/
def opensToEtaleBaseChangeObjIso (U : Y.Opens) :
    (EtaleCohomology.siteBaseChange f).obj ((opensToEtale Y).obj U) ≅
      (opensToEtale X).obj (f ⁻¹ᵁ U) :=
  MorphismProperty.Over.isoMk (isPullback_morphismRestrict f U).isoPullback.symm
    (isPullback_morphismRestrict f U).isoPullback_inv_snd

/-- The comparison keeps the original projection to the source scheme. -/
@[reassoc (attr := simp)]
theorem opensToEtaleBaseChangeObjIso_hom_ι (U : Y.Opens) :
    (opensToEtaleBaseChangeObjIso f U).hom.left ≫ (f ⁻¹ᵁ U).ι =
      pullback.snd U.ι f :=
  (isPullback_morphismRestrict f U).isoPullback_inv_snd

/-- The other leg is the original restriction of the scheme morphism. -/
@[reassoc (attr := simp)]
theorem opensToEtaleBaseChangeObjIso_hom_restrict (U : Y.Opens) :
    (opensToEtaleBaseChangeObjIso f U).hom.left ≫ f ∣_ U =
      pullback.fst U.ι f :=
  (isPullback_morphismRestrict f U).isoPullback_inv_fst

/-- The whole native site square, including transition maps of open charts. -/
def opensToEtaleBaseChangeIso :
    opensToEtale Y ⋙ EtaleCohomology.siteBaseChange f ≅
      Opens.map f.base ⋙ opensToEtale X :=
  NatIso.ofComponents (opensToEtaleBaseChangeObjIso f) (by
    intro U V g
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono (f ⁻¹ᵁ V).ι).mp
    have h₁ := MorphismProperty.Over.w
      (((opensToEtale Y ⋙ EtaleCohomology.siteBaseChange f).map g) ≫
        (opensToEtaleBaseChangeObjIso f V).hom)
    have h₂ := MorphismProperty.Over.w
      ((opensToEtaleBaseChangeObjIso f U).hom ≫
        ((Opens.map f.base ⋙ opensToEtale X).map g))
    exact h₁.trans h₂.symm)

end AlgebraicGeometry.Scheme
