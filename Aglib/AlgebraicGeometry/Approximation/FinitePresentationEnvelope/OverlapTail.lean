/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Compatible principal overlap coordinates on a cofinal tail

Once a stage has the prescribed principal image, its sections pull back to
compatible sections on every later stage. The image presentation and original
limit-section equations are retained literally.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.FinitePresentationEnvelope

universe u v

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
  (i : I) {J : Type v} (r : J → Γ(D.obj i, ⊤))

/-- Pull back the chosen stage sections to the actual cofinal tail. -/
def tailSections (j : Over i) (l : J) : Γ(D.obj j.left, ⊤) :=
  (D.map j.hom).appTop (r l)

/-- The chosen principal coordinates commute with every actual tail transition. -/
theorem tailSections_naturality {j k : Over i} (q : j ⟶ k) (l : J) :
    (D.map q.left).appTop (tailSections D i r k l) = tailSections D i r j l := by
  dsimp only [tailSections]
  rw [← CommRingCat.comp_apply, ← Hom.comp_appTop, ← Functor.map_comp, Over.w]

/-- Tail coordinates still pull back to the same original section. -/
theorem tailSections_projection (c : Cone D) (j : Over i) (l : J) :
    (c.π.app j.left).appTop (tailSections D i r j l) = (c.π.app i).appTop (r l) := by
  dsimp only [tailSections]
  rw [← CommRingCat.comp_apply, ← Hom.comp_appTop, c.w]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma preimage_iSup_basicOpen
    {A B : CommRingCat.{u}} (φ : A ⟶ B) {L : Type v} (r : L → A) :
    Spec.map φ ⁻¹ᵁ (⨆ l, PrimeSpectrum.basicOpen (r l)) =
      ⨆ l, PrimeSpectrum.basicOpen (φ.hom (r l)) := by
  change Spec.map φ ⁻¹ᵁ (⨆ l, PrimeSpectrum.basicOpen (r l)) =
    ⨆ l, Spec.map φ ⁻¹ᵁ PrimeSpectrum.basicOpen (r l)
  exact (Spec.map φ).preimage_iSup _

/-- Principal image presentations are preserved on the cofinal tail of a
quasi-affine system with affine transition maps. -/
theorem tailSections_opensRange
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, IsQuasiAffine (D.obj j)]
    (hr : (D.obj i).toSpecΓ.opensRange = ⨆ l, PrimeSpectrum.basicOpen (r l))
    (j : Over i) :
    (D.obj j.left).toSpecΓ.opensRange =
      ⨆ l, PrimeSpectrum.basicOpen (tailSections D i r j l) := by
  calc
    (D.obj j.left).toSpecΓ.opensRange =
        Spec.map (D.map j.hom).appTop ⁻¹ᵁ (D.obj i).toSpecΓ.opensRange :=
      (Scheme.preimage_opensRange_toSpecΓ (D.map j.hom)).symm
    _ = Spec.map (D.map j.hom).appTop ⁻¹ᵁ
        (⨆ l, PrimeSpectrum.basicOpen (r l)) :=
      congrArg (fun U => Spec.map (D.map j.hom).appTop ⁻¹ᵁ U) hr
    _ = ⨆ l, PrimeSpectrum.basicOpen (tailSections D i r j l) :=
      preimage_iSup_basicOpen (D.map j.hom).appTop r


end AlgebraicGeometry.Scheme.FinitePresentationEnvelope
