module

import Aglib.AlgebraicGeometry.Blowup.AffineUniversalProperty
import Mathlib.Data.ZMod.Basic

/-! Consumers of the actual affine blowup universal property and its boundary cases. -/

noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Blowup
universe u

namespace AglibTest.AffineBlowupUniversalProperty

/-- The original image-ideal predicate gives the literal final-object property on every
test scheme, without affine, reduced, Noetherian or finite-generation inputs. -/
example {A : Type u} [CommRing A] (I : Ideal A) (T : Scheme.{u})
    (f : T ⟶ Spec (.of A)) (hf : cartierPullback (affineCenter A I) f) :
    ∃! g : T ⟶ affineProj I, g ≫ affineProjMap I = f :=
  affineProjMap_universal I T f hf

/-- The realized interface retains the exact pre-existing scheme and morphism. -/
example {A : Type u} [CommRing A] (I : Ideal A) :
    (affineProjBlowupDatum I).Y = affineProj I ∧
      (affineProjBlowupDatum I).map = affineProjMap I := ⟨rfl, rfl⟩

private lemma unitCentre_cartier_id (S : Type u) [CommRing S] :
    cartierPullback (affineCenter S ⊤) (𝟙 (Spec (.of S))) := by
  unfold cartierPullback
  rw [Scheme.IdealSheafData.comap_id]
  exact affineCenter_rankOne_of_equiv S ⊤ Submodule.topEquiv.symm

/-- A concrete nonreduced test ring is admitted by the actual factory. -/
example : ∃! g : Spec (.of (ZMod 4)) ⟶ affineProj (⊤ : Ideal (ZMod 4)),
    g ≫ affineProjMap (⊤ : Ideal (ZMod 4)) = 𝟙 (Spec (.of (ZMod 4))) :=
  affineProjMap_universal ⊤ _ _ (unitCentre_cartier_id (ZMod 4))

/-- The zero centre forces the precise empty-test boundary, through the actual empty
native Rees Proj rather than a nontriviality assumption. -/
example {A : Type u} [CommRing A] (T : Scheme.{u}) (f : T ⟶ Spec (.of A))
    (hf : cartierPullback (affineCenter A ⊥) f) : IsEmpty T := by
  obtain ⟨g, _, _⟩ := affineProjMap_universal ⊥ T f hf
  exact ⟨fun x => isEmptyElim (g x)⟩

end AglibTest.AffineBlowupUniversalProperty
