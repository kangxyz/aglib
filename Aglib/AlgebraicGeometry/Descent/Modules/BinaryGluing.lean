/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.Modules.ZariskiStack
public import Aglib.CategoryTheory.Sites.Descent.Binary

/-!
# Actual line bundles glued from a single binary overlap isomorphism

The existing open-cover gluing supplies the actual module sheaf and the
entire native descent comparison. Binary descent constructs its cocycle
from the given overlap isomorphism, and local rank one descends on the
specified two-open cover. The local bundles need not be trivial.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace OpenCoverGluing

variable {S : Scheme.{u}} {ι : Type u} {X : ι → Scheme.{u}}
  (f : ∀ i, X i ⟶ S) [∀ i, IsOpenImmersion (f i)]
  (D : pullbackPseudofunctor.{u}.DescentData f)

/-- The original comparison of open-cover gluing is invertible, using the
proved cocycle step for arbitrary module sheaves. -/
def actualComparisonIso :
    (pullbackPseudofunctor.toDescentData f).obj (glued f D) ≅ D :=
  comparisonIso f D fun i => by
    have : IsIso (toObj f D i) := isIso_toObj f D i
      (projectionSurjective S ι X f D i)
    dsimp [phi]
    infer_instance

/-- The original pullback comparison with one specified local coefficient. -/
def actualLocalIso (i : ι) : (pullback (f i)).obj (glued f D) ≅ D.obj i := by
  have : IsIso (toObj f D i) := isIso_toObj f D i
    (projectionSurjective S ι X f D i)
  exact ((restrictFunctorIsoPullback (f i)).app (glued f D)).symm ≪≫ asIso (toObj f D i)

/-- Local rank one of the actual glued coefficient follows from its local
coefficients on the supplied covering family. -/
theorem isLocallyRankOne_glued (hcover : iSup (fun i => (f i).opensRange) = ⊤)
    (hD : ∀ i, IsLocallyRankOne (X i) (D.obj i)) :
    IsLocallyRankOne S (glued f D) := by
  apply isLocallyRankOne_of_cover_restrict (glued f D)
    (fun i => (f i).opensRange) hcover
  intro i
  apply isLocallyRankOne_of_iso _ (restrictOpensRangeIso (f i) (glued f D)).symm
  apply pullback_locallyRankOne
  exact isLocallyRankOne_of_iso _ (actualLocalIso f D i).symm (hD i)

end OpenCoverGluing

namespace BinaryGluing

open CategoryTheory.Pseudofunctor.BinaryDescent

variable {S X₀ X₁ W : Scheme.{u}} (f₀ : X₀ ⟶ S) (f₁ : X₁ ⟶ S)
  [IsOpenImmersion f₀] [IsOpenImmersion f₁]
  (p₀ : W ⟶ X₀) (p₁ : W ⟶ X₁) (h : IsPullback p₀ p₁ f₀ f₁)
  (A : LineBundle X₀) (B : LineBundle X₁)
  (e : (pullback p₀).obj A.val ≅ (pullback p₁).obj B.val)

instance open_arrows (i : ULift.{u} Bool) : IsOpenImmersion (arrows f₀ f₁ i) := by
  rcases i with ⟨i⟩
  cases i <;> dsimp [arrows] <;> infer_instance

/-- Native descent data for the two actual local line bundles. -/
def data : pullbackPseudofunctor.{u}.DescentData
    (fun i : ULift.{u} Bool => arrows f₀ f₁ i) :=
  descentData pullbackPseudofunctor f₀ f₁ p₀ p₁ h A.val B.val e

/-- The given binary open cover is the original family used for gluing. -/
theorem family_covers (hcover : f₀.opensRange ⊔ f₁.opensRange = ⊤) :
    iSup (fun i : ULift.{u} Bool => (arrows f₀ f₁ i).opensRange) = ⊤ := by
  apply top_le_iff.mp
  intro x _
  have hx : x ∈ f₀.opensRange ⊔ f₁.opensRange := by rw [hcover]; trivial
  rcases hx with hx | hx
  · exact Opens.mem_iSup.mpr ⟨⟨false⟩, hx⟩
  · exact Opens.mem_iSup.mpr ⟨⟨true⟩, hx⟩

/-- The actual global line bundle obtained by gluing the specified two
local line bundles through their specified overlap isomorphism. -/
def lineBundle (hcover : f₀.opensRange ⊔ f₁.opensRange = ⊤) : LineBundle S := by
  let D := data f₀ f₁ p₀ p₁ h A B e
  refine ⟨OpenCoverGluing.glued _ D,
    OpenCoverGluing.isLocallyRankOne_glued _ D (family_covers f₀ f₁ hcover) ?_⟩
  rintro ⟨i⟩
  cases i
  · exact A.property
  · exact B.property

/-- The entire native descent comparison, including the specified overlap
arrow, for the actual glued line bundle. -/
def comparisonIso (hcover : f₀.opensRange ⊔ f₁.opensRange = ⊤) :
    (pullbackPseudofunctor.toDescentData (fun i : ULift.{u} Bool => arrows f₀ f₁ i)).obj
        (lineBundle f₀ f₁ p₀ p₁ h A B e hcover).val ≅
      data f₀ f₁ p₀ p₁ h A B e :=
  OpenCoverGluing.actualComparisonIso _ _

end BinaryGluing

end AlgebraicGeometry.Scheme.Modules
