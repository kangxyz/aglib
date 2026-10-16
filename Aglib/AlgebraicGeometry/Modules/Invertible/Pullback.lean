/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Pullback.Free
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
# Pullback of line bundles

The native scheme module-sheaf pullback functor preserves local rank one.
Its open-local trivializations are transported through the actual restricted
scheme square and the canonical module pullback composition isomorphisms.
This constructs pullback of line bundles and isomorphism classes, with
identity, composition and unit laws. Tensor compatibility and the additive
Picard homomorphism are supplied by `PullbackTensor.Local`.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Picard.Pullback`
at revision `95a3772b895fbc19a81684be4ffd519d0fdcd6b3`.
The primary namespace is `AlgebraicGeometry.Scheme.Modules.Invertible`;
source names are provenance.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules.Invertible
universe u
variable {X Y : Scheme.{u}}

theorem isLocallyRankOne_iff_restrict_unit (M : SheafOfModules.{u} X.ringCatSheaf) :
    IsLocallyRankOne X M ↔ ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj M ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  rw [isLocallyRankOne_iff_local_unit]
  constructor
  · intro h x
    obtain ⟨U, hxU, ⟨e⟩⟩ := h x
    exact ⟨U, hxU, ⟨((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
      (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫ overUnitIso U⟩⟩
  · intro h x
    obtain ⟨U, hxU, ⟨e⟩⟩ := h x
    refine ⟨U, hxU, ⟨?_⟩⟩
    exact (Scheme.Modules.overEquiv U).functor.preimageIso
      ((Scheme.Modules.overFunctorEquiv U).app M ≪≫ e ≪≫ (overUnitIso U).symm)

theorem pullback_locallyRankOne (f : X ⟶ Y) (M : SheafOfModules.{u} Y.ringCatSheaf)
    (hM : IsLocallyRankOne Y M) :
    IsLocallyRankOne X ((Scheme.Modules.pullback f).obj M) := by
  rw [isLocallyRankOne_iff_restrict_unit] at hM ⊢
  intro x
  obtain ⟨U, hxU, ⟨e⟩⟩ := hM (f.base x)
  exact ⟨f ⁻¹ᵁ U, hxU, ⟨((Scheme.Modules.pullbackRestrictIso f U).app M) ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso e ≪≫ pullbackUnitIso (f ∣_ U)⟩⟩

/-- Pullback of a line bundle along the scheme morphism `f`. -/
def pullbackLineBundle (f : X ⟶ Y) (L : LineBundle Y) : LineBundle X :=
  ⟨(Scheme.Modules.pullback f).obj L.val, pullback_locallyRankOne f L.val L.property⟩

/-- Pullback of isomorphism classes of line bundles along `f`. -/
def pullbackClass (f : X ⟶ Y) (a : PicardGroup Y) : PicardGroup X :=
  Quotient.liftOn a (fun L => classOf X (pullbackLineBundle f L)) (by
    intro L M ⟨e⟩
    exact Quotient.sound ⟨(Scheme.Modules.pullback f).mapIso e⟩)

@[simp] theorem pullbackClass_classOf (f : X ⟶ Y) (L : LineBundle Y) :
    pullbackClass f (classOf Y L) = classOf X (pullbackLineBundle f L) := rfl

@[simp] theorem pullbackClass_id (a : PicardGroup X) : pullbackClass (𝟙 X) a = a := by
  induction a using Quotient.inductionOn with | h L =>
    exact Quotient.sound ⟨(Scheme.Modules.pullbackId X).app L.val⟩

@[simp] theorem pullbackClass_comp {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : PicardGroup Z) : pullbackClass (f ≫ g) a = pullbackClass f (pullbackClass g a) := by
  induction a using Quotient.inductionOn with | h L =>
    exact Quotient.sound ⟨((Scheme.Modules.pullbackComp f g).app L.val).symm⟩

@[simp] theorem pullbackClass_zero (f : X ⟶ Y) : pullbackClass f 0 = 0 := by
  apply Quotient.sound
  exact ⟨(Scheme.Modules.pullback f).mapIso
    (CategoryTheory.Limits.coproductUniqueIso
      (fun _ : PUnit.{u + 1} => SheafOfModules.unit Y.ringCatSheaf)) ≪≫
    pullbackUnitIso f ≪≫ (CategoryTheory.Limits.coproductUniqueIso
      (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)).symm⟩
end AlgebraicGeometry.Scheme.Modules.Invertible
