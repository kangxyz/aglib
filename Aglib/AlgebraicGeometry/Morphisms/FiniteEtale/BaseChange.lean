/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Fiber
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Base change of finite etale schemes and their point fibres

Arbitrary scheme morphisms pull back the actual finite etale objects. Identity and
composition use the canonical Over pullback isomorphisms. The fibre equivalence
is the actual map-pullback adjunction, with its forward lift and reverse projection.

Source: R5Lab/AlgebraicGeometry/FiniteEtale/BaseChange.lean
at R5 revision 2f9ca464b192cff865858dda70b2d8e5dca8b3df.
SHA256: 38e14f8b7e7d37836d0091b104fd2363ba6366bf801a7220f1e7f64d66450ea2
Selection: the actual pullback functor, canonical identity/composition and fibre base-change maps.
Actual objects, maps, universes and hypotheses are retained.
-/
@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- Pullback of finite étale covers along a scheme morphism. -/
def baseChange {X S : Scheme.{u}} (f : S ⟶ X) : FiniteEtale X ⥤ FiniteEtale S :=
  (finiteEtaleProperty S).lift (forget X ⋙ Over.pullback f) (fun Y => by
    dsimp [finiteEtaleProperty, forget]
    exact ⟨inferInstance, inferInstance⟩)

/-- Forgetting finite etaleness identifies base change with the actual `Over.pullback` functor. -/
def baseChangeForgetIso {X S : Scheme.{u}} (f : S ⟶ X) :
    baseChange f ⋙ forget S ≅ forget X ⋙ Over.pullback f := Iso.refl _

@[simp] theorem baseChange_obj_hom {X S : Scheme.{u}} (f : S ⟶ X) (Y : FiniteEtale X) :
    ((baseChange f).obj Y).obj.hom = pullback.snd Y.obj.hom f := rfl

/-- Pullback along the identity is naturally isomorphic to the identity functor. -/
def baseChangeId (X : Scheme.{u}) : baseChange (𝟙 X) ≅ 𝟭 (FiniteEtale X) :=
  NatIso.ofComponents
    (fun Y => ObjectProperty.isoMk _ ((Over.pullbackId).app Y.obj))
    (fun f => by
      apply ObjectProperty.hom_ext
      exact (Over.pullbackId).hom.naturality f.hom)

/-- Pullback respects composition up to the canonical natural isomorphism. -/
def baseChangeComp {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) :
    baseChange (g ≫ f) ≅ baseChange f ⋙ baseChange g :=
  NatIso.ofComponents
    (fun Y => ObjectProperty.isoMk _ ((Over.pullbackComp g f).app Y.obj))
    (fun h => by
      apply ObjectProperty.hom_ext
      exact (Over.pullbackComp g f).hom.naturality h.hom)

/-- The universal property of pullback identifies the two sets of point lifts. -/
def fiberBaseChangeEquiv {X S : Scheme.{u}} {K : Type u} [Field K]
    (f : S ⟶ X) (x : Spec (CommRingCat.of K) ⟶ S) (Y : FiniteEtale X) :
    Fiber (x ≫ f) Y ≃ Fiber x ((baseChange f).obj Y) :=
  (Over.mapPullbackAdj f).homEquiv (Over.mk x) Y.obj

@[simp] theorem fiberBaseChangeEquiv_left {X S : Scheme.{u}} {K : Type u} [Field K]
    (f : S ⟶ X) (x : Spec (CommRingCat.of K) ⟶ S) (Y : FiniteEtale X)
    (p : Fiber (x ≫ f) Y) :
    (fiberBaseChangeEquiv f x Y p).left = pullback.lift p.left x (Over.w p) := by
  simp only [fiberBaseChangeEquiv, Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

@[simp] theorem fiberBaseChangeEquiv_symm_left {X S : Scheme.{u}} {K : Type u} [Field K]
    (f : S ⟶ X) (x : Spec (CommRingCat.of K) ⟶ S) (Y : FiniteEtale X)
    (p : Fiber x ((baseChange f).obj Y)) :
    ((fiberBaseChangeEquiv f x Y).symm p).left = p.left ≫ pullback.fst Y.obj.hom f := by
  rfl

/-- Fibre compatibility with base change, natural in the finite étale cover. -/
def fiberBaseChangeIso {X S : Scheme.{u}} {K : Type u} [Field K]
    (f : S ⟶ X) (x : Spec (CommRingCat.of K) ⟶ S) :
    fiber (x ≫ f) ≅ baseChange f ⋙ fiber x :=
  Functor.isoWhiskerLeft (forget X)
    ((Over.mapPullbackAdj f).compCoyonedaIso.app (op (Over.mk x)))

theorem fiberBaseChangeIso_hom_app_apply
    {X S : Scheme.{u}} {K : Type u} [Field K]
    (f : S ⟶ X) (x : Spec (CommRingCat.of K) ⟶ S) (Y : FiniteEtale X)
    (p : Fiber (x ≫ f) Y) :
    (fiberBaseChangeIso f x).hom.app Y p = fiberBaseChangeEquiv f x Y p := rfl

theorem fiberBaseChangeIso_inv_app_apply
    {X S : Scheme.{u}} {K : Type u} [Field K]
    (f : S ⟶ X) (x : Spec (CommRingCat.of K) ⟶ S) (Y : FiniteEtale X)
    (p : Fiber x ((baseChange f).obj Y)) :
    (fiberBaseChangeIso f x).inv.app Y p = (fiberBaseChangeEquiv f x Y).symm p := rfl
/-- Fibre compatibility with base change in `FintypeCat`. -/
def fiberToFiniteBaseChangeIso {X S : Scheme.{u}} {K : Type u} [Field K]
    (f : S ⟶ X) (x : Spec (CommRingCat.of K) ⟶ S) :
    fiberToFinite (x ≫ f) ≅ baseChange f ⋙ fiberToFinite x :=
  Functor.fullyFaithfulCancelRight FintypeCat.incl (fiberBaseChangeIso f x)

end AlgebraicGeometry.Scheme.FiniteEtale
