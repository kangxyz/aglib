/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Map
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Flat
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor

/-!
# Actual fibre inclusions and conditional ideal comparisons

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/Fibre.lean`, SHA-256
  `3287d66f8b79c5b2296483ffcee86e204285eb2f42bb6b53f5b1291cb4604ba5`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `doc/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules
open LinearMap
open AlgebraicGeometry.Scheme.Modules.Invertible

section
namespace AlgebraicGeometry.Scheme.Hom

variable {S T X D : Scheme.{u}} (p : X ⟶ S) (i : D ⟶ X) (t : T ⟶ S)

/-- The canonical map between the base changes of the composite and ambient structure morphisms. -/
def fibreInclusion : pullback (i ≫ p) t ⟶ pullback p t :=
  pullback.lift (pullback.fst (i ≫ p) t ≫ i) (pullback.snd (i ≫ p) t)
    (by rw [Category.assoc, pullback.condition])

@[reassoc (attr := simp)] theorem fibreInclusion_fst :
    fibreInclusion p i t ≫ pullback.fst p t = pullback.fst (i ≫ p) t ≫ i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem fibreInclusion_snd :
    fibreInclusion p i t ≫ pullback.snd p t = pullback.snd (i ≫ p) t :=
  pullback.lift_snd _ _ _

theorem fibreInclusion_isPullback :
    IsPullback (pullback.fst (i ≫ p) t) (fibreInclusion p i t) i (pullback.fst p t) := by
  apply IsPullback.flip
  apply IsPullback.of_right (h₁₂ := pullback.snd p t) (h₂₂ := p) (v₁₃ := t)
    _ (fibreInclusion_fst p i t) (IsPullback.of_hasPullback p t).flip
  simpa only [fibreInclusion_snd] using (IsPullback.of_hasPullback (i ≫ p) t).flip

/-- The canonical fibre inclusion is closed when the original immersion is closed. -/
instance fibreInclusion_isClosedImmersion [IsClosedImmersion i] :
    IsClosedImmersion (fibreInclusion p i t) :=
  MorphismProperty.of_isPullback (fibreInclusion_isPullback p i t) inferInstance

/-- The actual fibre-ideal comparison, conditional on the displayed pointwise base-change supplier.
-/
def fibreIdealIso (hbase : (∀ (S T X Y D D' : Scheme.{u}) (p : X ⟶ S) (q : T ⟶ S) (p' : Y ⟶ T)
    (b : Y ⟶ X) (i : D ⟶ X) (i' : D' ⟶ Y) (a : D' ⟶ D)
    (h : a ≫ i = i' ≫ b),
    IsPullback b p' p q → IsPullback a i' i b → IsClosedImmersion i →
      IsLocallyRankOne X (idealModule i) → Flat (i ≫ p) →
        IsIso (idealPullbackMap i i' b a h)))
    [IsClosedImmersion i] [Flat (i ≫ p)]
    (hI : IsLocallyRankOne X (idealModule i)) :
    (Scheme.Modules.pullback (pullback.fst p t)).obj (idealModule i) ≅
      idealModule (fibreInclusion p i t) := by
  letI := hbase S T X (pullback p t) D (pullback (i ≫ p) t)
    p t (pullback.snd p t) (pullback.fst p t) i (fibreInclusion p i t)
    (pullback.fst (i ≫ p) t) (fibreInclusion_fst p i t).symm
    (IsPullback.of_hasPullback p t) (fibreInclusion_isPullback p i t) inferInstance hI inferInstance
  exact asIso (idealPullbackMap i (fibreInclusion p i t) (pullback.fst p t)
    (pullback.fst (i ≫ p) t) (fibreInclusion_fst p i t).symm)

@[reassoc] theorem fibreIdealIso_inclusion (hbase : (∀ (S T X Y D D' : Scheme.{u}) (p : X ⟶ S) (q :
  T ⟶ S) (p' : Y ⟶ T)
    (b : Y ⟶ X) (i : D ⟶ X) (i' : D' ⟶ Y) (a : D' ⟶ D)
    (h : a ≫ i = i' ≫ b),
    IsPullback b p' p q → IsPullback a i' i b → IsClosedImmersion i →
      IsLocallyRankOne X (idealModule i) → Flat (i ≫ p) →
        IsIso (idealPullbackMap i i' b a h)))
    [IsClosedImmersion i] [Flat (i ≫ p)]
    (hI : IsLocallyRankOne X (idealModule i)) :
    (fibreIdealIso p i t hbase hI).hom ≫ idealInclusion (fibreInclusion p i t) =
      (Scheme.Modules.pullback (pullback.fst p t)).map (idealInclusion i) ≫
        SheafOfModules.pullbackObjUnitToUnit (pullback.fst p t).toRingCatSheafHom :=
  idealPullbackMap_inclusion i (fibreInclusion p i t) (pullback.fst p t)
    (pullback.fst (i ≫ p) t) (fibreInclusion_fst p i t).symm

end AlgebraicGeometry.Scheme.Hom
end

section
namespace AlgebraicGeometry.Scheme.Hom

variable {S T X D : Scheme.{u}} (p : X ⟶ S) (i : D ⟶ X) (t : T ⟶ S)
variable (hbase : (∀ (S T X Y D D' : Scheme.{u}) (p : X ⟶ S) (q : T ⟶ S) (p' : Y ⟶ T)
    (b : Y ⟶ X) (i : D ⟶ X) (i' : D' ⟶ Y) (a : D' ⟶ D)
    (h : a ≫ i = i' ≫ b),
    IsPullback b p' p q → IsPullback a i' i b → IsClosedImmersion i →
      IsLocallyRankOne X (idealModule i) → Flat (i ≫ p) →
        IsIso (idealPullbackMap i i' b a h))) [IsClosedImmersion i] [Flat (i ≫ p)]
variable (hI : IsLocallyRankOne X (idealModule i))

/-- The line bundle carried by the actual fibre ideal using the displayed base-change comparison. -/
def fibreIdealLineBundle : LineBundle (pullback p t) := by
  let e := fibreIdealIso p i t hbase hI
  let e' : ((Scheme.Modules.pullback (pullback.fst p t)).obj (idealModule i) :
      SheafOfModules.{u} (pullback p t).ringCatSheaf) ≅ idealModule (fibreInclusion p i t) :=
    ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩
  exact ⟨idealModule (fibreInclusion p i t), isLocallyRankOne_of_iso _ e'
    (pullback_locallyRankOne (pullback.fst p t) (idealModule i) hI)⟩

end AlgebraicGeometry.Scheme.Hom
end
