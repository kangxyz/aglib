/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.HenselianConstant.Sections
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.HenselianEquivalence
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.FieldFiber
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverSheafFunctor

/-!
# The actual split root cover over a strictly henselian local spectrum

The map from the labelled constant cover is defined by actual global root
sections. Its residue fibre is bijective; reflection of isomorphisms is used
only in the native finite-etale category, not for arbitrary sheaves.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Group
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.HenselianConstant

universe u
variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]

/-- Over a strictly henselian local ring, the actual residue fibre is an equivalence
on finite-etale covers. -/
instance residueFiber_isEquivalence :
    (fiberToFinite (Scheme.LocalRing.residueSpecMap R)).IsEquivalence := by
  have e := fiberToFiniteBaseChangeIso (Scheme.LocalRing.residueSpecMap R)
    (𝟙 (Spec (.of (IsLocalRing.ResidueField R))))
  rw [Category.id_comp] at e
  exact Functor.isEquivalence_of_iso e.symm

variable (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(Spec (.of R), ⊤)))

attribute [local instance] Over.cartesianMonoidalCategory
/-- The native commutative group structure on the actual scheme of n-th roots. -/
local instance : CommGrpObj (MultiplicativeGroup.rootsScheme (Spec (.of R)) n) :=
  MultiplicativeGroup.rootsCommGroup (Spec (.of R)) n

/-- The existing root scheme, viewed as its proved finite-etale cover. -/
def rootCover : Scheme.FiniteEtale (Spec (.of R)) :=
  ⟨MultiplicativeGroup.rootsScheme (Spec (.of R)) n,
    RootsFiniteEtale.rootsScheme_finite _ n hn,
    RootsFiniteEtale.rootsScheme_etale _ n hn hinv⟩

/-- The section attached to a label, as a morphism of finite-etale covers. -/
def rootCoverComponent (a : ULift.{u} (ZMod n)) :
    terminalCover (Spec (.of R)) ⟶ rootCover R n hn hinv :=
  ObjectProperty.homMk ((globalRootCoordinates R n hn hinv a.down).toMul)

/-- The actual map from the labelled constant cover, using actual global root sections. -/
def rootCoverMap :
    letI : NeZero n := ⟨hn.ne'⟩
    trivialCover (Spec (.of R)) (ULift.{u} (ZMod n)) ⟶ rootCover R n hn hinv := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact Sigma.desc (rootCoverComponent R n hn hinv)

/-- Each labelled component is sent by its actual global root section. -/
theorem rootCoverMap_component (a : ULift.{u} (ZMod n)) :
    letI : NeZero n := ⟨hn.ne'⟩
    (trivialCoverι (Spec (.of R)) (ULift.{u} (ZMod n)) a ≫ rootCoverMap R n hn hinv).hom =
      (globalRootCoordinates R n hn hinv a.down).toMul := by
  let : NeZero n := ⟨hn.ne'⟩
  exact congrArg (fun k => k.hom) (Sigma.ι_comp_desc
    (rootCoverComponent R n hn hinv) a)

/-- The map on the literal residue fibre is restriction of the chosen global root. -/
theorem rootCoverMap_fiber (a : ULift.{u} (ZMod n)) :
    letI : NeZero n := ⟨hn.ne'⟩
    (fiberToFinite (Scheme.LocalRing.residueSpecMap R)).map (rootCoverMap R n hn hinv)
      (trivialCoverFiberPoint (ULift.{u} (ZMod n)) (Scheme.LocalRing.residueSpecMap R) a) =
      rootSectionRestriction R n (globalRootCoordinates R n hn hinv a.down).toMul := by
  let : NeZero n := ⟨hn.ne'⟩
  apply Over.OverMorphism.ext
  change ((Scheme.LocalRing.residueSpecMap R) ≫
      (trivialCoverι (Spec (.of R)) (ULift.{u} (ZMod n)) a).hom.left) ≫
      (rootCoverMap R n hn hinv).hom.left = _
  rw [Category.assoc]
  exact congrArg (fun k => Scheme.LocalRing.residueSpecMap R ≫ k.left)
    (rootCoverMap_component R n hn hinv a)

/-- The split-cover map is bijective on the actual residue fibre. -/
theorem rootCoverMap_fiber_bijective :
    letI : NeZero n := ⟨hn.ne'⟩
    Function.Bijective
      ((fiberToFinite (Scheme.LocalRing.residueSpecMap R)).map (rootCoverMap R n hn hinv)) := by
  let : NeZero n := ⟨hn.ne'⟩
  let e := trivialCoverFiberEquiv (ULift.{u} (ZMod n)) (Scheme.LocalRing.residueSpecMap R)
  have he : Function.Bijective (fun a : ULift.{u} (ZMod n) =>
      rootSectionRestriction R n (globalRootCoordinates R n hn hinv a.down).toMul) :=
    (rootSectionRestriction_bijective R n hn hinv).comp
      (Additive.toMul.bijective.comp
        ((globalRootCoordinates R n hn hinv).bijective.comp Equiv.ulift.bijective))
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    apply congrArg e
    apply he.injective
    exact (rootCoverMap_fiber R n hn hinv a).symm.trans
      (hxy.trans (rootCoverMap_fiber R n hn hinv b))
  · intro y
    obtain ⟨a, ha⟩ := he.surjective y
    exact ⟨e a, (rootCoverMap_fiber R n hn hinv a).trans ha⟩

/-- The original root scheme is a constant finite cover, with its actual section map. -/
def rootCoverIso :
    letI : NeZero n := ⟨hn.ne'⟩
    trivialCover (Spec (.of R)) (ULift.{u} (ZMod n)) ≅ rootCover R n hn hinv := by
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsIso ((fiberToFinite (Scheme.LocalRing.residueSpecMap R)).map
      (rootCoverMap R n hn hinv)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (rootCoverMap_fiber_bijective R n hn hinv)
  letI : IsIso (rootCoverMap R n hn hinv) :=
    isIso_of_reflects_iso _ (fiberToFinite (Scheme.LocalRing.residueSpecMap R))
  exact asIso (rootCoverMap R n hn hinv)

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.HenselianConstant
