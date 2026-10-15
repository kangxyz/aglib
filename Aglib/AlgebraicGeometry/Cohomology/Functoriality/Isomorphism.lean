/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pullback
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/

/-!
# Actual scheme-isomorphism invariance of coherent cohomology

The canonical pullback maps are shown bijective using the induced equivalence
of actual Zariski sheaf categories and the actual structural sheaf isomorphism.
Original application provenance: K2-018#prop:k2018-arithmetic-characters, expose.tex lines 341–445,
mathematical source e73d98b1b5c1e5abcdebf7d058e436d792b87982;
engineering 7f86e4a1763cc4ec35e9b0a8acd659750355a0de with frozen pins.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.Isomorphism` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The equivalence of Zariski sheaves of abelian groups induced by the scheme isomorphism `e`. -/
def zariskiSheafEquivOfIso (e : X ≅ Y) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≌
      Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} := by
  let E := TopCat.Presheaf.presheafEquivOfIso AddCommGrpCat.{u} (Scheme.forgetToTop.mapIso e)
  letI : ObjectProperty.IsClosedUnderIsomorphisms
      (Presheaf.IsSheaf (Opens.grothendieckTopology Y) : ObjectProperty
        (Y.Opensᵒᵖ ⥤ AddCommGrpCat.{u})) :=
    ⟨fun e h ↦ (Presheaf.isSheaf_of_iso_iff e).mp h⟩
  apply E.congrFullSubcategory
  ext P
  constructor
  · intro h
    have h' : Presheaf.IsSheaf (Opens.grothendieckTopology X) (E.inverse.obj (E.functor.obj P)) :=
      TopCat.Sheaf.pushforward_sheaf_of_sheaf e.inv.base h
    exact (Presheaf.isSheaf_of_iso_iff (E.unitIso.app P)).mpr h'
  · intro h
    exact TopCat.Sheaf.pushforward_sheaf_of_sheaf e.hom.base h

instance zariskiPushforward_isEquivalence [IsIso f] : (zariskiPushforward f).IsEquivalence := by
  change (zariskiSheafEquivOfIso (asIso f)).functor.IsEquivalence
  infer_instance

instance zariskiPullback_isEquivalence [IsIso f] : (zariskiPullback f).IsEquivalence := by
  letI : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).IsEquivalence :=
    zariskiPushforward_isEquivalence f
  exact (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    f.base).isEquivalence_left_of_isEquivalence_right

instance structurePushforwardMap_isIso [IsIso f] : IsIso (structurePushforwardMap f) := by
  letI : IsIso f.c := PresheafedSpace.c_isIso_of_iso f.toPshHom
  letI : IsIso ((sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).map
      (structurePushforwardMap f)) := by
    change IsIso (Functor.whiskerRight f.c _)
    infer_instance
  exact isIso_of_reflects_iso _ (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})

instance structurePullbackMap_isIso [IsIso f] : IsIso (structurePullbackMap f) := by
  letI : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).IsEquivalence :=
    zariskiPushforward_isEquivalence f
  letI : IsIso (structurePushforwardMap f) := structurePushforwardMap_isIso f
  dsimp only [structurePullbackMap]
  rw [Adjunction.homEquiv_counit]
  infer_instance

/-- The canonical cohomology map is bijective for a scheme isomorphism and
an actual isomorphism of the pulled-back coefficient sheaves. -/
theorem zariskiCohomologyMap_bijective [IsIso f]
    (A : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (a : (zariskiPullback f).obj A ⟶ B) [IsIso a] (n : ℕ) :
    Function.Bijective (zariskiCohomologyMap f A B a n) := by
  let U := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let V := (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let c : U ⟶ (zariskiPullback f).obj V :=
    (constantPullbackIso f).inv.app (AddCommGrpCat.of (ULift.{u} ℤ))
  letI : IsIso c := by dsimp [c]; infer_instance
  have hmap : Function.Bijective ((zariskiPullback f).mapExtAddHom V A n) :=
    (zariskiPullback f).mapExt_bijective_of_preservesInjectiveObjects V A n
  have hpre : Function.Bijective ((Abelian.Ext.mk₀ c).precomp
      ((zariskiPullback f).obj A) (Nat.zero_add n)) :=
    ConcreteCategory.bijective_of_isIso
      (((Abelian.extFunctor.{u + 1} n).map c.op).app ((zariskiPullback f).obj A))
  have hpost : Function.Bijective ((Abelian.Ext.mk₀ a).postcomp U (Nat.add_zero n)) :=
    ConcreteCategory.bijective_of_isIso ((Abelian.extFunctorObj.{u + 1} U n).map a)
  exact hpost.comp (hpre.comp hmap)

/-- Bijectivity of the actual structural cohomology pullback for scheme isomorphisms. -/
theorem structureCohomologyPullback_bijective [IsIso f] (n : ℕ) :
    Function.Bijective (structureCohomologyPullback f n) :=
  zariskiCohomologyMap_bijective f _ _ (structurePullbackMap f) n
end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.OverField
universe u
variable {F : Type u} [Field F] {X Y : FScheme F}
/-- The linear equivalence is the actual contravariant map induced by the
F-scheme isomorphism; no equivalence of arbitrary vector spaces is supplied. -/
def structureCohomologyIso (e : X ≅ Y) (n : ℕ) :
    structureCohomology F Y n ≃ₗ[F] structureCohomology F X n :=
  LinearEquiv.ofBijective (structureCohomologyPullbackLinear e.hom n)
    (structureCohomologyPullback_bijective e.hom.left n)
end AlgebraicGeometry.Scheme.Cohomology
