/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.ProjectiveLineTests
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEquivalence
public import Mathlib.Algebra.Group.Shrink

/-! # Original cohomology pullback under coefficient isomorphisms

The original coefficient naturality equation transports injectivity and
surjectivity separately. Finite values in the sheaf-value universe are
resized through the actual additive Shrink equivalence before applying the
accepted small-value strictly local projective-line tests. Auxiliary source
and fibre Ext models are supplied internally at the standard universe.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u eX eS

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}}
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{eS} (AbelianSheaf.{u, u + 1} S)]

/-- An actual coefficient isomorphism transports surjectivity of the
literal original cohomology pullback. -/
theorem cohomologyPullback_surjective_of_iso (g : S ⟶ X)
    {F G : AbelianSheaf.{u, u + 1} X} (e : F ≅ G) (q : ℕ)
    (hF : Function.Surjective (cohomologyPullback.{u, eX, eS} g F q)) :
    Function.Surjective (cohomologyPullback.{u, eX, eS} g G q) := by
  intro z
  obtain ⟨y, hy⟩ := (cohomologyMapIso_bijective ((inverseImage g).mapIso e) q).surjective z
  obtain ⟨x, hx⟩ := hF y
  refine ⟨Sheaf.H.map e.hom q x, ?_⟩
  rw [cohomologyPullback_coefficientMap, hx]
  exact hy

/-- The same original coefficient square transports injectivity without
any surjectivity premise on the pullback itself. -/
theorem cohomologyPullback_injective_of_iso (g : S ⟶ X)
    {F G : AbelianSheaf.{u, u + 1} X} (e : F ≅ G) (q : ℕ)
    (hF : Function.Injective (cohomologyPullback.{u, eX, eS} g F q)) :
    Function.Injective (cohomologyPullback.{u, eX, eS} g G q) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := (cohomologyMapIso_bijective e q).surjective x
  obtain ⟨b, rfl⟩ := (cohomologyMapIso_bijective e q).surjective y
  apply congrArg (Sheaf.H.map e.hom q)
  apply hF
  apply (cohomologyMapIso_bijective ((inverseImage g).mapIso e) q).injective
  change Sheaf.H.map ((inverseImage g).map e.hom) q (cohomologyPullback g F q a) =
    Sheaf.H.map ((inverseImage g).map e.hom) q (cohomologyPullback g F q b)
  exact ((cohomologyPullback_coefficientMap g e.hom q a).symm.trans hxy).trans
    (cohomologyPullback_coefficientMap g e.hom q b)

namespace Proper

private theorem exists_small_finiteConstantValueIso
    (A : AddCommGrpCat.{u + 1}) [Finite A] :
    ∃ (B : Type u) (_ : AddCommGroup B) (_ : Finite B),
      Nonempty (ConstantFinite.value B ≅ A) := by
  let := Fintype.ofFinite A
  have : Small.{u} A := Small.mk'
    ((Fintype.equivFin A).trans (Equiv.ulift.{u}).symm)
  let B := Shrink.{u} A
  have : Finite B := Finite.of_equiv A (equivShrink A)
  exact ⟨B, inferInstance, inferInstance,
    ⟨AddEquiv.toAddCommGrpIso (AddEquiv.ulift.trans (Shrink.addEquiv (α := A)))⟩⟩

section StrictlyLocal

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} (ProjectiveLine.projectiveP1 R))]
  [HasExt.{eS} (AbelianSheaf.{u, u + 1}
    (pullback (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)))]
  {Y : Scheme.{u}} (f : Y ⟶ ProjectiveLine.projectiveP1 R) [IsFinite f]

/-- Arbitrary finite values in the original sheaf-value universe satisfy
all-degree surjectivity on the same finite direct-image tests. -/
theorem finiteConstantDirectImage_residuePullback_surjective_of_finite_value
    [IsSepClosed (IsLocalRing.ResidueField R)]
    (A : AddCommGrpCat.{u + 1}) [Finite A] (q : ℕ) :
    Function.Surjective (cohomologyPullback.{u, eX, eS}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      ((directImage f).obj
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)) q) := by
  obtain ⟨B, _, _, ⟨e⟩⟩ := exists_small_finiteConstantValueIso A
  have : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Y) := hasExtStandard Y
  have : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} (Curves.residueFiber f)) :=
    hasExtStandard (Curves.residueFiber f)
  let eF := (directImage f).mapIso
    ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso e)
  exact cohomologyPullback_surjective_of_iso _ eF q
    (finiteConstantDirectImage_residuePullback_surjective.{u, u + 2, eX, u + 2, eS} f B q)

/-- Degree-zero injectivity holds for the same large finite values over
the arbitrary henselian local base, without a residue-field closure premise. -/
theorem finiteConstantDirectImage_residuePullback_injective_zero_of_finite_value
    (A : AddCommGrpCat.{u + 1}) [Finite A] :
    Function.Injective (cohomologyPullback.{u, eX, eS}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      ((directImage f).obj
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)) 0) := by
  obtain ⟨B, _, _, ⟨e⟩⟩ := exists_small_finiteConstantValueIso A
  have : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Y) := hasExtStandard Y
  have : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} (Curves.residueFiber f)) :=
    hasExtStandard (Curves.residueFiber f)
  let eF := (directImage f).mapIso
    ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso e)
  exact cohomologyPullback_injective_of_iso _ eF 0
    (finiteConstantDirectImage_residuePullback_injective_zero.{u, u + 2, eX, u + 2, eS} f B)

end StrictlyLocal

end Proper

end AlgebraicGeometry.Scheme.EtaleCohomology
