/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Geometrically.Irreducible.FieldExtension
public import Aglib.AlgebraicGeometry.Group.IdentityComponent.BaseChange
public import Aglib.AlgebraicGeometry.Group.IdentityComponent.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# The identity component is geometrically irreducible and of finite type

Let `k` be a field and `G` a group scheme locally of finite type over `k`, that is
`G : Over (Spec k)` with a group object structure and `LocallyOfFiniteType G.hom`. Its identity
component `G⁰` (`AlgebraicGeometry.Scheme.Group.identityComponentOver G`) satisfies, over an
arbitrary field `k` (Stacks Project, Tag 0B7R(3), (4); Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Lemma 5.1(3), pp. 36–37):

* **`G⁰` is geometrically irreducible**
  (`AlgebraicGeometry.Scheme.Group.geometricallyIrreducible_identityComponentOver`), in particular
  irreducible (`irreducibleSpace_identityComponent`, `isIrreducible_identityComponent`);
* **`G⁰` is quasi-compact** (`compactSpace_identityComponent`, `isCompact_identityComponent`,
  and `quasiCompact_identityComponentOver_hom`);
* hence **`G⁰` is of finite type over `k`**
  (`quasiCompact_and_locallyOfFiniteType_identityComponentOver`) and is a Noetherian scheme
  (`isNoetherian_identityComponent`).

For an algebraically closed extension `K` of `k`, the base change `(G⁰)_K` is isomorphic to the
identity component `(G_K)⁰` of the base change (`pullbackIdentityComponentIso`), which is
irreducible and quasi-compact (`Aglib.AlgebraicGeometry.Group.IdentityComponent.Irreducible`,
`Aglib.AlgebraicGeometry.Group.IdentityComponent.QuasiCompact`). Geometric irreducibility follows
from `Scheme.Geometrically.geometricallyIrreducible_of_forall_isAlgClosed`, and quasi-compactness
descends along the surjection from the base change of `G⁰` to `AlgebraicClosure k`. Stacks 0B7R
deduces (3) from Tags 0B7Q and 047M, and (4) from Tag 0B7P; Kleiman deduces finite type from
quasi-compactness and local finite type.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.Scheme.Group

universe u

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom]

/-- **Over an algebraically closed extension field, the base change of `G⁰` is irreducible**:
`(G⁰)_K ≅ (G_K)⁰`, which is irreducible. -/
theorem irreducibleSpace_pullback_identityComponentOver_of_isAlgClosed (K : Type u) [Field K]
    [Algebra k K] [IsAlgClosed K] :
    IrreducibleSpace (pullback (identityComponentOver G).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) :=
  (pullbackIdentityComponentIso G K).hom.homeomorph.irreducibleSpace_iff.mpr
    (irreducibleSpace_identityComponent_of_isAlgClosed _)

/-- **The identity component is geometrically irreducible** (Stacks 0B7R(3); Kleiman,
Lemma 5.1(3), p. 37). -/
instance geometricallyIrreducible_identityComponentOver :
    GeometricallyIrreducible (identityComponentOver G).hom :=
  Scheme.Geometrically.geometricallyIrreducible_of_forall_isAlgClosed _ fun K _ _ _ =>
    irreducibleSpace_pullback_identityComponentOver_of_isAlgClosed G K

/-- **The identity component is irreducible**, as a scheme over `k`. -/
instance irreducibleSpace_identityComponentOver_left :
    IrreducibleSpace (identityComponentOver G).left :=
  GeometricallyIrreducible.irreducibleSpace_of_subsingleton (identityComponentOver G).hom

/-- The identity component is irreducible, as a scheme. -/
instance irreducibleSpace_identityComponent : IrreducibleSpace (identityComponent G).toScheme :=
  irreducibleSpace_identityComponentOver_left G

/-- **The identity component is an irreducible subset of `G`.** -/
theorem isIrreducible_identityComponent : IsIrreducible (identityComponent G : Set G.left) := by
  have h := (IrreducibleSpace.isIrreducible_univ (identityComponent G).toScheme).image
    (identityComponent G).ι (identityComponent G).ι.continuous.continuousOn
  rwa [Set.image_univ, Scheme.Opens.range_ι] at h

/-- **The identity component is quasi-compact** (Stacks 0B7R(4), 0B7P; Kleiman, Lemma 5.1(3),
p. 37): its base change to `AlgebraicClosure k` is the identity component of the base change of
`G`, which is quasi-compact, and it maps onto `G⁰`. -/
instance compactSpace_identityComponent : CompactSpace (identityComponent G).toScheme := by
  set b := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have : CompactSpace (identityComponent ((Over.pullback b).obj G)).toScheme :=
    compactSpace_identityComponent_of_isAlgClosed _
  have : CompactSpace (pullback (identityComponentOver G).hom b : Scheme.{u}) :=
    (Scheme.homeoOfIso (pullbackIdentityComponentIso G (AlgebraicClosure k)).symm).compactSpace
  have : Surjective b := ⟨Function.surjective_to_subsingleton _⟩
  exact Function.Surjective.compactSpace (pullback.fst (identityComponentOver G).hom b).continuous
    (pullback.fst (identityComponentOver G).hom b).surjective

/-- The identity component is quasi-compact, as a scheme over `k`. -/
instance compactSpace_identityComponentOver_left : CompactSpace (identityComponentOver G).left :=
  compactSpace_identityComponent G

/-- **The identity component is a quasi-compact subset of `G`.** -/
theorem isCompact_identityComponent : IsCompact (identityComponent G : Set G.left) := by
  have h := isCompact_range (identityComponent G).ι.continuous
  rwa [Scheme.Opens.range_ι] at h

/-- **The identity component is quasi-compact over `k`.** -/
instance quasiCompact_identityComponentOver_hom : QuasiCompact (identityComponentOver G).hom :=
  quasiCompact_of_compactSpace _

/-- **The identity component is of finite type over `k`** (Kleiman, Lemma 5.1(3), p. 37): it is
quasi-compact and locally of finite type. -/
theorem quasiCompact_and_locallyOfFiniteType_identityComponentOver :
    QuasiCompact (identityComponentOver G).hom ∧
      LocallyOfFiniteType (identityComponentOver G).hom :=
  ⟨inferInstance, inferInstance⟩

/-- **The identity component is a Noetherian scheme**: it is quasi-compact and locally
Noetherian. -/
instance isNoetherian_identityComponent : IsNoetherian (identityComponent G).toScheme :=
  have : IsLocallyNoetherian (identityComponentOver G).left :=
    LocallyOfFiniteType.isLocallyNoetherian (identityComponentOver G).hom
  { toIsLocallyNoetherian := this, toCompactSpace := compactSpace_identityComponent G }

end AlgebraicGeometry.Scheme.Group
