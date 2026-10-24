/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.IdentityComponent.FiniteType
public import Aglib.AlgebraicGeometry.Picard.GroupLaw

/-!
# The identity component of the Picard scheme over a field

Let `k` be a field and `p : X ⟶ Spec k` a morphism. Suppose that the fppf Picard sheaf
`Pic_{X/k,(fppf)}` (`fppfPicardSheaf p`), restricted to locally Noetherian test schemes, is
represented by `P` locally of finite type over `k`:

`e : (T ⟶ P) ≃ Pic_{X/k,(fppf)}(T)`, natural in locally Noetherian `k`-schemes `T`.

Then `P` is a commutative group scheme over `k` (`picardCommGrpObj p P e`,
`Aglib.AlgebraicGeometry.Picard.GroupLaw`), and its identity component, the connected component
of the identity `Pic⁰_{X/k}` (`AlgebraicGeometry.Scheme.RelativePicard.picardIdentityComponent`),
satisfies the following (Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Prop. 5.3, p. 37,
which Kleiman deduces from Prop. 4.17, p. 33 (local finite type, here a hypothesis), and the
group-scheme Lemma 5.1(3), pp. 36–37):

* it is an open and closed subset of `P` (`isClopen_picardIdentityComponent`) and a group
  subscheme (`grpObjPicardIdentityComponent`, `isMonHom_picardIdentityComponentι`);
* it is of finite type over `k` (`quasiCompact_picardIdentityComponent_hom` and
  `locallyOfFiniteType_picardIdentityComponent_hom`);
* it is geometrically irreducible (`geometricallyIrreducible_picardIdentityComponent_hom`);
* forming it commutes with extending `k`: for every field extension `K` of `k`, the identity
  component of the base change `P_K`, with the base-changed group law, is the preimage of `Pic⁰`
  (`picardIdentityComponent_pullback`), and `(Pic⁰)_K ≅ (P_K)⁰` as schemes
  (`pullbackPicardIdentityComponentIso`).

The representation `e` is an explicit argument; its existence (Kleiman, Thm 4.8, pp. 27–28) is not
proved here. The statement about `P_K` concerns the base change of the group scheme `P`; that
`P_K` represents `Pic_{X_K/K,(fppf)}` (Kleiman, Ex. 4.4, p. 27, Answer 4.4, pp. 65–66) is not used
or proved here. The separatedness and smoothness clauses of Prop. 5.3 are not treated.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.LocallyNoetherianOver Scheme.Group

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (e : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- **The identity component of the Picard scheme** `Pic⁰_{X/k}`: the identity component of the
scheme `P` representing `Pic_{X/k,(fppf)}`, for the group law `picardCommGrpObj p P e`, as a
scheme over `k`. -/
abbrev picardIdentityComponent : Over (Spec (.of k)) :=
  letI := picardCommGrpObj p P e
  identityComponentOver P.obj

/-- The inclusion `Pic⁰_{X/k} ⟶ P`, an open immersion. -/
abbrev picardIdentityComponentι : picardIdentityComponent p P e ⟶ P.obj :=
  letI := picardCommGrpObj p P e
  identityComponentι P.obj

/-- **`Pic⁰_{X/k}` is open and closed in `P`.** -/
theorem isClopen_picardIdentityComponent :
    letI := picardCommGrpObj p P e
    IsClopen (identityComponent P.obj : Set P.obj.left) :=
  letI := picardCommGrpObj p P e
  isClopen_identityComponent P.obj

/-- The inclusion of `Pic⁰_{X/k}` is an open immersion. -/
instance isOpenImmersion_picardIdentityComponentι :
    IsOpenImmersion (picardIdentityComponentι p P e).left :=
  letI := picardCommGrpObj p P e
  isOpenImmersion_identityComponentι_left P.obj

/-- **`Pic⁰_{X/k}` is a group scheme over `k`.** -/
instance grpObjPicardIdentityComponent : GrpObj (picardIdentityComponent p P e) :=
  letI := picardCommGrpObj p P e
  grpObjIdentityComponentOver P.obj

/-- **`Pic⁰_{X/k}` is a group subscheme of `P`**: its inclusion is a monoid morphism for the
group law `picardCommGrpObj p P e`. -/
theorem isMonHom_picardIdentityComponentι :
    letI := picardCommGrpObj p P e
    IsMonHom (picardIdentityComponentι p P e) :=
  letI := picardCommGrpObj p P e
  isMonHom_identityComponentι P.obj

/-- **`Pic⁰_{X/k}` is quasi-compact over `k`.** -/
instance quasiCompact_picardIdentityComponent_hom :
    QuasiCompact (picardIdentityComponent p P e).hom :=
  letI := picardCommGrpObj p P e
  quasiCompact_identityComponentOver_hom P.obj

/-- `Pic⁰_{X/k}` is locally of finite type over `k`. -/
instance locallyOfFiniteType_picardIdentityComponent_hom :
    LocallyOfFiniteType (picardIdentityComponent p P e).hom :=
  letI := picardCommGrpObj p P e
  locallyOfFiniteType_identityComponentOver_hom P.obj

/-- **`Pic⁰_{X/k}` is of finite type over `k`** (Kleiman, Prop. 5.3, p. 37). -/
theorem quasiCompact_and_locallyOfFiniteType_picardIdentityComponent :
    QuasiCompact (picardIdentityComponent p P e).hom ∧
      LocallyOfFiniteType (picardIdentityComponent p P e).hom :=
  ⟨inferInstance, inferInstance⟩

/-- **`Pic⁰_{X/k}` is geometrically irreducible** (Kleiman, Prop. 5.3, p. 37). -/
instance geometricallyIrreducible_picardIdentityComponent_hom :
    GeometricallyIrreducible (picardIdentityComponent p P e).hom :=
  letI := picardCommGrpObj p P e
  geometricallyIrreducible_identityComponentOver P.obj

/-- **The identity component of `P` commutes with extending `k`** (the group-scheme form of
Kleiman, Prop. 5.3, p. 37, "forming it commutes with extending k"): for a field extension `K`
of `k`, the identity component of the base change `P_K`, with the base-changed group law, is
the preimage of `Pic⁰_{X/k}`. That `P_K` represents `Pic_{X_K/K,(fppf)}` is not used. -/
theorem picardIdentityComponent_pullback (K : Type u) [Field K] [Algebra k K] :
    letI := picardCommGrpObj p P e
    identityComponent ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj P.obj) =
      pullback.fst P.obj.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⁻¹ᵁ
        identityComponent P.obj :=
  letI := picardCommGrpObj p P e
  identityComponent_pullback P.obj K

/-- **The base change of `Pic⁰_{X/k}` is the identity component of the base change**, as schemes:
`(Pic⁰_{X/k})_K ≅ (P_K)⁰`. -/
noncomputable def pullbackPicardIdentityComponentIso (K : Type u) [Field K] [Algebra k K] :
    letI := picardCommGrpObj p P e
    (pullback (picardIdentityComponent p P e).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) ≅
      (identityComponent
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj P.obj)).toScheme :=
  letI := picardCommGrpObj p P e
  pullbackIdentityComponentIso P.obj K

end AlgebraicGeometry.Scheme.RelativePicard
