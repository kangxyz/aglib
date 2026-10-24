/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Presheaf

/-!
# Base change of the family Picard presheaf

Let `p : X ⟶ S` and `g : S' ⟶ S` be morphisms of schemes, and put
`p' := pullback.snd p g : X ×_S S' ⟶ S'`. For a scheme `T` over `S'`, the family of `p'` over `T`
is `(X ×_S S') ×_{S'} T`; the family of `p` over `T`, viewed over `S` through `T ⟶ S' ⟶ S`
(`Over.map g`), is `X ×_S T`. Pasting the two pullback squares (Mathlib's
`pullbackLeftPullbackSndIso`) identifies them, naturally in `T`:

* `familyBaseChangeIso p g T : (X ×_S S') ×_{S'} T ≅ X ×_S T`, between the literal fibre
  products `pullback (pullback.snd p g) T.hom` and `pullback p (T.hom ≫ g)`; it commutes with the
  projections to `X` and to `T`;
* `familySchemeBaseChangeIso p g : familyScheme p' ≅ Over.map g ⋙ familyScheme p`;
* `familyPicardFunctorBaseChangeIso p g :
    familyPicardFunctor p' ≅ (Over.map g).op ⋙ familyPicardFunctor p`,
  pullback of line-bundle classes along the inverses of these isomorphisms, so that
  `Pic((X ×_S S') ×_{S'} T) ≅ Pic(X ×_S T)` naturally in `T`;
* compatibility with the base pullbacks: `basePullback p'` followed by this isomorphism is
  `basePullback p` at `T ⟶ S' ⟶ S`
  (`basePullback_app_comp_familyPicardFunctorBaseChangeIso_hom_app`,
  `basePullback_comp_familyPicardFunctorBaseChangeIso_hom`), because the two projections to `T`
  correspond.

This is the presheaf level of the base change of the Picard functor (Kleiman, *The Picard
scheme*, arXiv:math/0504020v1, Ex. 4.4, p. 27, and Answer 4.4, p. 65). Kleiman's identification
of the sheafified functors on `S'`-schemes `T`, which "holds essentially by definition", also
uses that coverings of `S'`-schemes are those of the underlying `S`-schemes; that step is not
done here. No hypothesis on `p`, `g` or the test schemes is used. The maps are typed between the
literal fibre products, as for the base-change maps of linear systems (`docs/PERFORMANCE.md`,
linear-system family maps).
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local

universe u

variable {S S' X : Scheme.{u}} (p : X ⟶ S) (g : S' ⟶ S)

/-- **The base-change comparison of the families**: for a scheme `T` over `S'`,
`(X ×_S S') ×_{S'} T ≅ X ×_S T`, between the literal fibre products, by pasting of pullback
squares. -/
def familyBaseChangeIso (T : Over S') :
    Limits.pullback (pullback.snd p g) T.hom ≅ Limits.pullback p (T.hom ≫ g) :=
  pullbackLeftPullbackSndIso p g T.hom

@[reassoc (attr := simp)]
theorem familyBaseChangeIso_hom_fst (T : Over S') :
    (familyBaseChangeIso p g T).hom ≫ pullback.fst p (T.hom ≫ g) =
      pullback.fst (pullback.snd p g) T.hom ≫ pullback.fst p g :=
  pullbackLeftPullbackSndIso_hom_fst p g T.hom

@[reassoc (attr := simp)]
theorem familyBaseChangeIso_hom_snd (T : Over S') :
    (familyBaseChangeIso p g T).hom ≫ pullback.snd p (T.hom ≫ g) =
      pullback.snd (pullback.snd p g) T.hom :=
  pullbackLeftPullbackSndIso_hom_snd p g T.hom

@[reassoc (attr := simp)]
theorem familyBaseChangeIso_inv_snd (T : Over S') :
    (familyBaseChangeIso p g T).inv ≫ pullback.snd (pullback.snd p g) T.hom =
      pullback.snd p (T.hom ≫ g) :=
  pullbackLeftPullbackSndIso_inv_snd_snd p g T.hom

-- `pullback.map` and the pasted pullback carry their own `HasPullback` instances; relaxing
-- instance transparency lets the projection lemmas match them, as in `Picard/Presheaf`.
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of `familyBaseChangeIso` in `T`, against the family maps `pullback.map`. -/
@[reassoc]
theorem familyBaseChangeIso_hom_naturality {T T' : Over S'} (f : T ⟶ T') :
    (familyScheme (pullback.snd p g)).map f ≫ (familyBaseChangeIso p g T').hom =
      (familyBaseChangeIso p g T).hom ≫ (familyScheme p).map ((Over.map g).map f) := by
  apply pullback.hom_ext
  · simp [familyScheme_map, pullback.map]
  · simp [familyScheme_map, pullback.map]

/-- **Base change of the family**: `familyScheme (pullback.snd p g) ≅ Over.map g ⋙ familyScheme p`,
with components `familyBaseChangeIso p g T`. -/
def familySchemeBaseChangeIso : familyScheme (pullback.snd p g) ≅ Over.map g ⋙ familyScheme p :=
  NatIso.ofComponents (familyBaseChangeIso p g) (familyBaseChangeIso_hom_naturality p g)

theorem familySchemeBaseChangeIso_app (T : Over S') :
    (familySchemeBaseChangeIso p g).app T = familyBaseChangeIso p g T :=
  rfl

/-- **Base change of the family Picard presheaf** (Kleiman's absolute functor
`T ↦ Pic(X ×_S T)`): `Pic((X ×_S S') ×_{S'} T) ≅ Pic(X ×_S T)`, naturally in the `S'`-scheme `T`,
by pullback of line-bundle classes along `(familyBaseChangeIso p g T).inv`. -/
def familyPicardFunctorBaseChangeIso :
    familyPicardFunctor (pullback.snd p g) ≅ (Over.map g).op ⋙ familyPicardFunctor p :=
  Functor.isoWhiskerRight (NatIso.op (familySchemeBaseChangeIso p g).symm) picardFunctor

theorem familyPicardFunctorBaseChangeIso_hom_app_apply (T : (Over S')ᵒᵖ)
    (a : PicardGroup (Limits.pullback (pullback.snd p g) T.unop.hom)) :
    ((familyPicardFunctorBaseChangeIso p g).hom.app T).hom a =
      pullbackClass (familyBaseChangeIso p g T.unop).inv a :=
  rfl

theorem familyPicardFunctorBaseChangeIso_inv_app_apply (T : (Over S')ᵒᵖ)
    (a : PicardGroup (Limits.pullback p (T.unop.hom ≫ g))) :
    ((familyPicardFunctorBaseChangeIso p g).inv.app T).hom a =
      pullbackClass (familyBaseChangeIso p g T.unop).hom a :=
  rfl

/-- **Compatibility with the base pullbacks**, at each `S'`-scheme `T`: pulling a class on `T`
back to `(X ×_S S') ×_{S'} T` and then to `X ×_S T` is pulling it back along `X ×_S T ⟶ T`. -/
theorem basePullback_app_comp_familyPicardFunctorBaseChangeIso_hom_app (T : (Over S')ᵒᵖ) :
    (basePullback (pullback.snd p g)).app T ≫ (familyPicardFunctorBaseChangeIso p g).hom.app T =
      (basePullback p).app (op ((Over.map g).obj T.unop)) := by
  ext a
  exact (pullbackClass_comp _ _ a).symm.trans
    (congrArg (fun φ => pullbackClass φ a) (familyBaseChangeIso_inv_snd p g T.unop))

/-- **Compatibility with the base pullbacks**, as natural transformations:
`basePullback (pullback.snd p g)` followed by `familyPicardFunctorBaseChangeIso p g` is
`basePullback p` restricted along `Over.map g`. -/
theorem basePullback_comp_familyPicardFunctorBaseChangeIso_hom :
    basePullback (pullback.snd p g) ≫ (familyPicardFunctorBaseChangeIso p g).hom =
      Functor.whiskerLeft (Over.map g).op (basePullback p) := by
  ext T : 2
  exact basePullback_app_comp_familyPicardFunctorBaseChangeIso_hom_app p g T

end AlgebraicGeometry.Scheme.RelativePicard
