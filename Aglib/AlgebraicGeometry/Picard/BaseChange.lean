/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.FamilyBaseChange
public import Aglib.AlgebraicGeometry.Picard.Fppf
public import Aglib.CategoryTheory.Sites.OverMapCovering
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Base change of the fppf Picard sheaf

Let `p : X ⟶ S` and `g : S' ⟶ S` be morphisms of schemes, and put
`p' := pullback.snd p g : X ×_S S' ⟶ S'`. An `S'`-scheme `T` is an `S`-scheme through
`T ⟶ S' ⟶ S` (`Over.map g`). Then

`Pic_{X'/S',(fppf)}(T) ≅ Pic_{X/S,(fppf)}(T)`,

naturally in the `S'`-scheme `T`: `fppfPicardSheafBaseChangeIso p g` is an isomorphism of
presheaves of abelian groups on `Over S'`
`(fppfPicardSheaf p').obj ≅ (Over.map g).op ⋙ (fppfPicardSheaf p).obj`, and
`fppfPicardSheafBaseChangeSheafIso p g` is the same isomorphism of fppf sheaves, with target the
restriction `Functor.sheafPushforwardContinuous` along `Over.map g`. This is Kleiman's base change
of the Picard functor (Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Ex. 4.4, p. 27, and
Answer 4.4, p. 65), for the fppf sheafification on the big sites.

The isomorphism is compatible with the sheafification units: the unit of `p'` followed by the
isomorphism is the base change of the relative Picard presheaves followed by the unit of `p`
(`toFppfPicardSheaf_comp_fppfPicardSheafBaseChangeIso_hom`), and on the family Picard presheaves
(`quotientProjection_comp_toFppfPicardSheaf_comp_fppfPicardSheafBaseChangeIso_hom`). On the
class of a line bundle `L` on `(X ×_S S') ×_{S'} T`, the isomorphism gives the class of the pullback
of `L` to `X ×_S T` (`fppfPicardSheafBaseChangeIso_hom_app_toFppfPicardSheaf_mk`).

Naturality in `T` is `fppfPicardSheafBaseChangeIso_hom_naturality`, on elements
`fppfPicardSheafBaseChangeIso_hom_app_map_apply`. For a morphism `i : T₀ ⟶ T` of `S'`-schemes, the
isomorphism at `T` identifies the kernels of the restrictions along `i` and along
`(Over.map g).map i` (`fppfPicardSheafBaseChangeKerAddEquiv`); for a field `K` over `S'`,
`T = Spec K[ε]` and `T₀ = Spec K`, these are the tangent spaces at the origin.

## Route

1. At the presheaf level, `familyPicardFunctorBaseChangeIso p g` identifies Kleiman's absolute
   functors `T ↦ Pic((X ×_S S') ×_{S'} T)` and `T ↦ Pic(X ×_S T)`, and it carries the image of
   `Pic(T)` onto the image of `Pic(T)`; hence it induces `relativePicardFunctorBaseChangeIso p g`
   on the relative Picard functors `T ↦ Pic(X_T) / Pic(T)`.
2. Fppf sheafification commutes with the restriction along `Over.map g`: Mathlib's
   `Functor.pushforwardContinuousSheafificationCompatibility`. Its hypotheses are that
   `Over.map g` is continuous and cocontinuous for `Scheme.fppfTopology.over S'` and
   `Scheme.fppfTopology.over S` (Mathlib instances), that right Kan extensions along
   `(Over.map g).op` exist pointwise for presheaves with values in `AddCommGrpCat.{u + 1}`, and
   that both sheafifications exist; the last two are found by instance search. The covering
   conditions behind this continuity and cocontinuity are the correspondence of coverings
   `fppf_functorPushforward_over_map_mem_iff` (with its preimage form
   `GrothendieckTopology.functorPullback_over_map_mem_iff`): a family of `S'`-schemes covers if
   and only if it covers as a family of `S`-schemes. Kleiman's identification of the sheafified
   functors, which "holds essentially by definition", rests on this correspondence (Answer 4.4,
   p. 65, for étale coverings).
3. The fppf sheafifications of the absolute and relative functors agree
   (`fppfFamilyPicardSheafIso`), for `p` and for `p'`.

No hypothesis on `p`, `g` or the test schemes is used. Kleiman's Answer 4.4 treats the étale
functor and states that a similar analysis applies to the others; the argument here is the fppf
case.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible

universe u

variable {S S' X : Scheme.{u}} (p : X ⟶ S) (g : S' ⟶ S)

/-- **Fppf coverings along `Over.map g`**: a sieve on an `S'`-scheme `T` is an fppf covering of
`T` over `S'` if and only if its image under `Over.map g` is an fppf covering of `T` over `S`.
This is the reason Kleiman gives for the identification of the sheafified Picard functors, which
"holds essentially by definition, since a map of S′-schemes is an étale-covering if and only if
it is an étale-covering when viewed as a map of S-schemes" (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Answer 4.4, p. 65); here for fppf coverings. -/
theorem fppf_functorPushforward_over_map_mem_iff {T : Over S'} (R : Sieve T) :
    R.functorPushforward (Over.map g) ∈ Scheme.fppfTopology.over S ((Over.map g).obj T) ↔
      R ∈ Scheme.fppfTopology.over S' T :=
  Scheme.fppfTopology.functorPushforward_over_map_mem_iff g R

/-- The base-change isomorphism of the family Picard presheaves carries the image of `Pic(T)`
in `Pic((X ×_S S') ×_{S'} T)` onto the image of `Pic(T)` in `Pic(X ×_S T)`. -/
theorem baseImage_map_familyPicardFunctorBaseChangeIso_hom_app (T : (Over S')ᵒᵖ) :
    (baseImage (pullback.snd p g) T).map
        ((familyPicardFunctorBaseChangeIso p g).app T).addCommGroupIsoToAddEquiv.toAddMonoidHom =
      baseImage p (op ((Over.map g).obj T.unop)) := by
  rw [AddMonoidHom.map_range]
  congr 1
  ext a
  exact congrArg (fun φ => φ.hom a)
    (basePullback_app_comp_familyPicardFunctorBaseChangeIso_hom_app p g T)

/-- **Base change of the relative Picard functor**: for an `S'`-scheme `T`,
`Pic((X ×_S S') ×_{S'} T) / Pic(T) ≅ Pic(X ×_S T) / Pic(T)`, naturally in `T`, induced by
`familyPicardFunctorBaseChangeIso p g` (Kleiman, *The Picard scheme*, arXiv:math/0504020v1,
Ex. 4.4, p. 27, and Answer 4.4, p. 65, at the presheaf level). -/
def relativePicardFunctorBaseChangeIso :
    relativePicardFunctor (pullback.snd p g) ≅ (Over.map g).op ⋙ relativePicardFunctor p :=
  NatIso.ofComponents
    (fun T => AddEquiv.toAddCommGrpIso
      (QuotientAddGroup.congr (baseImage (pullback.snd p g) T)
        (baseImage p (op ((Over.map g).obj T.unop)))
        ((familyPicardFunctorBaseChangeIso p g).app T).addCommGroupIsoToAddEquiv
        (baseImage_map_familyPicardFunctorBaseChangeIso_hom_app p g T)))
    (fun {T T'} f => by
      ext a
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
      exact congrArg QuotientAddGroup.mk
        (congrArg (fun φ => φ.hom a) ((familyPicardFunctorBaseChangeIso p g).hom.naturality f)))

/-- The base change of the relative Picard functors lifts that of the family Picard functors
through the quotient maps. -/
@[reassoc]
theorem quotientProjection_comp_relativePicardFunctorBaseChangeIso_hom :
    quotientProjection (pullback.snd p g) ≫ (relativePicardFunctorBaseChangeIso p g).hom =
      (familyPicardFunctorBaseChangeIso p g).hom ≫
        Functor.whiskerLeft (Over.map g).op (quotientProjection p) := by
  ext T a
  rfl

theorem relativePicardFunctorBaseChangeIso_hom_app_mk (T : (Over S')ᵒᵖ)
    (a : (familyPicardFunctor (pullback.snd p g)).obj T) :
    ((relativePicardFunctorBaseChangeIso p g).hom.app T).hom (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk (((familyPicardFunctorBaseChangeIso p g).hom.app T).hom a) :=
  rfl

/-- **Base change of the fppf Picard sheaf, as fppf sheaves**:
`Pic_{X'/S',(fppf)} ≅ (Over.map g)^* Pic_{X/S,(fppf)}` in sheaves on `Over S'`, where
`X' = X ×_S S'` and `(Over.map g)^*` is the restriction `Functor.sheafPushforwardContinuous` along
`Over.map g`. It is the fppf sheafification of `familyPicardFunctorBaseChangeIso p g`, followed by
Mathlib's compatibility of sheafification with this restriction
(`Functor.pushforwardContinuousSheafificationCompatibility`), between the identifications
`fppfFamilyPicardSheafIso` of the fppf sheafifications of the absolute and relative functors. -/
def fppfPicardSheafBaseChangeSheafIso :
    fppfPicardSheaf (pullback.snd p g) ≅
      ((Over.map g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).obj (fppfPicardSheaf p) :=
  (fppfFamilyPicardSheafIso (pullback.snd p g)).symm ≪≫
    (presheafToSheaf (Scheme.fppfTopology.over S') AddCommGrpCat.{u + 1}).mapIso
      (familyPicardFunctorBaseChangeIso p g) ≪≫
    ((Over.map g).pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u + 1}
      (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).app (familyPicardFunctor p) ≪≫
    ((Over.map g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).mapIso
      (fppfFamilyPicardSheafIso p)

/-- **Base change of the fppf Picard sheaf** (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Ex. 4.4, p. 27, and Answer 4.4, p. 65): for `X' = X ×_S S'`,
`Pic_{X'/S',(fppf)}(T) ≅ Pic_{X/S,(fppf)}(T)` naturally in the `S'`-scheme `T`, where on the right
`T` is an `S`-scheme through `T ⟶ S' ⟶ S`. -/
def fppfPicardSheafBaseChangeIso :
    (fppfPicardSheaf (pullback.snd p g)).obj ≅ (Over.map g).op ⋙ (fppfPicardSheaf p).obj :=
  (sheafToPresheaf (Scheme.fppfTopology.over S') AddCommGrpCat.{u + 1}).mapIso
    (fppfPicardSheafBaseChangeSheafIso p g)

theorem fppfPicardSheafBaseChangeIso_hom :
    (fppfPicardSheafBaseChangeIso p g).hom = (fppfPicardSheafBaseChangeSheafIso p g).hom.hom :=
  rfl

/-- Naturality of `fppfPicardSheafBaseChangeIso p g` in the `S'`-scheme `T`. -/
@[reassoc]
theorem fppfPicardSheafBaseChangeIso_hom_naturality {T T' : (Over S')ᵒᵖ} (f : T ⟶ T') :
    (fppfPicardSheaf (pullback.snd p g)).obj.map f ≫ (fppfPicardSheafBaseChangeIso p g).hom.app T' =
      (fppfPicardSheafBaseChangeIso p g).hom.app T ≫
        (fppfPicardSheaf p).obj.map ((Over.map g).op.map f) :=
  (fppfPicardSheafBaseChangeIso p g).hom.naturality f

/-- Naturality of `fppfPicardSheafBaseChangeIso p g` on elements: for `i : T₀ ⟶ T` of
`S'`-schemes, restricting along `i` and then changing the base is changing the base and then
restricting along `i` viewed over `S`. -/
theorem fppfPicardSheafBaseChangeIso_hom_app_map_apply {T₀ T : Over S'} (i : T₀ ⟶ T)
    (x : (fppfPicardSheaf (pullback.snd p g)).obj.obj (op T)) :
    ((fppfPicardSheafBaseChangeIso p g).hom.app (op T₀)).hom
        (((fppfPicardSheaf (pullback.snd p g)).obj.map i.op).hom x) =
      ((fppfPicardSheaf p).obj.map ((Over.map g).map i).op).hom
        (((fppfPicardSheafBaseChangeIso p g).hom.app (op T)).hom x) :=
  congrArg (fun φ => φ.hom x) (fppfPicardSheafBaseChangeIso_hom_naturality p g i.op)

theorem fppfPicardSheafBaseChangeIso_hom_app_inv_app_apply {T : Over S'}
    (y : (fppfPicardSheaf p).obj.obj (op ((Over.map g).obj T))) :
    ((fppfPicardSheafBaseChangeIso p g).hom.app (op T)).hom
        (((fppfPicardSheafBaseChangeIso p g).inv.app (op T)).hom y) = y :=
  congrArg (fun φ => φ.hom y) ((fppfPicardSheafBaseChangeIso p g).inv_hom_id_app (op T))

/-- **Kernels of restriction maps under base change**: for a morphism `i : T₀ ⟶ T` of
`S'`-schemes, `fppfPicardSheafBaseChangeIso p g` at `T` restricts to an isomorphism from the
kernel of `Pic_{X'/S',(fppf)}(T) → Pic_{X'/S',(fppf)}(T₀)` onto the kernel of
`Pic_{X/S,(fppf)}(T) → Pic_{X/S,(fppf)}(T₀)`, where `T₀ ⟶ T` is viewed over `S`. For a field `K`
over `S'`, `T = Spec K[ε]` and `T₀ = Spec K` its closed point, these kernels are the tangent
spaces at the origin. -/
def fppfPicardSheafBaseChangeKerAddEquiv {T₀ T : Over S'} (i : T₀ ⟶ T) :
    ((fppfPicardSheaf (pullback.snd p g)).obj.map i.op).hom.ker ≃+
      ((fppfPicardSheaf p).obj.map ((Over.map g).map i).op).hom.ker where
  toFun x := ⟨((fppfPicardSheafBaseChangeIso p g).hom.app (op T)).hom x.1, by
    rw [AddMonoidHom.mem_ker, ← fppfPicardSheafBaseChangeIso_hom_app_map_apply,
      AddMonoidHom.mem_ker.mp x.2, map_zero]⟩
  invFun y := ⟨((fppfPicardSheafBaseChangeIso p g).inv.app (op T)).hom y.1, by
    rw [AddMonoidHom.mem_ker]
    apply ((fppfPicardSheafBaseChangeIso p g).app (op T₀)).addCommGroupIsoToAddEquiv.injective
    change ((fppfPicardSheafBaseChangeIso p g).hom.app (op T₀)).hom _ =
      ((fppfPicardSheafBaseChangeIso p g).hom.app (op T₀)).hom 0
    rw [fppfPicardSheafBaseChangeIso_hom_app_map_apply, map_zero,
      fppfPicardSheafBaseChangeIso_hom_app_inv_app_apply]
    exact AddMonoidHom.mem_ker.mp y.2⟩
  left_inv x := Subtype.ext
    (congrArg (fun φ => φ.hom x.1) ((fppfPicardSheafBaseChangeIso p g).hom_inv_id_app (op T)))
  right_inv y := Subtype.ext (fppfPicardSheafBaseChangeIso_hom_app_inv_app_apply p g y.1)
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)

theorem fppfPicardSheafBaseChangeKerAddEquiv_apply_coe {T₀ T : Over S'} (i : T₀ ⟶ T)
    (x : ((fppfPicardSheaf (pullback.snd p g)).obj.map i.op).hom.ker) :
    (fppfPicardSheafBaseChangeKerAddEquiv p g i x : (fppfPicardSheaf p).obj.obj
        (op ((Over.map g).obj T))) =
      ((fppfPicardSheafBaseChangeIso p g).hom.app (op T)).hom x :=
  rfl

/-- **Compatibility with the units, on the family Picard presheaves**: the class of a line bundle
on `(X ×_S S') ×_{S'} T` in `Pic_{X'/S',(fppf)}(T)`, carried to `Pic_{X/S,(fppf)}(T)`, is the class
of its pullback to `X ×_S T`. -/
@[reassoc]
theorem quotientProjection_comp_toFppfPicardSheaf_comp_fppfPicardSheafBaseChangeIso_hom :
    quotientProjection (pullback.snd p g) ≫ toFppfPicardSheaf (pullback.snd p g) ≫
        (fppfPicardSheafBaseChangeIso p g).hom =
      (familyPicardFunctorBaseChangeIso p g).hom ≫
        Functor.whiskerLeft (Over.map g).op (quotientProjection p ≫ toFppfPicardSheaf p) := by
  have e₁ : quotientProjection (pullback.snd p g) ≫ toFppfPicardSheaf (pullback.snd p g) =
      toSheafify (Scheme.fppfTopology.over S') (familyPicardFunctor (pullback.snd p g)) ≫
        (fppfFamilyPicardSheafIso (pullback.snd p g)).hom.hom :=
    toSheafify_naturality (Scheme.fppfTopology.over S') (quotientProjection (pullback.snd p g))
  have e₂ : toSheafify (Scheme.fppfTopology.over S') (familyPicardFunctor (pullback.snd p g)) ≫
      ((presheafToSheaf (Scheme.fppfTopology.over S') AddCommGrpCat.{u + 1}).map
        (familyPicardFunctorBaseChangeIso p g).hom).hom =
      (familyPicardFunctorBaseChangeIso p g).hom ≫
        toSheafify (Scheme.fppfTopology.over S') ((Over.map g).op ⋙ familyPicardFunctor p) :=
    (toSheafify_naturality (Scheme.fppfTopology.over S')
      (familyPicardFunctorBaseChangeIso p g).hom).symm
  have e₃ := (Over.map g).toSheafify_pullbackSheafificationCompatibility AddCommGrpCat.{u + 1}
    (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S) (familyPicardFunctor p)
  have e₄ : toSheafify (Scheme.fppfTopology.over S) (familyPicardFunctor p) ≫
      (fppfFamilyPicardSheafIso p).hom.hom = quotientProjection p ≫ toFppfPicardSheaf p :=
    (toSheafify_naturality (Scheme.fppfTopology.over S) (quotientProjection p)).symm
  change quotientProjection (pullback.snd p g) ≫ toFppfPicardSheaf (pullback.snd p g) ≫
      (fppfFamilyPicardSheafIso (pullback.snd p g)).inv.hom ≫
        ((presheafToSheaf (Scheme.fppfTopology.over S') AddCommGrpCat.{u + 1}).map
          (familyPicardFunctorBaseChangeIso p g).hom).hom ≫
        (((Over.map g).pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u + 1}
          (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).hom.app
            (familyPicardFunctor p)).hom ≫
        (((Over.map g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).map
            (fppfFamilyPicardSheafIso p).hom).hom = _
  rw [reassoc_of% e₁, ObjectProperty.isoHom_inv_id_hom_assoc, reassoc_of% e₂]
  -- the restriction along `Over.map g` of a morphism of sheaves is its whiskering by
  -- `(Over.map g).op`; the last two steps are definitional on that whiskering
  exact congrArg ((familyPicardFunctorBaseChangeIso p g).hom ≫ ·)
    (((reassoc_of% e₃) _).trans (congrArg (Functor.whiskerLeft (Over.map g).op) e₄))

/-- **Compatibility with the units**: the sheafification unit of `p'` followed by
`fppfPicardSheafBaseChangeIso p g` is the base change of the relative Picard functors followed by
the unit of `p`, restricted along `Over.map g`. -/
@[reassoc]
theorem toFppfPicardSheaf_comp_fppfPicardSheafBaseChangeIso_hom :
    toFppfPicardSheaf (pullback.snd p g) ≫ (fppfPicardSheafBaseChangeIso p g).hom =
      (relativePicardFunctorBaseChangeIso p g).hom ≫
        Functor.whiskerLeft (Over.map g).op (toFppfPicardSheaf p) := by
  ext T a
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
  exact congrArg (fun φ => (φ.app T).hom a)
    (quotientProjection_comp_toFppfPicardSheaf_comp_fppfPicardSheafBaseChangeIso_hom p g)

/-- **The class of a line bundle under base change**: for a line bundle `L` on
`(X ×_S S') ×_{S'} T`, the isomorphism sends the class of `L` in `Pic_{X'/S',(fppf)}(T)` to the
class in `Pic_{X/S,(fppf)}(T)` of its pullback along `X ×_S T ≅ (X ×_S S') ×_{S'} T`. -/
theorem fppfPicardSheafBaseChangeIso_hom_app_toFppfPicardSheaf_mk (T : (Over S')ᵒᵖ)
    (a : (familyPicardFunctor (pullback.snd p g)).obj T) :
    ((fppfPicardSheafBaseChangeIso p g).hom.app T).hom
        (((toFppfPicardSheaf (pullback.snd p g)).app T).hom (QuotientAddGroup.mk a)) =
      ((toFppfPicardSheaf p).app (op ((Over.map g).obj T.unop))).hom
        (QuotientAddGroup.mk (pullbackClass (familyBaseChangeIso p g T.unop).inv a)) :=
  congrArg (fun φ => (φ.app T).hom a)
    (quotientProjection_comp_toFppfPicardSheaf_comp_fppfPicardSheafBaseChangeIso_hom p g)

end AlgebraicGeometry.Scheme.RelativePicard
