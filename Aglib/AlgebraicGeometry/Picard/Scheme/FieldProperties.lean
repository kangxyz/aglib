/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.BaseChangeGroupLaw
public import Aglib.AlgebraicGeometry.Picard.IdentityComponent
public import Aglib.AlgebraicGeometry.Picard.Representability.FineStrata
public import Aglib.AlgebraicGeometry.Picard.Tangent.StructureCohomology

/-!
# The Picard scheme over a field: tangent space and identity component

Let `k` be a field, `i : X ⟶ P^N_k = ProjectiveSpace k ι` a closed immersion with
`ι ≃ Fin (N + 1)`, such that `p = i ≫ toSpec k ι` is flat with geometrically integral fibres, and
let `P = picardScheme h` with `R = picardSchemeRepresentableBy h` be the Picard scheme of
Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Thm 4.8, pp. 27–31 (target 5 of
`docs/PICARD_PLAN.md`), for any proof `h` of the fine-strata premise, which always holds
(`Strata.fineStrataRepresentableByHQuasiProjective i e`). It represents `Pic_{X/k,(fppf)}` on
locally Noetherian test schemes, and `picardCommGrpObj p P R` is its group law
([GroupLaw](../GroupLaw.lean)). This file instantiates the results over a field at `P`, with
no further hypothesis.

* **Properness** (`ProjectiveSpace.isProper_comp_toSpec_of_isClosedImmersion`, over any ring): `p`
  is proper, since `i` is a closed immersion and `P^N_A ⟶ Spec A` is proper for finitely many
  coordinates. With it, `X` is the scheme `Over.mk p` over `k` (an `FScheme k`, whose structure
  morphism is `p` by definition) to which [StructureCohomology](../Tangent/StructureCohomology.lean)
  applies.
* **The tangent space at the unit** (Kleiman, Thm 5.11, p. 42: `T_0 Pic_{X/k} = H^1(𝒪_X)`):
  `picardSchemeTangentKernelLinearEquiv h : ker(F(k[ε]) → F(k)) ≃ₗ[k] H^1(X, 𝒪_X)` for
  `F = Pic_{X/k,(fppf)}` and the scalars `a • t = F(µ_a) t`, and the Zariski form
  `picardSchemeCotangentSpaceDualLinearEquiv h : (𝔪/𝔪²)^∨ ≃ₗ[k] H^1(X, 𝒪_X)`, for the maximal
  ideal `𝔪` of the local ring of `P` at the point `unitPoint R` of the section representing
  `0 ∈ F(k)`. That point is the unit point of the group law
  (`unitPoint_eq_unitPoint_picardCommGrpObj`, for any representing scheme), so this is the
  tangent space of the group scheme `P` at its unit.
* **The identity component** (Kleiman, Lemma 5.1(3), pp. 36–37, Prop. 5.3, p. 37):
  `picardIdentityComponent p P R` (`Pic⁰_{X/k}`, [IdentityComponent](../IdentityComponent.lean))
  is an open and closed group subscheme of `P`, of finite type and geometrically irreducible over
  `k`; these are the theorems and instances of that file and of
  `Aglib.AlgebraicGeometry.Group.IdentityComponent` at `P` and `R`, with no new declaration.
* **`Pic⁰` and field extension.** For a field extension `K` of `k` and `b : Spec K ⟶ Spec k`,
  `P_K = P ×_k K` represents `Pic_{X_K/K,(fppf)}`, `X_K = X ×_k K`, on locally Noetherian test
  schemes (`baseChangeRepresentableBy`; Kleiman, Ex. 4.4, p. 27, and Answer 4.4, p. 65), and its
  group law as such is the base change of that of `P` (`picardCommGrpObj_baseChange_toGrpObj`).
  So the identity component of the Picard scheme `P_K` of `X_K` is the preimage of `Pic⁰_{X/k}`
  (`identityComponent_baseChangeRepresentableBy`), and `(Pic⁰_{X/k})_K ≅ Pic⁰_{X_K/K}` as schemes
  (`picardIdentityComponentBaseChangeIso`). This combines the group-scheme statement
  `picardIdentityComponent_pullback` with the base change of the representation; both hold for
  any representing scheme `P` locally of finite type over `k`.
* **Target 6 over a field** (`exists_representableBy_fppfPicardSheaf_fieldProperties`): a
  separated `k`-scheme locally of finite type representing `Pic_{X/k,(fppf)}` on locally
  Noetherian test schemes with the tangent space, unit point, `Pic⁰_{X/k}` and field-extension
  statements above for `X` itself, witnessed by `picardScheme h`.

The separatedness of `P` in Prop. 5.3 is that of target 5 (`isSeparated_picardScheme`); its
smoothness clause, `Pic^τ` and Cor. 5.13 are not treated.

Instance search does not find the `k`-algebra structure `unitStalkAlgebra` of the local ring of
`P` at the unit point when `P = picardScheme h`, which is reducible; the Zariski form therefore
supplies it with `letI`. The group structure of `Pic⁰_{X/k}` and its finiteness instances are
found at `picardScheme h`, through the instances on `identityComponentOver`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.ProjectiveSpace

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace A ι)
  [IsClosedImmersion i] {N : ℕ} (e : ι ≃ Fin (N + 1))

include e in
/-- **A closed subscheme of `P^N_A` is proper over `Spec A`**: `i` is a closed immersion, hence
proper, and `toSpec A ι : P^N_A ⟶ Spec A` is proper since `ι ≃ Fin (N + 1)` is finite
(`isProper_toSpec`). -/
theorem isProper_comp_toSpec_of_isClosedImmersion : IsProper (i ≫ toSpec A ι) := by
  have : Finite ι := .of_equiv _ e.symm
  infer_instance

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Group

section RepresentingScheme

open scoped CategoryTheory.MonObj

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (e : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- **The tangent space is taken at the unit of the group law**: the point `unitPoint e` of the
section representing `0 ∈ Pic_{X/k,(fppf)}(k)`, at which `unitStalk e` is the local ring, is the
unit point of the group law `picardCommGrpObj p P e`, the image of its unit section. The unit
section is `1 : Spec k ⟶ P`, which `e` sends to `0` (`picard_homEquiv_one`). -/
theorem unitPoint_eq_unitPoint_picardCommGrpObj :
    unitPoint e = (letI := picardCommGrpObj p P e; Group.unitPoint P.obj) := by
  let := picardCommGrpObj p P e
  have h₁ : unitSection e =
      ObjectProperty.homMk (1 : (locallyNoetherianSpecOver k k).obj ⟶ P.obj) :=
    e.homEquiv.symm_apply_eq.mpr (picard_homEquiv_one p P e (locallyNoetherianSpecOver k k)).symm
  calc unitPoint e = η[P.obj].left
        ((CartesianMonoidalCategory.toUnit (locallyNoetherianSpecOver k k).obj).left
          (closedPoint (CommRingCat.of k))) := by
        rw [unitPoint, h₁]
        rfl
    _ = Group.unitPoint P.obj := Group.one_left_apply P.obj _

variable (K : Type u) [Field K] [Algebra k K]

/-- **`Pic⁰` commutes with field extension, as the identity component of `Pic_{X_K/K}`**
(Kleiman, arXiv:math/0504020v1, Prop. 5.3 and Lemma 5.1(3), p. 37, "forming it commutes with
extending `k`", with Ex. 4.4, p. 27): for a field extension `K` of `k` and
`b : Spec K ⟶ Spec k`, the identity component of `P_K = P ×_k K`, for its group law as the scheme
representing `Pic_{X_K/K,(fppf)}` through `baseChangeRepresentableBy p b P e`, is the preimage of
the identity component of `P` under the projection `P_K ⟶ P`. That group law is the base change
of the group law of `P` (`picardCommGrpObj_baseChange_toGrpObj`), so this is
`picardIdentityComponent_pullback`. -/
theorem identityComponent_baseChangeRepresentableBy :
    (letI := picardCommGrpObj (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (LocallyNoetherianOver.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K))) P)
        (baseChangeRepresentableBy p (Spec.map (CommRingCat.ofHom (algebraMap k K))) P e);
      identityComponent
        (LocallyNoetherianOver.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K))) P).obj) =
      pullback.fst P.obj.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⁻¹ᵁ
        (letI := picardCommGrpObj p P e; identityComponent P.obj) := by
  let := picardCommGrpObj p P e
  have hM := congrArg (fun G => G.toMonObj)
    (picardCommGrpObj_baseChange_toGrpObj p (Spec.map (CommRingCat.ofHom (algebraMap k K))) P e)
  refine Eq.trans ?_ (picardIdentityComponent_pullback p P e K)
  exact congrArg (fun m => @identityComponent K _
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj P.obj) m _) hM

/-- **`(Pic⁰_{X/k})_K ≅ Pic⁰_{X_K/K}`**: the base change of the identity component of `P` along
`Spec K ⟶ Spec k` is, as a scheme, the identity component of the scheme `P_K` representing
`Pic_{X_K/K,(fppf)}` (`baseChangeRepresentableBy`), for its group law. -/
def picardIdentityComponentBaseChangeIso :
    (pullback (picardIdentityComponent p P e).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) ≅
      (picardIdentityComponent (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (LocallyNoetherianOver.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K))) P)
        (baseChangeRepresentableBy p (Spec.map (CommRingCat.ofHom (algebraMap k K))) P e)).left :=
  pullbackPicardIdentityComponentIso p P e K ≪≫ Scheme.isoOfEq _
    ((picardIdentityComponent_pullback p P e K).trans
      (identityComponent_baseChangeRepresentableBy p P e K).symm)

end RepresentingScheme

section PicardScheme

open Strata

variable {k : Type u} [Field k] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace k ι} [IsClosedImmersion i] [Flat (i ≫ toSpec k ι)]
  [GeometricallyIntegral (i ≫ toSpec k ι)] {N : ℕ} {e : ι ≃ Fin (N + 1)}
  (h : FineStrataRepresentableByHQuasiProjective i N e)

/-- **The tangent space at the unit of the Picard scheme is `H^1(X, 𝒪_X)`** (Kleiman,
arXiv:math/0504020v1, Thm 5.11, p. 42): for the Picard scheme of a closed subscheme `X` of
`P^N_k`, flat with geometrically integral fibres, `ker(F(k[ε]) → F(k)) ≃ₗ[k] H^1(X, 𝒪_X)`, where
`F = Pic_{X/k,(fppf)}`, `X` is a scheme over `k` through `i ≫ toSpec k ι`, and
`a • t = F(µ_a) t`. This is
`tangentKernelLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral` at
`picardSchemeRepresentableBy h`, with properness from
`isProper_comp_toSpec_of_isClosedImmersion`. -/
def picardSchemeTangentKernelLinearEquiv :
    letI := tangentKernelModule (picardSchemeRepresentableBy h) k
    tangentKernel (fppfPicardSheaf (i ≫ toSpec k ι)).obj k ≃ₗ[k]
      structureCohomology k (Over.mk (i ≫ toSpec k ι)) 1 :=
  haveI : IsProper (Over.mk (i ≫ toSpec k ι)).hom := isProper_comp_toSpec_of_isClosedImmersion i e
  haveI : Flat (Over.mk (i ≫ toSpec k ι)).hom := inferInstanceAs (Flat (i ≫ toSpec k ι))
  haveI : GeometricallyIntegral (Over.mk (i ≫ toSpec k ι)).hom :=
    inferInstanceAs (GeometricallyIntegral (i ≫ toSpec k ι))
  tangentKernelLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral
    (Over.mk (i ≫ toSpec k ι)) (picardSchemeRepresentableBy h)

/-- **The Zariski form** (Kleiman, arXiv:math/0504020v1, proof of Thm 5.11, p. 42): the dual of
the cotangent space `𝔪/𝔪²` of the Picard scheme at the unit point is `H^1(X, 𝒪_X)`. The
`k`-algebra structure `unitStalkAlgebra` of the local ring is supplied explicitly, since instance
search does not find it at `picardScheme h`. -/
def picardSchemeCotangentSpaceDualLinearEquiv :
    letI := unitStalkAlgebra (picardSchemeRepresentableBy h)
    Module.Dual k (CotangentSpace (unitStalk (picardSchemeRepresentableBy h))) ≃ₗ[k]
      structureCohomology k (Over.mk (i ≫ toSpec k ι)) 1 :=
  haveI : IsProper (Over.mk (i ≫ toSpec k ι)).hom := isProper_comp_toSpec_of_isClosedImmersion i e
  haveI : Flat (Over.mk (i ≫ toSpec k ι)).hom := inferInstanceAs (Flat (i ≫ toSpec k ι))
  haveI : GeometricallyIntegral (Over.mk (i ≫ toSpec k ι)).hom :=
    inferInstanceAs (GeometricallyIntegral (i ≫ toSpec k ι))
  cotangentSpaceDualLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral
    (Over.mk (i ≫ toSpec k ι)) (picardSchemeRepresentableBy h)

variable (i e) in
include e in
/-- **The Picard scheme over a field** (target 6 of `docs/PICARD_PLAN.md` over a field; Kleiman,
*The Picard scheme*, arXiv:math/0504020v1, Thm 4.8, pp. 27–31, Prop. 5.3, p. 37, Thm 5.11, p. 42,
with Ex. 4.4, p. 27). Let `k` be a field and `X ⊆ P^N_k` closed, flat with geometrically integral
fibres, and write `p = i ≫ toSpec k ι`. There are a scheme `P`, separated and locally of finite
type over `k`, and a representation `R` of `Pic_{X/k,(fppf)}` by `P` on locally Noetherian test
schemes, such that, for the group law `picardCommGrpObj p P R` of `P`:

1. `ker(Pic_{X/k,(fppf)}(k[ε]) → Pic_{X/k,(fppf)}(k)) ≃ₗ[k] H^1(X, 𝒪_X)` (Thm 5.11), and the dual
   of the cotangent space of `P` at the point of the zero class is `H^1(X, 𝒪_X)`;
2. that point is the unit point of the group law;
3. the identity component `Pic⁰_{X/k}` is open and closed in `P`, a group subscheme,
   quasi-compact and locally of finite type, and geometrically irreducible over `k` (Prop. 5.3);
4. for every field extension `K` of `k`, the identity component of `Pic_{X_K/K}`, represented by
   `P ×_k K`, is the preimage of `Pic⁰_{X/k}`.

The witnesses are `picardScheme h` and `picardSchemeRepresentableBy h` for
`h = Strata.fineStrataRepresentableByHQuasiProjective i e`. -/
theorem exists_representableBy_fppfPicardSheaf_fieldProperties :
    ∃ (P : LocallyNoetherianOver (Spec (.of k)))
      (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
        (fppfPicardSheaf (i ≫ toSpec k ι)).obj ⋙
          CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
      (_ : LocallyOfFiniteType P.obj.hom),
      IsSeparated P.obj.hom ∧
      (letI := tangentKernelModule R k;
        Nonempty (tangentKernel (fppfPicardSheaf (i ≫ toSpec k ι)).obj k ≃ₗ[k]
          structureCohomology k (Over.mk (i ≫ toSpec k ι)) 1)) ∧
      (letI := unitStalkAlgebra R;
        Nonempty (Module.Dual k (CotangentSpace (unitStalk R)) ≃ₗ[k]
          structureCohomology k (Over.mk (i ≫ toSpec k ι)) 1)) ∧
      (letI := picardCommGrpObj (i ≫ toSpec k ι) P R;
        unitPoint R = Group.unitPoint P.obj ∧
          IsClopen (identityComponent P.obj : Set P.obj.left) ∧
          IsMonHom (identityComponentι P.obj) ∧
          QuasiCompact (identityComponentOver P.obj).hom ∧
          LocallyOfFiniteType (identityComponentOver P.obj).hom ∧
          GeometricallyIrreducible (identityComponentOver P.obj).hom) ∧
      ∀ (K : Type u) [Field K] [Algebra k K],
        (letI := picardCommGrpObj
            (pullback.snd (i ≫ toSpec k ι) (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            (LocallyNoetherianOver.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K))) P)
            (baseChangeRepresentableBy (i ≫ toSpec k ι)
              (Spec.map (CommRingCat.ofHom (algebraMap k K))) P R);
          identityComponent (LocallyNoetherianOver.baseChange
            (Spec.map (CommRingCat.ofHom (algebraMap k K))) P).obj) =
          pullback.fst P.obj.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⁻¹ᵁ
            (letI := picardCommGrpObj (i ≫ toSpec k ι) P R; identityComponent P.obj) := by
  have h₀ := fineStrataRepresentableByHQuasiProjective i e
  exact ⟨picardScheme h₀, picardSchemeRepresentableBy h₀, inferInstance, inferInstance,
    ⟨picardSchemeTangentKernelLinearEquiv h₀⟩, ⟨picardSchemeCotangentSpaceDualLinearEquiv h₀⟩,
    ⟨unitPoint_eq_unitPoint_picardCommGrpObj _ _ _, isClopen_picardIdentityComponent _ _ _,
      isMonHom_picardIdentityComponentι _ _ _, inferInstance, inferInstance, inferInstance⟩,
    fun K _ _ => identityComponent_baseChangeRepresentableBy _ _ _ K⟩

end PicardScheme

end AlgebraicGeometry.Scheme.RelativePicard
