/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Comparison.RepresentableBy
public import Aglib.AlgebraicGeometry.Picard.Scheme.FieldProperties

/-!
# Basic properties of the Picard scheme

Let `A` be a Noetherian ring, `S = Spec A`, `i : X ⟶ P^N_A = ProjectiveSpace A ι` a closed
immersion with `ι ≃ Fin (N + 1)`, such that `p = i ≫ toSpec A ι` is flat with geometrically
integral fibres, and let `P = picardScheme h` with `R = picardSchemeRepresentableBy h` be the
Picard scheme of Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Thm 4.8, pp. 27–31 (target 5
of `docs/PICARD_PLAN.md`): it represents `Pic_{X/S,(fppf)}` on locally Noetherian test schemes
and is separated and locally of finite type over `S`. Here `h` is any proof of the fine-strata
premise, which always holds (`Strata.fineStrataRepresentableByHQuasiProjective i e`,
[FineStrata](../Representability/FineStrata.lean)), so nothing below is conditional. This file
instantiates the basic properties of a scheme representing `Pic_{X/S,(fppf)}` at `P` (target 6 of
`docs/PICARD_PLAN.md`):

* **The group law** (Kleiman, Def. 4.1, p. 26, for the Picard scheme; Stacks, Tag 022S, for group
  schemes through their functors of points): `picardCommGrpObj p P R` is a commutative group object
  of `Over S`, and `R` is an isomorphism of abelian groups on locally Noetherian points
  (`picard_homEquiv_mul`, `picardHomAddEquiv`). These apply at `P` as they stand
  ([GroupLaw](../GroupLaw.lean)).
* **With a section** `o` of `p` (Kleiman, Thm 2.5(2), p. 18, Def. 2.8 and Lemma 2.9, p. 19;
  Stacks, Tag 0B9N): `P` also represents the normalized functor `T ↦ ker(o_T^*)`
  (`picardSchemeNormalizedRepresentableBy`) and the rigidified functor
  (`picardSchemeRigidifiedRepresentableBy`), and, if `p` has a section, the relative functor
  `P_{X/S}(T) = Pic(X ×_S T) / Pic(T)` (`picardSchemeRelativeRepresentableByOfIsSplitEpi`), on
  locally Noetherian test schemes. The properness of `p` is
  `ProjectiveSpace.isProper_comp_toSpec_of_isClosedImmersion`.
* **Base change** (Kleiman, Ex. 4.4, p. 27, and Answer 4.4, p. 65): for `g : S' ⟶ S` with `S'`
  locally Noetherian, `P ×_S S'` represents `Pic_{X_{S'}/S',(fppf)}` on locally Noetherian
  `S'`-schemes (`baseChangeRepresentableBy p g P R`), with the base-changed group law
  (`picardCommGrpObj_baseChange_toGrpObj`), and every scheme representing
  `Pic_{X_{S'}/S',(fppf)}` there is isomorphic to `P ×_S S'` (`picardSchemeBaseChangeIso`).
* **The Hilbert-polynomial decomposition** (Kleiman, Thm 4.8(2), pp. 27–29): the open and closed
  strata `picardStratumOpens h φ` cover `P` disjointly, each the increasing union of the
  H-quasi-projective `picardLevelOpens h φ m`
  ([Stratification](Stratification.lean), `exists_representableBy_fppfPicardSheaf`).
* **Over a field** ([FieldProperties](FieldProperties.lean)): `T_0 = H^1(X, 𝒪_X)` and
  `Pic⁰_{X/k}` an open and closed group subscheme of finite type, geometrically irreducible, whose
  formation commutes with field extension.

`exists_representableBy_fppfPicardSheaf_basicProperties` collects these statements, with the field
statements for the fibres `X_K = X ×_S Spec K ⟶ Spec K` over all field points
`g : Spec K ⟶ S`, where `P ×_S Spec K` represents `Pic_{X_K/K,(fppf)}`. For `A = k` a field the
statements for `X` itself are collected in `exists_representableBy_fppfPicardSheaf_fieldProperties`
([FieldProperties](FieldProperties.lean)).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.RelativePicard

open Strata Scheme.Group

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)] {N : ℕ} {e : ι ≃ Fin (N + 1)}
  (h : FineStrataRepresentableByHQuasiProjective i N e)

section Section

variable (o : Spec (.of A) ⟶ X) (ho : o ≫ i ≫ toSpec A ι = 𝟙 _)

/-- **The Picard scheme represents the normalized Picard functor** (Kleiman,
arXiv:math/0504020v1, Thm 2.5(2), p. 18): for a section `o` of `p = i ≫ toSpec A ι`, the Picard
scheme represents `T ↦ ker(o_T^* : Pic(X ×_S T) → Pic(T))` on locally Noetherian test schemes.
This is `normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral` at
`picardSchemeRepresentableBy h`, with properness from
`isProper_comp_toSpec_of_isClosedImmersion`. -/
def picardSchemeNormalizedRepresentableBy :
    ((locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
      normalizedPicardFunctor (i ≫ toSpec A ι) o ho ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy (picardScheme h) :=
  haveI := isProper_comp_toSpec_of_isClosedImmersion i e
  normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral _ o ho
    (picardSchemeRepresentableBy h)

theorem picardSchemeNormalizedRepresentableBy_homEquiv
    {T : LocallyNoetherianOver (Spec (.of A))} (f : T ⟶ picardScheme h) :
    (picardSchemeNormalizedRepresentableBy h o ho).homEquiv f =
      haveI := isProper_comp_toSpec_of_isClosedImmersion i e
      ((normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral _ o ho).inv.app
        (op T.obj)).hom ((picardSchemeRepresentableBy h).homEquiv f) :=
  rfl

/-- **The Picard scheme represents the rigidified Picard functor** (Kleiman,
arXiv:math/0504020v1, Def. 2.8 and Lemma 2.9, p. 19, with Thm 2.5(2), p. 18): the functor of
isomorphism classes of line bundles rigidified along the section `o`, on locally Noetherian test
schemes. -/
def picardSchemeRigidifiedRepresentableBy :
    ((locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
      rigidifiedPicardFunctor (i ≫ toSpec A ι) o ho).RepresentableBy (picardScheme h) :=
  haveI := isProper_comp_toSpec_of_isClosedImmersion i e
  rigidifiedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral _ o ho
    (picardSchemeRepresentableBy h)

theorem picardSchemeRigidifiedRepresentableBy_homEquiv
    {T : LocallyNoetherianOver (Spec (.of A))} (f : T ⟶ picardScheme h) :
    (picardSchemeRigidifiedRepresentableBy h o ho).homEquiv f =
      haveI := isProper_comp_toSpec_of_isClosedImmersion i e
      (rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral _ o ho).inv.app (op T.obj)
        ((picardSchemeRepresentableBy h).homEquiv f) :=
  rfl

end Section

/-- **The Picard scheme represents the relative Picard functor** when `p = i ≫ toSpec A ι` has a
section (Kleiman, arXiv:math/0504020v1, Thm 2.5(2), p. 18): `P_{X/S}(T) = Pic(X ×_S T) / Pic(T)`
on locally Noetherian test schemes. -/
def picardSchemeRelativeRepresentableByOfIsSplitEpi [IsSplitEpi (i ≫ toSpec A ι)] :
    ((locallyNoetherianOverInclusion (Spec (.of A))).op ⋙ relativePicardFunctor (i ≫ toSpec A ι) ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy (picardScheme h) :=
  haveI := isProper_comp_toSpec_of_isClosedImmersion i e
  relativeRepresentableByOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral _
    (picardSchemeRepresentableBy h)

theorem picardSchemeRelativeRepresentableByOfIsSplitEpi_homEquiv [IsSplitEpi (i ≫ toSpec A ι)]
    {T : LocallyNoetherianOver (Spec (.of A))} (f : T ⟶ picardScheme h) :
    (picardSchemeRelativeRepresentableByOfIsSplitEpi h).homEquiv f =
      haveI := isProper_comp_toSpec_of_isClosedImmersion i e
      ((relativeFppfIsoOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral _).inv.app
        (op T.obj)).hom ((picardSchemeRepresentableBy h).homEquiv f) :=
  rfl

section BaseChange

variable {S' : Scheme.{u}} [IsLocallyNoetherian S'] (g : S' ⟶ Spec (.of A))

/-- **`Pic_{X_{S'}/S'} ≅ Pic_{X/S} ×_S S'`** (Kleiman, arXiv:math/0504020v1, Ex. 4.4, p. 27, and
Answer 4.4, p. 65): for `g : S' ⟶ S` with `S'` locally Noetherian, every scheme `P'` representing
`Pic_{X_{S'}/S',(fppf)}` on locally Noetherian `S'`-schemes, `X_{S'} = X ×_S S'`, is isomorphic to
the base change `P ×_S S'` of the Picard scheme, which represents it through
`baseChangeRepresentableBy` (Mathlib's `RepresentableBy.uniqueUpToIso`). -/
def picardSchemeBaseChangeIso {P' : LocallyNoetherianOver S'}
    (e' : ((locallyNoetherianOverInclusion S').op ⋙
      (fppfPicardSheaf (pullback.snd (i ≫ toSpec A ι) g)).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P') :
    P' ≅ LocallyNoetherianOver.baseChange g (picardScheme h) :=
  e'.uniqueUpToIso (baseChangeRepresentableBy _ g _ (picardSchemeRepresentableBy h))

end BaseChange

variable (i e) in
/-- **Basic properties of the Picard scheme** (target 6 of `docs/PICARD_PLAN.md`; Kleiman, *The
Picard scheme*, arXiv:math/0504020v1, Thm 4.8, pp. 27–31, with Def. 4.1, p. 26, Thm 2.5(2), p. 18,
Ex. 4.4, p. 27, Lemma 5.1 and Prop. 5.3, pp. 36–37, Thm 5.11, p. 42). Let `A` be Noetherian and
`X ⊆ P^N_A` closed, flat over `S = Spec A` with geometrically integral fibres, and write
`p = i ≫ toSpec A ι`. There are a scheme `P`, separated and locally of finite type over `S`, and
a representation `R` of `Pic_{X/S,(fppf)}` by `P` on locally Noetherian test schemes, such that,
for the group law `picardCommGrpObj p P R` of `P`:

1. `R` is additive on locally Noetherian points;
2. for every section `o` of `p`, `P` represents the normalized and the rigidified Picard functors,
   and, if `p` has a section, the relative Picard functor `P_{X/S}`, on locally Noetherian test
   schemes;
3. for every `g : S' ⟶ S` with `S'` locally Noetherian, `P ×_S S'` represents
   `Pic_{X_{S'}/S',(fppf)}` on locally Noetherian test schemes through
   `baseChangeRepresentableBy p g P R`, its group law as such is the base change of that of `P`,
   and every representing scheme of `Pic_{X_{S'}/S',(fppf)}` is isomorphic to `P ×_S S'`;
4. the open and closed strata of the Hilbert polynomials `φ` of `L^{-1}` on the fibres
   (`eulerCondition`) are pairwise disjoint and cover `P`, and a morphism lands in the stratum of
   `φ` exactly when its class lies in the subsheaf `Pic^φ`;
5. for every field `K` and `g : Spec K ⟶ S`, with `X_K = X ×_S Spec K` over `K` and
   `P_K = P ×_S Spec K` representing `Pic_{X_K/K,(fppf)}`:
   `ker(Pic_{X_K/K,(fppf)}(K[ε]) → Pic_{X_K/K,(fppf)}(K)) ≃ₗ[K] H^1(X_K, 𝒪)` (Thm 5.11), the
   dual of the cotangent space at the point of the zero class is `H^1(X_K, 𝒪)`, and that point is
   the unit point of the group law of `P_K`; the identity component `Pic⁰_{X_K/K}` is open and
   closed in `P_K`, a group subscheme, quasi-compact and locally of finite type, and
   geometrically irreducible over `K` (Prop. 5.3); and for every field extension `L` of `K` the
   identity component of `Pic_{X_L/L}`, represented by `P_K ×_K L`, is the preimage of
   `Pic⁰_{X_K/K}`.

The witnesses are `picardScheme h` and `picardSchemeRepresentableBy h` for
`h = Strata.fineStrataRepresentableByHQuasiProjective i e`. For `A = k` a field, item 5 at
`g = 𝟙` concerns `X ×_k k`; the statements for `X` itself are collected in
`exists_representableBy_fppfPicardSheaf_fieldProperties` ([FieldProperties](FieldProperties.lean)).
-/
theorem exists_representableBy_fppfPicardSheaf_basicProperties :
    ∃ (P : LocallyNoetherianOver (Spec (.of A)))
      (R : ((locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙
          CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
      (_ : LocallyOfFiniteType P.obj.hom),
      IsSeparated P.obj.hom ∧
      -- 1. the group law: the product `a * b = lift a b ≫ μ` of `T ⟶ P` goes to the sum
      (letI := picardCommGrpObj (i ≫ toSpec A ι) P R;
        ∀ {T : LocallyNoetherianOver (Spec (.of A))} (a b : T.obj ⟶ P.obj),
          R.homEquiv (ObjectProperty.homMk (CartesianMonoidalCategory.lift a b ≫ MonObj.mul)) =
            R.homEquiv' (F := (locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
                (fppfPicardSheaf (i ≫ toSpec A ι)).obj) (ObjectProperty.homMk a) +
              R.homEquiv' (F := (locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
                (fppfPicardSheaf (i ≫ toSpec A ι)).obj) (ObjectProperty.homMk b)) ∧
      -- 2. with a section
      (∀ (o : Spec (.of A) ⟶ X) (ho : o ≫ i ≫ toSpec A ι = 𝟙 _),
        Nonempty (((locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
          normalizedPicardFunctor (i ≫ toSpec A ι) o ho ⋙
            CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P) ∧
        Nonempty (((locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
          rigidifiedPicardFunctor (i ≫ toSpec A ι) o ho).RepresentableBy P)) ∧
      (IsSplitEpi (i ≫ toSpec A ι) →
        Nonempty (((locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
          relativePicardFunctor (i ≫ toSpec A ι) ⋙
            CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)) ∧
      -- 3. base change
      (∀ {S' : Scheme.{u}} [IsLocallyNoetherian S'] (g : S' ⟶ Spec (.of A)),
        (letI := picardCommGrpObj (i ≫ toSpec A ι) P R;
          (picardCommGrpObj (pullback.snd (i ≫ toSpec A ι) g)
              (LocallyNoetherianOver.baseChange g P)
              (baseChangeRepresentableBy (i ≫ toSpec A ι) g P R)).toGrpObj =
            Functor.grpObjObj (F := Over.pullback g) (G := P.obj)) ∧
        ∀ (P' : LocallyNoetherianOver S'), ((locallyNoetherianOverInclusion S').op ⋙
          (fppfPicardSheaf (pullback.snd (i ≫ toSpec A ι) g)).obj ⋙
            CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P' →
          Nonempty (P' ≅ LocallyNoetherianOver.baseChange g P)) ∧
      -- 4. the Hilbert-polynomial decomposition
      (∃ stratum : Polynomial ℚ → P.obj.left.Opens,
        (∀ φ, IsClopen (stratum φ : Set P.obj.left)) ∧
          Pairwise (Function.onFun Disjoint stratum) ∧ ⨆ φ, stratum φ = ⊤ ∧
          ∀ {T : LocallyNoetherianOver (Spec (.of A))} (a : T ⟶ P) (φ : Polynomial ℚ),
            R.homEquiv a ∈ (eulerCondition i N e φ).subfunctor.obj (op T.obj) ↔
              a.hom.left ⁻¹ᵁ stratum φ = ⊤) ∧
      -- 5. over the field points of `S`
      (∀ (K : Type u) [Field K] (g : Spec (.of K) ⟶ Spec (.of A)),
        (letI := tangentKernelModule (baseChangeRepresentableBy (i ≫ toSpec A ι) g P R) K;
          Nonempty (tangentKernel (fppfPicardSheaf (pullback.snd (i ≫ toSpec A ι) g)).obj K ≃ₗ[K]
            structureCohomology K (Over.mk (pullback.snd (i ≫ toSpec A ι) g)) 1)) ∧
        (letI := unitStalkAlgebra (baseChangeRepresentableBy (i ≫ toSpec A ι) g P R);
          Nonempty (Module.Dual K (CotangentSpace
              (unitStalk (baseChangeRepresentableBy (i ≫ toSpec A ι) g P R))) ≃ₗ[K]
            structureCohomology K (Over.mk (pullback.snd (i ≫ toSpec A ι) g)) 1)) ∧
        (letI := picardCommGrpObj (pullback.snd (i ≫ toSpec A ι) g)
            (LocallyNoetherianOver.baseChange g P)
            (baseChangeRepresentableBy (i ≫ toSpec A ι) g P R);
          unitPoint (baseChangeRepresentableBy (i ≫ toSpec A ι) g P R) =
              Group.unitPoint (LocallyNoetherianOver.baseChange g P).obj ∧
            IsClopen (identityComponent (LocallyNoetherianOver.baseChange g P).obj :
              Set (LocallyNoetherianOver.baseChange g P).obj.left) ∧
            IsMonHom (identityComponentι (LocallyNoetherianOver.baseChange g P).obj) ∧
            QuasiCompact (identityComponentOver (LocallyNoetherianOver.baseChange g P).obj).hom ∧
            LocallyOfFiniteType
              (identityComponentOver (LocallyNoetherianOver.baseChange g P).obj).hom ∧
            GeometricallyIrreducible
              (identityComponentOver (LocallyNoetherianOver.baseChange g P).obj).hom) ∧
        ∀ (L : Type u) [Field L] [Algebra K L],
          (letI := picardCommGrpObj
              (pullback.snd (pullback.snd (i ≫ toSpec A ι) g)
                (Spec.map (CommRingCat.ofHom (algebraMap K L))))
              (LocallyNoetherianOver.baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))
                (LocallyNoetherianOver.baseChange g P))
              (baseChangeRepresentableBy (pullback.snd (i ≫ toSpec A ι) g)
                (Spec.map (CommRingCat.ofHom (algebraMap K L)))
                (LocallyNoetherianOver.baseChange g P)
                (baseChangeRepresentableBy (i ≫ toSpec A ι) g P R));
            identityComponent (LocallyNoetherianOver.baseChange
              (Spec.map (CommRingCat.ofHom (algebraMap K L)))
              (LocallyNoetherianOver.baseChange g P)).obj) =
            pullback.fst (LocallyNoetherianOver.baseChange g P).obj.hom
                (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⁻¹ᵁ
              (letI := picardCommGrpObj (pullback.snd (i ≫ toSpec A ι) g)
                  (LocallyNoetherianOver.baseChange g P)
                  (baseChangeRepresentableBy (i ≫ toSpec A ι) g P R);
                identityComponent (LocallyNoetherianOver.baseChange g P).obj)) := by
  have h₀ := fineStrataRepresentableByHQuasiProjective i e
  have : IsProper (i ≫ toSpec A ι) := isProper_comp_toSpec_of_isClosedImmersion i e
  refine ⟨picardScheme h₀, picardSchemeRepresentableBy h₀, inferInstance, inferInstance,
    fun a b => picard_homEquiv_mul _ _ _ a b,
    fun o ho => ⟨⟨picardSchemeNormalizedRepresentableBy h₀ o ho⟩,
      ⟨picardSchemeRigidifiedRepresentableBy h₀ o ho⟩⟩,
    fun _ => ⟨picardSchemeRelativeRepresentableByOfIsSplitEpi h₀⟩,
    fun g => ⟨picardCommGrpObj_baseChange_toGrpObj _ g _ _,
      fun _ e' => ⟨picardSchemeBaseChangeIso h₀ g e'⟩⟩,
    ⟨picardStratumOpens h₀, isClopen_picardStratumOpens h₀,
      pairwise_disjoint_picardStratumOpens h₀, iSup_picardStratumOpens h₀,
      fun a φ => picardSchemeRepresentableBy_homEquiv_mem_eulerCondition_iff h₀ φ a⟩,
    ?_⟩
  intro K _ g
  have hK : IsProper (Over.mk (pullback.snd (i ≫ toSpec A ι) g)).hom :=
    inferInstanceAs (IsProper (pullback.snd (i ≫ toSpec A ι) g))
  have hF : Flat (Over.mk (pullback.snd (i ≫ toSpec A ι) g)).hom :=
    inferInstanceAs (Flat (pullback.snd (i ≫ toSpec A ι) g))
  have hG : GeometricallyIntegral (Over.mk (pullback.snd (i ≫ toSpec A ι) g)).hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd (i ≫ toSpec A ι) g))
  refine ⟨⟨tangentKernelLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral
      (Over.mk (pullback.snd (i ≫ toSpec A ι) g))
      (baseChangeRepresentableBy (i ≫ toSpec A ι) g (picardScheme h₀)
        (picardSchemeRepresentableBy h₀))⟩,
    ⟨cotangentSpaceDualLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral
      (Over.mk (pullback.snd (i ≫ toSpec A ι) g))
      (baseChangeRepresentableBy (i ≫ toSpec A ι) g (picardScheme h₀)
        (picardSchemeRepresentableBy h₀))⟩,
    ⟨unitPoint_eq_unitPoint_picardCommGrpObj _ _ _,
      isClopen_picardIdentityComponent _ _ _, isMonHom_picardIdentityComponentι _ _ _,
      inferInstance, inferInstance, inferInstance⟩,
    ?_⟩
  intro L _ _
  exact identityComponent_baseChangeRepresentableBy _ _ _ L

end AlgebraicGeometry.Scheme.RelativePicard
