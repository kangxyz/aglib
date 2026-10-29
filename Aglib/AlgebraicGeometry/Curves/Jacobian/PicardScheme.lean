/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Core
public import Aglib.AlgebraicGeometry.Curves.SmoothGeometry
public import Aglib.AlgebraicGeometry.Curves.Projectivity.Integral
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension
public import Aglib.AlgebraicGeometry.Picard.Scheme.Properties

/-!
# The Picard scheme of a smooth proper curve

Let `k` be a field and `X` a smooth proper geometrically connected curve over `k`
(`Curve.Properties X`). This file derives from `Curve.Properties X` alone the hypotheses of the
Picard-scheme theorems of `Aglib.AlgebraicGeometry.Picard.Scheme` and states their conclusions for
the structure morphism `X ⟶ Spec k` itself.

* `Curve.Properties.topologicalKrullDim_eq_one`, `Curve.Properties.flat`: `X` has dimension one
  and is flat over `k`; integrality and geometric integrality are
  `Curve.Properties.isIntegral` and `Curve.Properties.isGeometricallyIntegral`
  ([SmoothGeometry](../SmoothGeometry.lean)).
* `Curve.Properties.exists_closedImmersion_projectiveSpace`: a closed immersion
  `i : X ⟶ P^N_k = ProjectiveSpace k (ULift (Fin (N + 1)))` with `i ≫ toSpec = X.hom`, from the
  projectivity of proper integral curves (`Curve.Projectivity.exists_projectiveEmbedding`).
* `Curve.exists_representableBy_fppfPicardSheaf_properties`: **the Picard scheme of `X`**. There
  are a scheme `P` over `k`, separated and locally of finite type, and a representation `R` of
  `Pic_{X/k,(fppf)}` (for `X.hom`) on locally Noetherian test schemes, such that the group law
  `picardCommGrpObj X.hom P R` is additive on points, `P` represents the normalized, rigidified and
  (with a section) relative Picard functors, its base changes along locally Noetherian `S'` are the
  Picard schemes of `X_{S'}`, the tangent space at the unit is `H^1(X, 𝒪_X)`, and the identity
  component `Pic⁰_{X/k}` is open and closed, a group subscheme, quasi-compact, of finite type and
  geometrically irreducible, compatibly with field extensions. These are Kleiman, *The Picard
  scheme*, arXiv:math/0504020v1, Thm 4.8 (pp. 27–31, fppf form), Thm 2.5(2) (p. 18), Ex. 4.4
  (p. 27), Lemma 5.1(3) and Prop. 5.3 (pp. 36–37) and Thm 5.11 (p. 42), in the form of items 1–3
  of `exists_representableBy_fppfPicardSheaf_basicProperties` and of
  `exists_representableBy_fppfPicardSheaf_fieldProperties`, at the embedding above. Item 4 there,
  the Hilbert-polynomial strata, depends on the embedding and is treated in
  [DegreeStrata](DegreeStrata.lean); item 5, the same field statements for the fibres over all
  field points of `Spec k`, is not repeated.

The only hypothesis is `Curve.Properties X`; no rational point, genus or algebraic closedness is
assumed. The structure morphism `X.hom` is identified with `i ≫ toSpec` by generalizing it to a
variable and substituting.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.Group

namespace AlgebraicGeometry.Scheme.OverField.Curve

variable {k : Type u} [Field k] {X : FScheme k}

/-- **A curve has dimension one**: `smoothFieldDimension` at the smooth relative dimension one
structure morphism of a nonempty curve. -/
theorem Properties.topologicalKrullDim_eq_one (hX : Properties X) :
    topologicalKrullDim X.left = 1 :=
  curveProperties_dimension smoothFieldDimension hX

/-- **A curve is flat over the field**: a smooth morphism is flat. -/
theorem Properties.flat (hX : Properties X) : Flat X.hom := by
  have := curveProperties_smooth hX
  infer_instance

/-- **A curve is a closed subscheme of a projective space over its field**
(`Curve.Projectivity.exists_projectiveEmbedding`, for the proper integral dimension-one scheme
`X`): there is a closed immersion `i : X ⟶ P^N_k` with `i ≫ toSpec = X.hom`. -/
theorem Properties.exists_closedImmersion_projectiveSpace (hX : Properties X) :
    ∃ (N : ℕ) (i : X.left ⟶ ProjectiveSpace k (ULift.{u} (Fin (N + 1)))),
      IsClosedImmersion i ∧ i ≫ ProjectiveSpace.toSpec k (ULift.{u} (Fin (N + 1))) = X.hom := by
  have := hX.isIntegral
  have := hX.proper
  exact Projectivity.exists_projectiveEmbedding X hX.topologicalKrullDim_eq_one

/-- **The Picard scheme of a smooth proper curve** (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Thm 4.8, pp. 27–31, fppf form on locally Noetherian test schemes, with
Def. 4.1, p. 26, Thm 2.5(2), p. 18, Ex. 4.4, p. 27, Lemma 5.1(3) and Prop. 5.3, pp. 36–37,
Thm 5.11, p. 42). For a smooth proper geometrically connected curve `X` over a field `k`, there are
a scheme `P` over `k`, locally of finite type and separated, and a representation `R` of
`Pic_{X/k,(fppf)}` by `P` on locally Noetherian test schemes, such that, for the group law
`picardCommGrpObj X.hom P R`:

1. `R` is additive on locally Noetherian points;
2. for every section `o` of `X.hom`, `P` represents the normalized and the rigidified Picard
   functors, and, if `X.hom` has a section, the relative Picard functor `P_{X/k}`;
3. for every locally Noetherian `S'` over `k`, `P ×_k S'` represents `Pic_{X_{S'}/S',(fppf)}` with
   the base-changed group law, and every representing scheme of that sheaf is `P ×_k S'`;
4. `ker(Pic_{X/k,(fppf)}(k[ε]) → Pic_{X/k,(fppf)}(k)) ≃ₗ[k] H^1(X, 𝒪_X)` (Thm 5.11), and the dual
   of the cotangent space of `P` at the point of the zero class is `H^1(X, 𝒪_X)`;
5. that point is the unit point; the identity component `Pic⁰_{X/k}` is open and closed in `P`, a
   group subscheme, quasi-compact and locally of finite type, and geometrically irreducible over
   `k` (Prop. 5.3);
6. for every field extension `K` of `k`, the identity component of `Pic_{X_K/K}`, represented by
   `P ×_k K`, is the preimage of `Pic⁰_{X/k}`.

The witnesses are `picardScheme h` and `picardSchemeRepresentableBy h` of the closed embedding of
`Curve.Properties.exists_closedImmersion_projectiveSpace`, with
`h = Strata.fineStrataRepresentableByHQuasiProjective i e`. -/
theorem exists_representableBy_fppfPicardSheaf_properties (hX : Properties X) :
    ∃ (P : LocallyNoetherianOver (Spec (.of k)))
      (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
        (fppfPicardSheaf X.hom).obj ⋙
          CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
      (_ : LocallyOfFiniteType P.obj.hom),
      IsSeparated P.obj.hom ∧
      -- 1. the group law
      (letI := picardCommGrpObj X.hom P R;
        ∀ {T : LocallyNoetherianOver (Spec (.of k))} (a b : T.obj ⟶ P.obj),
          R.homEquiv (ObjectProperty.homMk (CartesianMonoidalCategory.lift a b ≫ MonObj.mul)) =
            R.homEquiv' (F := (locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
                (fppfPicardSheaf X.hom).obj) (ObjectProperty.homMk a) +
              R.homEquiv' (F := (locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
                (fppfPicardSheaf X.hom).obj) (ObjectProperty.homMk b)) ∧
      -- 2. with a section
      (∀ (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _),
        Nonempty (((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
          normalizedPicardFunctor X.hom o ho ⋙
            CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P) ∧
        Nonempty (((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
          rigidifiedPicardFunctor X.hom o ho).RepresentableBy P)) ∧
      (IsSplitEpi X.hom →
        Nonempty (((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
          relativePicardFunctor X.hom ⋙
            CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)) ∧
      -- 3. base change
      (∀ {S' : Scheme.{u}} [IsLocallyNoetherian S'] (g : S' ⟶ Spec (.of k)),
        (letI := picardCommGrpObj X.hom P R;
          (picardCommGrpObj (pullback.snd X.hom g)
              (LocallyNoetherianOver.baseChange g P)
              (baseChangeRepresentableBy X.hom g P R)).toGrpObj =
            Functor.grpObjObj (F := Over.pullback g) (G := P.obj)) ∧
        ∀ (P' : LocallyNoetherianOver S'), ((locallyNoetherianOverInclusion S').op ⋙
          (fppfPicardSheaf (pullback.snd X.hom g)).obj ⋙
            CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P' →
          Nonempty (P' ≅ LocallyNoetherianOver.baseChange g P)) ∧
      -- 4. the tangent space at the unit
      (letI := tangentKernelModule R k;
        Nonempty (tangentKernel (fppfPicardSheaf X.hom).obj k ≃ₗ[k]
          structureCohomology k X 1)) ∧
      (letI := unitStalkAlgebra R;
        Nonempty (Module.Dual k (CotangentSpace (unitStalk R)) ≃ₗ[k]
          structureCohomology k X 1)) ∧
      -- 5. the unit point and the identity component
      (letI := picardCommGrpObj X.hom P R;
        unitPoint R = Group.unitPoint P.obj ∧
          IsClopen (identityComponent P.obj : Set P.obj.left) ∧
          IsMonHom (identityComponentι P.obj) ∧
          QuasiCompact (identityComponentOver P.obj).hom ∧
          LocallyOfFiniteType (identityComponentOver P.obj).hom ∧
          GeometricallyIrreducible (identityComponentOver P.obj).hom) ∧
      -- 6. field extension
      ∀ (K : Type u) [Field K] [Algebra k K],
        (letI := picardCommGrpObj
            (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            (LocallyNoetherianOver.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K))) P)
            (baseChangeRepresentableBy X.hom
              (Spec.map (CommRingCat.ofHom (algebraMap k K))) P R);
          identityComponent (LocallyNoetherianOver.baseChange
            (Spec.map (CommRingCat.ofHom (algebraMap k K))) P).obj) =
          pullback.fst P.obj.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⁻¹ᵁ
            (letI := picardCommGrpObj X.hom P R; identityComponent P.obj) := by
  obtain ⟨N, i, hi, hiX⟩ := hX.exists_closedImmersion_projectiveSpace
  have hflat := hX.flat
  have hgi := hX.isGeometricallyIntegral
  obtain ⟨Xl, ⟨⟨⟩⟩, Xh⟩ := X
  change Xl ⟶ ProjectiveSpace k (ULift.{u} (Fin (N + 1))) at i
  change i ≫ ProjectiveSpace.toSpec k (ULift.{u} (Fin (N + 1))) = Xh at hiX
  subst hiX
  have e : ULift.{u} (Fin (N + 1)) ≃ Fin (N + 1) := Equiv.ulift
  have h₀ := Strata.fineStrataRepresentableByHQuasiProjective i e
  have : IsProper (i ≫ ProjectiveSpace.toSpec k (ULift.{u} (Fin (N + 1)))) :=
    isProper_comp_toSpec_of_isClosedImmersion i e
  exact ⟨picardScheme h₀, picardSchemeRepresentableBy h₀, inferInstance, inferInstance,
    fun a b => picard_homEquiv_mul _ _ _ a b,
    fun o ho => ⟨⟨picardSchemeNormalizedRepresentableBy h₀ o ho⟩,
      ⟨picardSchemeRigidifiedRepresentableBy h₀ o ho⟩⟩,
    fun _ => ⟨picardSchemeRelativeRepresentableByOfIsSplitEpi h₀⟩,
    fun g => ⟨picardCommGrpObj_baseChange_toGrpObj _ g _ _,
      fun _ e' => ⟨picardSchemeBaseChangeIso h₀ g e'⟩⟩,
    ⟨picardSchemeTangentKernelLinearEquiv h₀⟩, ⟨picardSchemeCotangentSpaceDualLinearEquiv h₀⟩,
    ⟨unitPoint_eq_unitPoint_picardCommGrpObj _ _ _, isClopen_picardIdentityComponent _ _ _,
      isMonHom_picardIdentityComponentι _ _ _, inferInstance, inferInstance, inferInstance⟩,
    fun K _ _ => identityComponent_baseChangeRepresentableBy _ _ _ K⟩

end AlgebraicGeometry.Scheme.OverField.Curve
