/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalPoint.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Local rings at rational points of smooth curves

Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.SmoothCurve`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `080cceb158bce2f0351052e3ba1033435e97f7f61b770cc5ad883b4fb69c66ad`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.RationalPoint
variable {F : Type u} [Field F] {X : Scheme.{u}}

/-- the actual rational
section is a closed immersion; no separation or finite-type input is needed. -/
lemma section_isClosedImmersion (q : RationalPoint F X) :
    IsClosedImmersion q.sectionMap :=
  AlgebraicGeometry.isClosedImmersion_of_comp_eq_id
    q.structureMap q.sectionMap q.section_comp

/-- the point chosen by
the rational section is a closed point of the actual scheme. -/
lemma point_isClosed (q : RationalPoint F X) : IsClosed {q.point} := by
  let := q.section_isClosedImmersion
  have h : Set.range q.sectionMap = {q.point} := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      have hs : s = IsLocalRing.closedPoint F := Subsingleton.elim _ _
      simp [hs, point]
    · intro hx
      exact ⟨IsLocalRing.closedPoint F, Set.mem_singleton_iff.mp hx |>.symm⟩
  rw [← h]
  exact q.sectionMap.isClosedEmbedding.isClosed_range

/-- local finite type
of the actual structure morphism over the field makes the scheme locally Noetherian. -/
lemma scheme_isLocallyNoetherian (q : RationalPoint F X)
    [LocallyOfFiniteType q.structureMap] : IsLocallyNoetherian X :=
  LocallyOfFiniteType.isLocallyNoetherian q.structureMap

/-- local finite type
of the actual structure morphism makes the actual origin stalk Noetherian. -/
lemma localRing_isNoetherianRing (q : RationalPoint F X)
    [LocallyOfFiniteType q.structureMap] : IsNoetherianRing q.localRing := by
  let := q.scheme_isLocallyNoetherian
  infer_instance

/-- smoothness gives
formal smoothness of the actual structure morphism's map at the origin stalk. -/
lemma structureMap_stalkMap_formallySmooth (q : RationalPoint F X)
    [Smooth q.structureMap] : (q.structureMap.stalkMap q.point).hom.FormallySmooth := by
  have h : q.point ∈ q.structureMap.smoothLocus := by
    rw [q.structureMap.smoothLocus_eq_top]
    trivial
  exact h

/-- the canonical
base-field constants map to the actual origin stalk is formally smooth. -/
lemma constants_formallySmooth (q : RationalPoint F X)
    [Smooth q.structureMap] : q.constants.FormallySmooth := by
  change (((fieldStalkIso F (q.structureMap q.point)).inv ≫
    q.structureMap.stalkMap q.point).hom).FormallySmooth
  rw [CommRingCat.hom_comp, RingHom.FormallySmooth.respectsIso.cancel_left_isIso]
  exact q.structureMap_stalkMap_formallySmooth

/-- local finite type
makes the canonical constants map to the actual origin stalk essentially finite type. -/
lemma constants_essFiniteType (q : RationalPoint F X)
    [LocallyOfFiniteType q.structureMap] : q.constants.EssFiniteType := by
  change (((fieldStalkIso F (q.structureMap q.point)).inv ≫
    q.structureMap.stalkMap q.point).hom).EssFiniteType
  rw [CommRingCat.hom_comp, RingHom.EssFiniteType.respectsIso.cancel_left_isIso]
  exact LocallyOfFiniteType.stalkMap q.structureMap q.point

/-- constants in an
actual open's section ring, obtained from the scheme structure morphism. -/
def affineConstants (q : RationalPoint F X) (V : X.Opens) : F →+* Γ(X, V) :=
  ((Scheme.ΓSpecIso (.of F)).inv ≫ q.structureMap.appLE ⊤ V (by simp)).hom

/-- the germ of the
affine constants agrees with the actual origin-stalk constants map. -/
lemma germ_comp_affineConstants (q : RationalPoint F X)
    {V : X.Opens} (hx : q.point ∈ V) :
    (X.presheaf.germ V q.point hx).hom.comp (q.affineConstants V) = q.constants := by
  apply CommRingCat.hom_ext_iff.mp
  change ((Scheme.ΓSpecIso (.of F)).inv ≫
    q.structureMap.appLE ⊤ V _ ≫ X.presheaf.germ V q.point hx) =
    (fieldStalkIso F (q.structureMap q.point)).inv ≫ q.structureMap.stalkMap q.point
  rw [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res,
    ← Scheme.Hom.germ_stalkMap, ← Category.assoc]
  have hg (s : Spec (.of F)) :
      (Scheme.ΓSpecIso (.of F)).inv ≫ (Spec (.of F)).presheaf.germ ⊤ s trivial =
        (fieldStalkIso F s).inv := by
    have he : s = IsLocalRing.closedPoint F := Subsingleton.elim _ _
    subst s
    simp only [fieldStalkIso, TopCat.Presheaf.stalkCongr]
    rw [← ΓSpecIso_hom_stalkClosedPointIso_inv]
    simp
  rw [hg]

/-- smooth relative
dimension `n` supplies an actual standard-smooth affine neighborhood over `F`. -/
lemma exists_standardSmooth_affineNeighborhood (q : RationalPoint F X) (n : ℕ)
    [SmoothOfRelativeDimension n q.structureMap] :
    ∃ (V : X.Opens) (_ : IsAffineOpen V), q.point ∈ V ∧
      RingHom.IsStandardSmoothOfRelativeDimension n (q.affineConstants V) := by
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := n) (f := q.structureMap) q.point
  have hUtop : U = ⊤ := by
    apply top_unique
    intro s _
    have he : q.structureMap q.point ∈ U := e hx
    exact Subsingleton.elim (q.structureMap q.point) s ▸ he
  subst U
  refine ⟨V, hV, hx, ?_⟩
  change RingHom.IsStandardSmoothOfRelativeDimension n
    (((Scheme.ΓSpecIso (.of F)).inv ≫ q.structureMap.appLE ⊤ V _).hom)
  rw [CommRingCat.hom_comp,
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).cancel_left_isIso]
  exact hs

/-- relative
dimension `n` makes the actual origin-stalk differential module free of rank `n`.
The `F`-algebra structure is precisely the canonical constants map. -/
lemma localRing_kaehlerDifferential_free_and_rank (q : RationalPoint F X) (n : ℕ)
    [SmoothOfRelativeDimension n q.structureMap] :
    letI := q.constants.toAlgebra
    Module.Free q.localRing (KaehlerDifferential F q.localRing) ∧
      Module.rank q.localRing (KaehlerDifferential F q.localRing) = n := by
  let := q.constants.toAlgebra
  obtain ⟨V, hV, hx, hs⟩ := q.exists_standardSmooth_affineNeighborhood n
  let A := Γ(X, V)
  let := (q.affineConstants V).toAlgebra
  let : Nontrivial A := (X.presheaf.germ V q.point hx).hom.domain_nontrivial
  let : Algebra A q.localRing := X.presheaf.algebra_section_stalk ⟨q.point, hx⟩
  let : IsScalarTower F A q.localRing :=
    IsScalarTower.of_algebraMap_eq' (q.germ_comp_affineConstants hx).symm
  have : Algebra.IsStandardSmoothOfRelativeDimension n F A := hs
  have : Algebra.IsStandardSmooth F A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : IsLocalization.AtPrime (q.localRing : Type u)
      (hV.primeIdealOf ⟨q.point, hx⟩).asIdeal := hV.isLocalization_stalk ⟨q.point, hx⟩
  have : Algebra.FormallyEtale A q.localRing :=
    Algebra.FormallyEtale.of_isLocalization (hV.primeIdealOf ⟨q.point, hx⟩).asIdeal.primeCompl
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale F A q.localRing
  refine ⟨Module.Free.of_equiv e, ?_⟩
  rw [← e.rank_eq, Module.rank_baseChange,
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n]
  simp

/-- the cotangent
space of the actual origin stalk has dimension `n` over its actual residue field.
Only the actual smooth relative-dimension hypothesis is supplied. -/
lemma localRing_finrank_cotangentSpace (q : RationalPoint F X) (n : ℕ)
    [SmoothOfRelativeDimension n q.structureMap] :
    Module.finrank (IsLocalRing.ResidueField q.localRing)
      (IsLocalRing.CotangentSpace q.localRing) = n := by
  let R := (q.localRing : Type u)
  let K := IsLocalRing.ResidueField R
  let := q.constants.toAlgebra
  let : Algebra F K := Ideal.Quotient.algebra F (I := IsLocalRing.maximalIdeal R)
  have : IsScalarTower F R K := Ideal.Quotient.isScalarTower F R (IsLocalRing.maximalIdeal R)
  have : Smooth q.structureMap := SmoothOfRelativeDimension.smooth n q.structureMap
  have : Algebra.FormallySmooth F R := q.constants_formallySmooth
  let eK : K ≃ₐ[F] F :=
    { q.residueEquiv with commutes' := by intro a; exact q.residueEquiv_constants a }
  have : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_equiv eK.symm
  have hr : Function.Surjective (algebraMap R K) := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (algebraMap R K) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.ker_residue
  let eI := Ideal.Cotangent.equivOfEq (IsLocalRing.maximalIdeal R)
    (RingHom.ker (algebraMap R K)) hker.symm
  let c := (KaehlerDifferential.kerCotangentToTensor F R K).comp eI.toLinearMap
  let cK := c.extendScalarsOfSurjective hr
  have hc : Function.Bijective cK := by
    constructor
    · exact ((Algebra.FormallySmooth.kerCotangentToTensor_injective_iff hr).mpr
        inferInstance).comp eI.injective
    · have hs : Function.Surjective (KaehlerDifferential.kerCotangentToTensor F R K) := by
        intro x
        apply (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange F R K hr x).mp
        exact Subsingleton.elim _ _
      exact hs.comp eI.surjective
  let eC := LinearEquiv.ofBijective cK hc
  have hΩ := q.localRing_kaehlerDifferential_free_and_rank n
  let := hΩ.1
  rw [Module.finrank, eC.rank_eq, Module.rank_baseChange, hΩ.2]
  simp

/-- the actual
origin stalk of a smooth relative-dimension-one scheme is not a field. -/
lemma localRing_not_isField_of_smoothOfRelativeDimension_one (q : RationalPoint F X)
    [SmoothOfRelativeDimension 1 q.structureMap] : ¬ IsField q.localRing := by
  have : Smooth q.structureMap := SmoothOfRelativeDimension.smooth 1 q.structureMap
  have : IsNoetherianRing q.localRing := q.localRing_isNoetherianRing
  intro hf
  have h := IsLocalRing.finrank_cotangentSpace_eq_zero_iff.mpr hf
  rw [q.localRing_finrank_cotangentSpace 1] at h
  exact one_ne_zero h

/-- smooth relative dimension one and the explicit domain
hypothesis on the actual origin stalk imply it is a DVR. Integrality of `X`
supplies the domain instance; regularity and dimension one are not inputs. -/
lemma localRing_isDiscreteValuationRing_of_smoothOfRelativeDimension_one (q : RationalPoint F X)
    [SmoothOfRelativeDimension 1 q.structureMap] [IsDomain q.localRing] :
    IsDiscreteValuationRing q.localRing := by
  have : Smooth q.structureMap := SmoothOfRelativeDimension.smooth 1 q.structureMap
  have : IsNoetherianRing q.localRing := q.localRing_isNoetherianRing
  exact ((IsDiscreteValuationRing.TFAE q.localRing
    q.localRing_not_isField_of_smoothOfRelativeDimension_one).out 6 1).mp
      (q.localRing_finrank_cotangentSpace 1)

/-- with the
explicit actual-stalk domain hypothesis, smooth relative dimension one implies
that the actual origin stalk has Krull dimension one. -/
lemma localRing_ringKrullDim_eq_one_of_smoothOfRelativeDimension_one (q : RationalPoint F X)
    [SmoothOfRelativeDimension 1 q.structureMap] [IsDomain q.localRing] :
    ringKrullDim q.localRing = 1 := by
  have := q.localRing_isDiscreteValuationRing_of_smoothOfRelativeDimension_one
  exact IsDiscreteValuationRing.ringKrullDim_eq_one q.localRing

/-- with the
explicit actual-stalk domain hypothesis, smooth relative dimension one implies
regularity of the actual origin stalk. -/
lemma localRing_isRegularLocalRing_of_smoothOfRelativeDimension_one (q : RationalPoint F X)
    [SmoothOfRelativeDimension 1 q.structureMap] [IsDomain q.localRing] :
    IsRegularLocalRing q.localRing := by
  have := q.localRing_isDiscreteValuationRing_of_smoothOfRelativeDimension_one
  infer_instance

/-- for an actual integral scheme smooth of relative
dimension one over `F`, the actual rational-origin stalk is regular of Krull
dimension one and a DVR. The sole extra global input is `IsIntegral X`. -/
lemma localRing_regular_dimension_one_and_dvr (q : RationalPoint F X) [IsIntegral X]
    [SmoothOfRelativeDimension 1 q.structureMap] :
    IsRegularLocalRing q.localRing ∧ ringKrullDim q.localRing = 1 ∧
      IsDiscreteValuationRing q.localRing := by
  exact ⟨q.localRing_isRegularLocalRing_of_smoothOfRelativeDimension_one,
    q.localRing_ringKrullDim_eq_one_of_smoothOfRelativeDimension_one,
    q.localRing_isDiscreteValuationRing_of_smoothOfRelativeDimension_one⟩

end AlgebraicGeometry.Scheme.RationalPoint
