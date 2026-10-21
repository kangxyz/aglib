/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Projectivity.Embedding
public import Aglib.AlgebraicGeometry.Curves.SmoothGeometry
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Properties
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Gluing
public import Aglib.AlgebraicGeometry.Morphisms.GeometricallyIntegral.Open
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Aglib.RingTheory.Spectrum.Prime.BasicOpenUnit
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Literal base-change comparisons under shrinking

Restricting a family to an open containing the image of its specified field
point preserves its original literal pullback. The comparison is an
isomorphism in the over category, so it retains the structural map and can be
composed with the original model comparison.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace AlgebraicGeometry.Scheme

/-- The literal pullback of the restricted family is the literal pullback of
the original family whenever the chosen base map factors through the open. -/
def morphismRestrictBaseChangeIso {X Y T : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (g : T ⟶ Y) (gU : T ⟶ U) (hg : gU ≫ U.ι = g) :
    (Over.pullback gU).obj (Over.mk (f ∣_ U)) ≅
      (Over.pullback g).obj (Over.mk f) := by
  have h : IsPullback (pullback.fst (f ∣_ U) gU ≫ (f ⁻¹ᵁ U).ι)
      (pullback.snd (f ∣_ U) gU) f g := by
    simpa only [hg] using
      (IsPullback.of_hasPullback (f ∣_ U) gU).paste_horiz
        (isPullback_morphismRestrict f U).flip
  exact Over.isoMk h.isoPullback h.isoPullback_hom_snd

/-- The comparison keeps the original map to the total space. -/
@[reassoc]
theorem morphismRestrictBaseChangeIso_hom_fst {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens) (g : T ⟶ Y) (gU : T ⟶ U) (hg : gU ≫ U.ι = g) :
    (morphismRestrictBaseChangeIso f U g gU hg).hom.left ≫ pullback.fst f g =
      pullback.fst (f ∣_ U) gU ≫ (f ⁻¹ᵁ U).ι := by
  exact IsPullback.isoPullback_hom_fst _

/-- A dominant point with a one-point source is the actual generic point. -/
theorem dominant_subsingleton_apply_eq_genericPoint {T Y : Scheme.{u}}
    [Subsingleton T] [IrreducibleSpace Y] (g : T ⟶ Y) [IsDominant g] (x : T) :
    g x = genericPoint Y := by
  have hrange : Set.range g = {g x} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact congrArg g (Subsingleton.elim z x)
    · rintro rfl
      exact ⟨x, rfl⟩
  refine IsGenericPoint.eq ?_ (genericPoint_spec Y)
  change closure ({g x} : Set Y) = Set.univ
  rw [← hrange]
  exact g.denseRange.closure_range

/-- A specified dominant field point factors through every open neighbourhood
of the actual generic point. -/
def liftDominantFieldPoint {Y : Scheme.{u}} [IrreducibleSpace Y]
    {K : Type u} [Field K] (g : Spec (CommRingCat.of K) ⟶ Y) [IsDominant g]
    (U : Y.Opens) (hU : genericPoint Y ∈ U) : Spec (CommRingCat.of K) ⟶ U :=
  IsOpenImmersion.lift U.ι g (by
    rintro y ⟨x, rfl⟩
    rw [Opens.range_ι]
    exact (dominant_subsingleton_apply_eq_genericPoint g x).symm ▸ hU)

@[reassoc (attr := simp)]
theorem liftDominantFieldPoint_ι {Y : Scheme.{u}} [IrreducibleSpace Y]
    {K : Type u} [Field K] (g : Spec (CommRingCat.of K) ⟶ Y) [IsDominant g]
    (U : Y.Opens) (hU : genericPoint Y ∈ U) : liftDominantFieldPoint g U hU ≫ U.ι = g :=
  IsOpenImmersion.lift_fac _ _ _

/-- Shrinking along a generic open preserves the supplied original-field
model comparison, as an isomorphism over that same original field. -/
def restrictModelComparison {X Y : Scheme.{u}} [IrreducibleSpace Y]
    {K : Type u} [Field K] (f : X ⟶ Y)
    (g : Spec (CommRingCat.of K) ⟶ Y) [IsDominant g]
    (C : Over (Spec (CommRingCat.of K)))
    (e : (Over.pullback g).obj (Over.mk f) ≅ C)
    (U : Y.Opens) (hU : genericPoint Y ∈ U) :
    (Over.pullback (liftDominantFieldPoint g U hU)).obj (Over.mk (f ∣_ U)) ≅ C :=
  morphismRestrictBaseChangeIso f U g (liftDominantFieldPoint g U hU)
    (liftDominantFieldPoint_ι g U hU) ≪≫ e

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProjectiveSpace

/-- An actual affine closed chart descends to a closed chart over a finite
integer subalgebra, with its original coordinates and prescribed constants. -/
theorem exists_closed_chart_model
    {K B : Type u} [Field K] [CommRing B] [Algebra K B]
    [Algebra.FinitePresentation K B] (ι : Type u) [Finite ι] (i : ι)
    (φ : coordinateRing K ι i →+* B) (hφsurj : Function.Surjective φ)
    (hφ : ∀ r, φ (coordinateRingCoefficient K ι i r) = algebraMap K B r)
    (extra : Finset K) :
    ∃ (A : Subalgebra ℤ K) (D : Type u) (_ : CommRing D) (_ : Algebra A D),
      A.FG ∧ Algebra.FinitePresentation A D ∧ (∀ r ∈ extra, r ∈ A) ∧
      ∃ (e : K ⊗[A] D ≃ₐ[K] B) (ψ : coordinateRing A ι i →+* D),
        Function.Surjective ψ ∧
        (∀ r, ψ (coordinateRingCoefficient A ι i r) = algebraMap A D r) ∧
        (e.toRingHom.comp
          (Algebra.TensorProduct.includeRight : D →ₐ[A] K ⊗[A] D).toRingHom).comp ψ =
          φ.comp (coordinateRingMap (algebraMap A K) ι i) := by
  classical
  let p : MvPolynomial {j : ι // j ≠ i} K →ₐ[K] B :=
    { __ := φ.comp (polynomialToCoordinateRing K ι i)
      commutes' := fun r => by simpa using hφ r }
  have hp : Function.Surjective p :=
    hφsurj.comp (coordinateRingEquivPolynomial K ι i).symm.surjective
  let G : Algebra.Generators K B {j : ι // j ≠ i} :=
    Algebra.Generators.ofSurjective (fun j => p (MvPolynomial.X j)) (by
      convert hp using 1
      congr 1
      ext j
      simp)
  obtain ⟨m, v, hv⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    G.fg_ker_of_finitePresentation
  let P : Algebra.Presentation K B {j : ι // j ≠ i} (Fin m) :=
    { __ := G
      relation := v
      span_range_relation_eq_ker := hv }
  let A := Algebra.adjoin ℤ (P.coeffs ∪ (extra : Set K))
  have hA : A.FG :=
    ⟨(P.finite_coeffs.union extra.finite_toSet).toFinset, by simp [A]⟩
  let : P.HasCoeffs A := ⟨fun r hr =>
    ⟨⟨r, Algebra.subset_adjoin (Or.inl hr)⟩, rfl⟩⟩
  let D := P.ModelOfHasCoeffs A
  let e : K ⊗[A] D ≃ₐ[K] B := P.tensorModelOfHasCoeffsEquiv A
  let ψ : coordinateRing A ι i →+* D :=
    (Ideal.Quotient.mk _).comp (coordinateRingToPolynomial A ι i)
  let mD := e.toRingHom.comp
    (Algebra.TensorProduct.includeRight : D →ₐ[A] K ⊗[A] D).toRingHom
  have hm (r : A) : mD (algebraMap A D r) = algebraMap K B (algebraMap A K r) :=
    ((e.restrictScalars A).toAlgHom.comp
      (Algebra.TensorProduct.includeRight : D →ₐ[A] K ⊗[A] D)).commutes r
  have hψ (r : A) : ψ (coordinateRingCoefficient A ι i r) = algebraMap A D r := by
    change Ideal.Quotient.mk _
      (coordinateRingToPolynomial A ι i (coordinateRingCoefficient A ι i r)) = _
    rw [coordinateRingToPolynomial_coefficient]
    rfl
  have hψsurj : Function.Surjective ψ :=
    Ideal.Quotient.mk_surjective.comp (coordinateRingEquivPolynomial A ι i).surjective
  refine ⟨A, D, inferInstance, inferInstance, hA, inferInstance,
    fun r hr => Algebra.subset_adjoin (Or.inr hr), e, ψ, hψsurj, hψ, ?_⟩
  have H : (mD.comp ψ).comp (polynomialToCoordinateRing A ι i) =
      (φ.comp (coordinateRingMap (algebraMap A K) ι i)).comp
        (polynomialToCoordinateRing A ι i) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, polynomialToCoordinateRing_C, hψ,
        coordinateRingMap_coefficient, hm, hφ]
    · intro j
      simp only [RingHom.comp_apply, polynomialToCoordinateRing_X, coordinateRingMap_ratio]
      change e (1 ⊗ₜ[A] ψ (coordinateRatio A ι i j.1)) = _
      change e (1 ⊗ₜ[A] Ideal.Quotient.mk _
        (coordinateRingToPolynomial A ι i (coordinateRatio A ι i j.1))) = _
      rw [coordinateRingToPolynomial_ratio]
      change P.tensorModelOfHasCoeffsEquiv A
        (1 ⊗ₜ[A] (Ideal.Quotient.mk _ (MvPolynomial.X j))) = _
      simp only [Algebra.Presentation.tensorModelOfHasCoeffsEquiv_tmul,
        map_one, one_mul, MvPolynomial.aeval_X]
      change p (MvPolynomial.X j) = _
      simp [p]
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := (coordinateRingEquivPolynomial A ι i).symm.surjective z
  exact RingHom.congr_fun H p

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.ProjectiveSpace

/-- One actual schematically dense affine closed chart constructs a proper
finitely presented finite-base model of the original projective scheme. -/
theorem exists_proper_model_of_dense_closed_chart
    {K B : Type u} [Field K] [CommRing B] [Algebra K B]
    [Algebra.FinitePresentation K B]
    (C : Scheme.OverField.FScheme K) (ι : Type u) [Finite ι] (i : ι)
    (ιC : C.left ⟶ ProjectiveSpace K ι) [IsClosedImmersion ιC]
    (hC : ιC ≫ toSpec K ι = C.hom)
    (j : Spec (.of B) ⟶ C.left) [IsSchemeTheoreticallyDominant j]
    (hj : j ≫ C.hom = Spec.map (CommRingCat.ofHom (algebraMap K B)))
    (φ : coordinateRing K ι i →+* B) (hφsurj : Function.Surjective φ)
    (hφ : ∀ r, φ (coordinateRingCoefficient K ι i r) = algebraMap K B r)
    (hchart : j ≫ ιC = Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule ι K) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X K i) Nat.zero_lt_one)
    (extra : Finset K) :
    ∃ (A : Subalgebra ℤ K) (X : Scheme.{u}) (f : X ⟶ Spec (.of A)),
      A.FG ∧ (∀ r ∈ extra, r ∈ A) ∧ IsProper f ∧ LocallyOfFinitePresentation f ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A K)))).obj
        (Over.mk f) ≅ C) ∧
      ∃ (D : Type u) (_ : CommRing D) (_ : Algebra A D) (a : Spec (.of D) ⟶ X),
        Algebra.FinitePresentation A D ∧ IsOpenImmersion a ∧
        a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A D)) ∧
        Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A K)))).obj
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A D)))) ≅
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K B)))) := by
  obtain ⟨A, D, hD, hAD, hA, hfp, hextra, e, ψ, hψsurj, hψ, he⟩ :=
    exists_closed_chart_model ι i φ hφsurj hφ extra
  let := hD
  let := hAD
  let := hfp
  let : IsNoetherianRing A := isNoetherianRing_of_fg hA
  let : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
  let : IsScalarTower A (FractionRing A) K := FractionRing.isScalarTower_liftAlgebra A K
  let : Module.Flat A (FractionRing A) := IsLocalization.flat _ (nonZeroDivisors A)
  let : Module.Free (FractionRing A) K :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace (FractionRing A) K)
  let : Module.Flat (FractionRing A) K :=
    Module.Flat.of_free (R := FractionRing A) (M := K)
  let : Module.Flat A K := Module.Flat.trans A (FractionRing A) K
  let g := Spec.map (CommRingCat.ofHom (algebraMap A K))
  let : Flat g := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let a := Spec.map (CommRingCat.ofHom ψ) ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule ι A) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X A i) Nat.zero_lt_one
  let p := toSpec A ι
  let fD := Spec.map (CommRingCat.ofHom (algebraMap A D))
  have ha : a ≫ p = fD := by
    dsimp only [a, p, fD]
    rw [Category.assoc, coordinateChart_toSpec, ← Spec.map_comp]
    apply congrArg Spec.map
    ext r
    exact hψ r
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom ψ)) :=
    IsClosedImmersion.spec_of_surjective _ hψsurj
  let : IsImmersion a := by
    dsimp only [a]
    infer_instance
  let : QuasiCompact a := inferInstance
  let q := a.imageι ≫ p
  let aX := a.toImage
  let iX := Spec.map (CommRingCat.ofHom (e.toRingHom.comp
    (Algebra.TensorProduct.includeRight : D →ₐ[A] K ⊗[A] D).toRingHom))
  let fK := Spec.map (CommRingCat.ofHom (algebraMap K B))
  have HX : IsPullback iX fK fD g := Scheme.isPullback_affineModelMap A K D B e
  let iP := map (algebraMap A K) ι
  let pK := toSpec K ι
  have HP : IsPullback iP pK p g := isPullback_map (algebraMap A K) ι
  let aK := j ≫ ιC
  have haK : iX ≫ a = aK ≫ iP := by
    dsimp only [iX, a, aK, iP]
    rw [hchart, Category.assoc, coordinateRingMap_awayι, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc]
    congr 2
    exact CommRingCat.hom_ext he
  have hb : aK ≫ pK = fK := by
    dsimp only [aK, pK]
    rw [Category.assoc, hC]
    exact hj
  let E := Scheme.imageModelBaseChangeIsoOfSchematicFactor fD p a ha g iX fK HX
    iP pK HP aK haK hb j ιC rfl C.hom hC
  refine ⟨A, a.image, q, hA, hextra, inferInstance, inferInstance, ⟨E⟩,
    D, hD, hAD, aX, hfp, inferInstance, ?_, ?_⟩
  · simpa only [aX, q, Category.assoc, Scheme.Hom.toImage_imageι_assoc] using ha
  · exact ⟨Over.isoMk HX.isoPullback.symm HX.isoPullback_inv_snd⟩

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.OverField.Curve

/-- The original smooth proper geometrically connected field curve has an
actual proper finitely presented model over a finite integral integer
subalgebra, containing any specified finite set of base constants. -/
theorem Properties.exists_proper_finite_base_model
    {K : Type u} [Field K] {C : FScheme K} (hC : Properties C) (extra : Finset K) :
    ∃ (A : Subalgebra ℤ K) (X : Scheme.{u}) (f : X ⟶ Spec (.of A)),
      A.FG ∧ (∀ r ∈ extra, r ∈ A) ∧ IsProper f ∧ LocallyOfFinitePresentation f ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A K)))).obj
        (Over.mk f) ≅ C) := by
  obtain ⟨n, ιC, hιC, hbase⟩ := Projectivity.curveProperties_exists_projectiveEmbedding hC
  let := hιC
  let : IsIntegral C.left := hC.isIntegral
  let : SmoothOfRelativeDimension 1 C.hom := hC.smooth
  let : Smooth C.hom := SmoothOfRelativeDimension.smooth 1 C.hom
  let ι := ULift.{u} (Fin (n + 1))
  let cover := ProjectiveSpace.coordinateAffineOpenCover K ι
  let x := Nonempty.some (inferInstance : Nonempty C.left)
  let i : ι := cover.idx (ιC x)
  let c := Proj.awayι (MvPolynomial.homogeneousSubmodule ι K) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X K i) Nat.zero_lt_one
  let W := pullback ιC c
  let a := pullback.fst ιC c
  let b := pullback.snd ιC c
  have hx : x ∈ Set.range a :=
    (Scheme.Pullback.range_fst ιC c).ge (cover.covers (ιC x))
  obtain ⟨w, hw⟩ := hx
  let : Nonempty W := ⟨w⟩
  let : IsAffine W := isAffine_of_isAffineHom b
  let : IsDominant a := ⟨a.isOpenMap.isOpen_range.dense ⟨a w, w, rfl⟩⟩
  let j : Spec Γ(W, ⊤) ⟶ C.left := W.isoSpec.inv ≫ a
  let : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isDominant j
  obtain ⟨φ, hφmap⟩ := Spec.map_surjective (W.isoSpec.inv ≫ b)
  let : IsClosedImmersion (Spec.map φ) := by
    rw [hφmap]
    infer_instance
  have hφsurj : Function.Surjective φ := by
    have hΓ := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map φ)).2
    have hΓ' : Function.Surjective ((Scheme.ΓSpecIso _).hom ≫ φ) := by
      rw [← Scheme.ΓSpecIso_naturality]
      exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).2.comp hΓ
    exact Function.Surjective.of_comp hΓ'
  let B := Γ(W, ⊤)
  let β : K →+* B := φ.hom.comp (ProjectiveSpace.coordinateRingCoefficient K ι i)
  let : Algebra K B := β.toAlgebra
  have hchart : j ≫ ιC = Spec.map φ ≫ c := by
    dsimp only [j, a, b]
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← hφmap]
  have hj : j ≫ C.hom = Spec.map (CommRingCat.ofHom (algebraMap K B)) := by
    rw [← hbase, ← Category.assoc, hchart, Category.assoc]
    dsimp only [c]
    rw [ProjectiveSpace.coordinateChart_toSpec, ← Spec.map_comp]
    apply congrArg Spec.map
    ext r
    rfl
  let : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap K B))) := by
    rw [← hj]
    infer_instance
  let : Algebra.FinitePresentation K B :=
    RingHom.finitePresentation_algebraMap.mp
      ((LocallyOfFinitePresentation.SpecMap_iff
        (CommRingCat.ofHom (algebraMap K B))).mp inferInstance)
  obtain ⟨A, X, f, hA, hextra, hp, hfp, e, _⟩ :=
    ProjectiveSpace.exists_proper_model_of_dense_closed_chart C ι i ιC hbase j hj
      φ.hom hφsurj (fun _ => rfl) hchart extra
  exact ⟨A, X, f, hA, hextra, hp, hfp, e⟩

end AlgebraicGeometry.Scheme.OverField.Curve

namespace AlgebraicGeometry.Scheme

/-- An injective ring map induces a dominant morphism on spectra. -/
theorem specMap_dominant_of_injective {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) :
    IsDominant (Spec.map (CommRingCat.ofHom φ)) := by
  constructor
  change DenseRange (PrimeSpectrum.comap φ)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot φ).mp hφ]
  exact bot_le

/-- An actual proper finitely presented model over an integral affine base
can be shrunk to the relative dimension of its specified smooth field fibre.
The field embedding need not be algebraic over the fraction field. -/
theorem exists_generic_open_smoothOfRelativeDimension_of_fieldBaseChange
    {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [FaithfulSMul R K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] [LocallyOfFinitePresentation f]
    (n : ℕ)
    [SmoothOfRelativeDimension n
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    ∃ U : (Spec (.of R)).Opens, genericPoint (Spec (.of R)) ∈ U ∧
      U ≠ ⊥ ∧ SmoothOfRelativeDimension n (f ∣_ U) := by
  let F := FractionRing R
  let : Algebra F K := FractionRing.liftAlgebra R K
  let : IsScalarTower R F K := FractionRing.isScalarTower_liftAlgebra R K
  let gF := Spec.map (CommRingCat.ofHom (algebraMap R F))
  let gK := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let t := Spec.map (CommRingCat.ofHom (algebraMap F K))
  have ht : t ≫ gF = gK := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    ext r
    exact (IsScalarTower.algebraMap_apply R F K r).symm
  let qF := pullback.snd f gF
  let qK := pullback.snd f gK
  let E := pullbackLeftPullbackSndIso f gF t ≪≫ pullback.congrHom rfl ht
  have hE : E.hom ≫ qK = pullback.snd qF t := by
    simp [E, qF, qK, Category.assoc]
  let : SmoothOfRelativeDimension n qK :=
    inferInstanceAs (SmoothOfRelativeDimension n
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
  let : Smooth qK := SmoothOfRelativeDimension.smooth n qK
  let : Smooth (pullback.snd qF t) := by
    rw [← hE]
    infer_instance
  let : Surjective t := ⟨Function.surjective_to_subsingleton t⟩
  let : Flat t := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let : Smooth qF := MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := qF) (g := t)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  let : Module.Flat R F := IsLocalization.flat F (nonZeroDivisors R)
  let : Flat gF := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let : IsPreimmersion gF := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  let s := gF (Nonempty.some (inferInstance : Nonempty (Spec (.of F))))
  obtain ⟨U, hs, hsm⟩ := exists_open_smooth_of_isProper_of_flat_preimmersion f gF s
    ⟨Nonempty.some (inferInstance : Nonempty (Spec (.of F))), rfl⟩
  have hη : genericPoint (Spec (.of R)) ∈ U :=
    (genericPoint_specializes s).mem_open U.isOpen hs
  let : Smooth (f ∣_ U) := hsm
  let : IsDominant gK := specMap_dominant_of_injective _
    (FaithfulSMul.algebraMap_injective R K)
  let gU := liftDominantFieldPoint gK U hη
  have hgU : gU ≫ U.ι = gK := liftDominantFieldPoint_ι gK U hη
  let : IsDominant (gU ≫ U.ι) := by
    rw [hgU]
    infer_instance
  let : IsDominant gU := IsDominant.of_comp_of_isOpenImmersion gU U.ι
  let EU := morphismRestrictBaseChangeIso f U gK gU hgU
  let : SmoothOfRelativeDimension n (pullback.snd (f ∣_ U) gU) := by
    have hEU : EU.hom.left ≫ qK = pullback.snd (f ∣_ U) gU := EU.hom.w
    rw [← hEU]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @SmoothOfRelativeDimension n) EU.hom.left qK).mpr inferInstance
  exact ⟨U, hη, U.ne_bot_iff_nonempty.mpr ⟨s, hs⟩,
    smoothOfRelativeDimension_of_dominant_fieldBaseChange (f ∣_ U) gU n⟩

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- A generic open of the spectrum of a finite integer subalgebra contains
the image of a larger finite integer subalgebra. Adjoining one inverse keeps
all original coefficients and the same ambient field. -/
theorem exists_fg_subalgebra_map_into_generic_open
    {K : Type u} [Field K] (A : Subalgebra ℤ K) (hA : A.FG)
    (U : (Spec (.of A)).Opens) (hU : genericPoint (Spec (.of A)) ∈ U) :
    ∃ (S : Subalgebra ℤ K) (hAS : A ≤ S), S.FG ∧
      Set.range (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hAS).toRingHom)) ⊆ U := by
  classical
  let g := Spec.map (CommRingCat.ofHom (algebraMap A K))
  let : IsDominant g := specMap_dominant_of_injective _ Subtype.val_injective
  let y : Spec (.of K) := ⟨⊥, inferInstance⟩
  have hy : g y ∈ U := (dominant_subsingleton_apply_eq_genericPoint g y).symm ▸ hU
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens hy
  have hr0 : (r : K) ≠ 0 := by
    change ¬ (algebraMap A K r) ∈ (⊥ : Ideal K) at hr
    change algebraMap A K r ≠ 0
    simpa only [Ideal.mem_bot] using hr
  let S := A ⊔ Algebra.adjoin ℤ ({(r : K)⁻¹} : Set K)
  have hAS : A ≤ S := le_sup_left
  have hS : S.FG := hA.sup (by
    simpa only [Finset.coe_singleton] using
      (Subalgebra.fg_adjoin_finset (R := ℤ) ({(r : K)⁻¹} : Finset K)))
  let φ := (Subalgebra.inclusion hAS).toRingHom
  have hmem : (r : K)⁻¹ ∈ S :=
    (show Algebra.adjoin ℤ ({(r : K)⁻¹} : Set K) ≤ S from le_sup_right)
      (Algebra.subset_adjoin (by simp))
  have hunit : IsUnit (φ r) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨(r : K)⁻¹, hmem⟩, ?_⟩
    apply Subtype.ext
    exact mul_inv_cancel₀ hr0
  refine ⟨S, hAS, hS, ?_⟩
  rintro z ⟨y, rfl⟩
  apply hsub
  change y ∈ PrimeSpectrum.basicOpen (φ r)
  rw [PrimeSpectrum.basicOpen_unit (φ r) hunit]
  trivial

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- A geometrically integral specified field fibre of a proper smooth
relative curve supplies a generic geometrically integral neighbourhood,
without assuming geometric integrality of the original residue-field fibre. -/
theorem exists_generic_open_geometricallyIntegral_of_fieldBaseChange
    {X Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {K : Type u} [Field K] (f : X ⟶ Y) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (g : Spec (.of K) ⟶ Y) [IsDominant g]
    [GeometricallyIntegral (pullback.snd f g)] :
    ∃ U : Y.Opens, genericPoint Y ∈ U ∧ U ≠ ⊥ ∧ GeometricallyIntegral (f ∣_ U) := by
  obtain ⟨⟨y, φ⟩, hφ⟩ := (Scheme.SpecToEquivOfField _ _).symm.surjective g
  have hfac : Spec.map φ ≫ Y.fromSpecResidueField y = g := by
    simpa only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk] using hφ
  have hy : y = genericPoint Y := by
    let z := Nonempty.some (inferInstance : Nonempty (Spec (.of K)))
    have hpoint := congrArg (fun q : Spec (.of K) ⟶ Y => q z) hfac
    have hpoint' : y = g z := by simpa only [Scheme.Hom.comp_apply,
      Scheme.fromSpecResidueField_apply] using hpoint
    exact hpoint'.trans (dominant_subsingleton_apply_eq_genericPoint g z)
  subst y
  let q := f.fiberToSpecResidueField (genericPoint Y)
  let : Algebra (Y.residueField (genericPoint Y)) K := φ.hom.toAlgebra
  let E := pullbackLeftPullbackSndIso f (Y.fromSpecResidueField (genericPoint Y))
      (Spec.map φ) ≪≫ pullback.congrHom rfl hfac
  have hE : E.hom ≫ pullback.snd f g = pullback.snd q (Spec.map φ) := by
    simp [E, q, Scheme.Hom.fiberToSpecResidueField, Category.assoc]
  let : GeometricallyIntegral (pullback.snd q (Spec.map φ)) := by
    rw [← hE]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIntegral)
      E.hom (pullback.snd f g)).mpr inferInstance
  let : IsProper q := MorphismProperty.pullback_snd _ _ inferInstance
  let : SmoothOfRelativeDimension 1 q := MorphismProperty.pullback_snd _ _ inferInstance
  let Z : OverField.FScheme (Y.residueField (genericPoint Y)) := Over.mk q
  let : GeometricallyIntegral (Cohomology.fieldBaseChange K Z).hom := by
    change GeometricallyIntegral (pullback.snd q (Spec.map φ))
    infer_instance
  let : IsProper Z.hom := inferInstanceAs (IsProper q)
  let : SmoothOfRelativeDimension 1 Z.hom :=
    inferInstanceAs (SmoothOfRelativeDimension 1 q)
  let : GeometricallyIntegral q :=
    geometricallyIntegral_of_smoothProper_of_fieldBaseChange (K := K) Z
  let : GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint Y)) :=
    inferInstanceAs (GeometricallyIntegral q)
  obtain ⟨U, hU, hne, hgeo, _⟩ := exists_generic_open_geometricallyIntegral_of_smoothProper f
  exact ⟨U, hU, hne, hgeo⟩

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- A property on an actual open pullback of a family is realized after
extension to a larger finite integer subalgebra, preserving the specified
literal comparison with the original field scheme. -/
theorem exists_fg_baseChange_property_of_open
    {K : Type u} [Field K] (A : Subalgebra ℤ K) (hA : A.FG)
    {X T XT : Scheme.{u}} (f : X ⟶ Spec (.of A)) (j : T ⟶ Spec (.of A))
    [IsOpenImmersion j] [Nonempty T]
    (a : XT ⟶ X) (b : XT ⟶ T) (H : IsPullback a b f j)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] [P.RespectsIso]
    (hP : P b) (C : Over (Spec (.of K)))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A K)))).obj
      (Over.mk f) ≅ C) :
    ∃ (S : Subalgebra ℤ K) (hAS : A ≤ S), S.FG ∧
      P (pullback.snd f (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hAS).toRingHom))) ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap S K)))).obj
        (Over.mk (pullback.snd f
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hAS).toRingHom)))) ≅ C) := by
  let t := Nonempty.some (inferInstance : Nonempty T)
  have hη : genericPoint (Spec (.of A)) ∈ j.opensRange :=
    (genericPoint_specializes (j t)).mem_open j.opensRange.isOpen ⟨t, rfl⟩
  obtain ⟨S, hAS, hS, hrange⟩ := exists_fg_subalgebra_map_into_generic_open A hA j.opensRange hη
  let φ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hAS).toRingHom)
  let l := IsOpenImmersion.lift j φ hrange
  have hl : l ≫ j = φ := IsOpenImmersion.lift_fac _ _ _
  let q := pullback.snd f φ
  have HT : IsPullback (pullback.fst b l ≫ a) (pullback.snd b l) f φ := by
    simpa only [hl] using (IsPullback.of_hasPullback b l).paste_horiz H
  have hb : P (pullback.snd b l) := MorphismProperty.pullback_snd (P := P) _ _ hP
  have hq : P q := by
    rw [← HT.isoPullback_hom_snd] at hb
    exact (MorphismProperty.cancel_left_of_respectsIso (P := P) HT.isoPullback.hom q).mp hb
  let gS := Spec.map (CommRingCat.ofHom (algebraMap S K))
  have hcomp : gS ≫ φ = Spec.map (CommRingCat.ofHom (algebraMap A K)) := by
    rw [← Spec.map_comp]
    rfl
  let E' : pullback q gS ≅
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap A K))) :=
    pullbackLeftPullbackSndIso f φ gS ≪≫ pullback.congrHom rfl hcomp
  let E : (Over.pullback gS).obj (Over.mk q) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A K)))).obj (Over.mk f) :=
    Over.isoMk E' (by simp [E', q, Category.assoc])
  exact ⟨S, hAS, hS, hq, ⟨E ≪≫ e⟩⟩

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.OverField.Curve

/-- Construct an actual proper smooth geometrically integral relative curve
over a finite integral integer subalgebra of the original field. The result
contains the prescribed finite constants and recovers the original curve by
the literal field pullback, with its original structural map. -/
theorem Properties.exists_finite_base_model
    {K : Type u} [Field K] {C : FScheme K} (hC : Properties C) (extra : Finset K) :
    ∃ (A : Subalgebra ℤ K) (X : Scheme.{u}) (f : X ⟶ Spec (.of A)),
      A.FG ∧ (∀ r ∈ extra, r ∈ A) ∧ IsProper f ∧ SmoothOfRelativeDimension 1 f ∧
      GeometricallyIntegral f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧
      QuasiCompact f ∧ QuasiSeparated f ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A K)))).obj
        (Over.mk f) ≅ C) := by
  obtain ⟨A, X, f, hA, hextra, hproper, hfp, ⟨e⟩⟩ :=
    hC.exists_proper_finite_base_model extra
  let := hproper
  let := hfp
  let : IsNoetherianRing A := isNoetherianRing_of_fg hA
  let g := Spec.map (CommRingCat.ofHom (algebraMap A K))
  let : IsDominant g := Scheme.specMap_dominant_of_injective _ Subtype.val_injective
  let : SmoothOfRelativeDimension 1 (pullback.snd f g) := by
    have he : e.hom.left ≫ C.hom = pullback.snd f g := e.hom.w
    rw [← he]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @SmoothOfRelativeDimension 1) e.hom.left C.hom).mpr hC.smooth
  obtain ⟨U, hηU, hUne, hsmU⟩ :=
    Scheme.exists_generic_open_smoothOfRelativeDimension_of_fieldBaseChange (K := K) f 1
  let : SmoothOfRelativeDimension 1 (f ∣_ U) := hsmU
  let : Nonempty U := ⟨⟨genericPoint (Spec (.of A)), hηU⟩⟩
  let : IsIntegral U := isIntegral_of_isOpenImmersion U.ι
  let : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion U.ι
  let gU := Scheme.liftDominantFieldPoint g U hηU
  have hgU : gU ≫ U.ι = g := Scheme.liftDominantFieldPoint_ι g U hηU
  let : IsDominant (gU ≫ U.ι) := by rw [hgU]; infer_instance
  let : IsDominant gU := IsDominant.of_comp_of_isOpenImmersion gU U.ι
  let EU := Scheme.restrictModelComparison f g C e U hηU
  let : GeometricallyIntegral (pullback.snd (f ∣_ U) gU) := by
    have hEU : EU.hom.left ≫ C.hom = pullback.snd (f ∣_ U) gU := EU.hom.w
    rw [← hEU]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIntegral)
      EU.hom.left C.hom).mpr hC.isGeometricallyIntegral
  obtain ⟨V, hηV, hVne, hgeo⟩ :=
    Scheme.exists_generic_open_geometricallyIntegral_of_fieldBaseChange (f ∣_ U) gU
  let : Nonempty V := ⟨⟨genericPoint U, hηV⟩⟩
  let a := ((f ∣_ U) ⁻¹ᵁ V).ι ≫ (f ⁻¹ᵁ U).ι
  let b := (f ∣_ U) ∣_ V
  let j := V.ι ≫ U.ι
  have H : IsPullback a b f j :=
    (isPullback_morphismRestrict (f ∣_ U) V).flip.paste_horiz
      (isPullback_morphismRestrict f U).flip
  have hsmV : SmoothOfRelativeDimension 1 b :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict (f ∣_ U) V).flip hsmU
  let P : MorphismProperty Scheme.{u} := @SmoothOfRelativeDimension 1 ⊓ @GeometricallyIntegral
  obtain ⟨S, hAS, hS, hP, eS⟩ := Scheme.exists_fg_baseChange_property_of_open A hA f j a b H
    P ⟨hsmV, hgeo⟩ C e
  let φ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hAS).toRingHom)
  let q := pullback.snd f φ
  let : SmoothOfRelativeDimension 1 q := hP.1
  let : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  refine ⟨S, pullback f φ, q, hS, fun r hr => hAS (hextra r hr), inferInstance,
    hP.1, hP.2, inferInstance, inferInstance, inferInstance, inferInstance, eS⟩

end AlgebraicGeometry.Scheme.OverField.Curve

namespace AlgebraicGeometry.Scheme

private lemma factor_integer_fp_ring_above
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (A : CommRingCat.{u}) [Algebra.FinitePresentation ℤ A]
    (φ : A ⟶ c.pt) (i₀ : I) :
    ∃ (i : I) (_ : i₀ ⟶ i) (ψ : A ⟶ F.obj i), ψ ≫ c.ι.app i = φ := by
  let Z := ULift.{u} ℤ
  let : Algebra Z A := ULift.algebra' ℤ A
  let : IsScalarTower ℤ Z A := ⟨fun r s x => by
    change (r * s.down) • x = r • (s.down • x)
    exact mul_smul r s.down x⟩
  let : IsNoetherianRing Z :=
    isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv : Z ≃+* ℤ).symm
  let : Algebra.FiniteType Z A := Algebra.FiniteType.of_restrictScalars_finiteType ℤ Z A
  let : Algebra.FinitePresentation Z A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let R := CommRingCat.of Z
  let α : (Functor.const I).obj R ⟶ F :=
    { app i := CommRingCat.ofHom
        ((Int.castRingHom (F.obj i)).comp (ULift.ringEquiv : Z ≃+* ℤ).toRingHom)
      naturality {i j} q := by
        ext ⟨r⟩
        change (r : F.obj j) = (F.map q).hom (r : F.obj i)
        exact (map_intCast (F.map q).hom r).symm }
  let a : R ⟶ A := CommRingCat.ofHom (algebraMap Z A)
  have ha : a.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.mpr inferInstance
  obtain ⟨j, ψ, _, hψ⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    R F α a c hc ha φ (fun j => by
      ext ⟨r⟩
      change φ.hom (r : A) = (c.ι.app j).hom (r : F.obj j)
      exact (map_intCast φ.hom r).trans (map_intCast (c.ι.app j).hom r).symm)
  refine ⟨IsFiltered.max i₀ j, IsFiltered.leftToMax i₀ j,
    ψ ≫ F.map (IsFiltered.rightToMax i₀ j), ?_⟩
  rw [Category.assoc, c.w]
  exact hψ.symm

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- Native pullback pasting with a specified composite base morphism. -/
def iteratedBaseChangeIso {X S T V : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (h : V ⟶ T) (k : V ⟶ S) (hk : h ≫ g = k) :
    (Over.pullback h).obj ((Over.pullback g).obj (Over.mk f)) ≅
      (Over.pullback k).obj (Over.mk f) :=
  Over.isoMk (pullbackLeftPullbackSndIso f g h ≪≫ pullback.congrHom rfl hk)
    (by simp [Category.assoc])

/-- Proper smooth curve properties hold on a literal later base change of
an already supplied finitely presented qcqs model. The ring-stage maps may
be noninjective and nonflat. The final field comparison is the canonical
pullback-pasting comparison followed by the original supplied comparison. -/
theorem exists_curve_properties_on_later_baseChange
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) (K : Type u) [Field K]
    (ι : F ⟶ (Functor.const I).obj (CommRingCat.of K))
    (hc : IsColimit (Cocone.mk (CommRingCat.of K) ι))
    (i₀ : I) {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (F.obj i₀))
    [LocallyOfFinitePresentation f₀] [QuasiCompact f₀] [QuasiSeparated f₀]
    (C : OverField.FScheme K) (hC : OverField.Curve.Properties C)
    (e₀ : (Over.pullback (Spec.map (ι.app i₀))).obj (Over.mk f₀) ≅ C) :
    ∃ (j : I) (q : i₀ ⟶ j),
      IsProper (pullback.snd f₀ (Spec.map (F.map q))) ∧
      SmoothOfRelativeDimension 1 (pullback.snd f₀ (Spec.map (F.map q))) ∧
      GeometricallyIntegral (pullback.snd f₀ (Spec.map (F.map q))) ∧
      Flat (pullback.snd f₀ (Spec.map (F.map q))) ∧
      LocallyOfFinitePresentation (pullback.snd f₀ (Spec.map (F.map q))) ∧
      Nonempty ((Over.pullback (Spec.map (ι.app j))).obj
        (Over.mk (pullback.snd f₀ (Spec.map (F.map q)))) ≅ C) := by
  obtain ⟨A, Y, fA, hA, _, hproperA, hsmA, hgeoA, _, hfpA, hqcA, hqsA, ⟨eA⟩⟩ :=
    hC.exists_finite_base_model ∅
  let := hproperA
  let := hfpA
  let := hqcA
  let := hqsA
  let : Algebra.FiniteType ℤ A := A.fg_iff_finiteType.mp hA
  let : Algebra.FinitePresentation ℤ A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let c : Cocone F := Cocone.mk (CommRingCat.of K) ι
  let α : CommRingCat.of A ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap A K)
  obtain ⟨i, u, ψ, hψ⟩ := factor_integer_fp_ring_above F c hc (.of A) α i₀
  let g₀ := Spec.map (F.map u)
  let gA := Spec.map ψ
  let gi := Spec.map (ι.app i)
  let fi := pullback.snd f₀ g₀
  let hi := pullback.snd fA gA
  have h₀ : gi ≫ g₀ = Spec.map (ι.app i₀) := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map (c.w u)
  have hAcomp : gi ≫ gA = Spec.map α := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map hψ
  let EX : (Over.pullback gi).obj (Over.mk fi) ≅ C :=
    iteratedBaseChangeIso f₀ g₀ gi (Spec.map (ι.app i₀)) h₀ ≪≫ e₀
  let EY : (Over.pullback gi).obj (Over.mk hi) ≅ C :=
    iteratedBaseChangeIso fA gA gi (Spec.map α) hAcomp ≪≫ eA
  let D : Iᵒᵖ ⥤ Scheme.{u} := F.op ⋙ Scheme.Spec
  let cS : Cone D := Scheme.Spec.mapCone c.op
  have hcS : IsLimit cS := isLimitOfPreserves Scheme.Spec hc.op
  have (j : Iᵒᵖ) : IsAffine (D.obj j) := inferInstanceAs (IsAffine (Spec (F.obj j.unop)))
  obtain ⟨t, ⟨e⟩⟩ := exists_iso_between_baseChanges_of_isLimit D cS hcS (.op i) fi hi
    (EX ≪≫ EY.symm)
  let v : i ⟶ t.left.unop := t.hom.unop
  let q := u ≫ v
  let gq := Spec.map (F.map q)
  let gt := D.map t.hom
  have hq : gt ≫ g₀ = gq := by
    change Spec.map (F.map v) ≫ Spec.map (F.map u) = Spec.map (F.map (u ≫ v))
    rw [← Spec.map_comp, F.map_comp]
  let Ecomp : (Over.pullback gt).obj (Over.mk fi) ≅ (Over.pullback gq).obj (Over.mk f₀) :=
    iteratedBaseChangeIso f₀ g₀ gt gq hq
  let E := Ecomp.symm ≪≫ e
  let Z := (Over.pullback gt).obj (Over.mk hi)
  let f := pullback.snd f₀ gq
  have hE : E.hom.left ≫ Z.hom = f := E.hom.w
  have transfer (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (hP : P Z.hom) : P f := by
    rw [← hE]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := P) E.hom.left Z.hom).mpr hP
  have hproper : IsProper f := transfer @IsProper
    (MorphismProperty.pullback_snd (P := @IsProper) hi gt
      (MorphismProperty.pullback_snd (P := @IsProper) fA gA hproperA))
  have hsm : SmoothOfRelativeDimension 1 f := transfer (@SmoothOfRelativeDimension 1)
    (MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) hi gt
      (MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) fA gA hsmA))
  have hgeo : GeometricallyIntegral f := transfer @GeometricallyIntegral
    (MorphismProperty.pullback_snd (P := @GeometricallyIntegral) hi gt
      (MorphismProperty.pullback_snd (P := @GeometricallyIntegral) fA gA hgeoA))
  let : SmoothOfRelativeDimension 1 f := hsm
  let : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have hfinal : Spec.map (ι.app t.left.unop) ≫ gq = Spec.map (ι.app i₀) := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map (c.w q)
  let Efinal := iteratedBaseChangeIso f₀ gq (Spec.map (ι.app t.left.unop))
      (Spec.map (ι.app i₀)) hfinal ≪≫ e₀
  exact ⟨t.left.unop, q, hproper, hsm, hgeo, inferInstance, inferInstance, ⟨Efinal⟩⟩

end AlgebraicGeometry.Scheme
