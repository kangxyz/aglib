/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Naturality
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Connectedness
public import Aglib.RingTheory.Smooth.GenericConnectedness

/-!
# Generic restriction over a normal affine domain

Supporting local uniqueness obligation for K2-018#prop:k2018-arithmetic-characters,
source revision e73d98b1b5c1e5abcdebf7d058e436d792b87982. The generic connectedness and injectivity
  prefix is imported directly through
native scheme and continuous-cohomology constructions. The original
normalization-coefficient-specific final theorem is outside this prefix. No
generic connectedness, fibre-group surjectivity, or H1-injectivity premise is introduced.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.AlgebraicGeometry.Scheme.EtaleH1 _root_.CategoryTheory.Abelian
  _root_.CategoryTheory.Functor.LargePresheaf
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberToFinite)
open _root_.AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open AlgebraicGeometry.Scheme.FiniteEtale
open _root_.GroupCohomology.ContinuousH1
open scoped TensorProduct CategoryTheory.PreGaloisCategory FintypeCatDiscrete

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericRestriction

universe u v w

section GenericMap
variable (R K Ω : Type u) [CommRing R] [Field K] [Algebra R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]

/-- The literal geometric point supplied by the displayed algebra map. -/
abbrev basePoint := Spec.algebraMap R Ω

/-- The generic inclusion is the spectrum of the displayed algebra map. -/
abbrev genericInclusion : Spec (.of K) ⟶ Spec (.of R) := Spec.algebraMap R K

/-- The original point factors through the generic point by the scalar tower. -/
theorem genericPoint_compat :
    basePoint K Ω ≫ genericInclusion R K = basePoint R Ω := by
  change Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R K)) = Spec.map (CommRingCat.ofHom (algebraMap R Ω))
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq R K Ω).symm

/-- The native pointed fibre-group map for this exact generic inclusion. -/
abbrev genericFibreMap : FiberAutGroup (basePoint K Ω) →ₜ* FiberAutGroup (basePoint R Ω) :=
  AlgebraicGeometry.Scheme.EtaleH1.Naturality.pointedGroupHom (genericInclusion R K)
    (basePoint K Ω) (basePoint R Ω) (genericPoint_compat R K Ω)

end GenericMap

/-- A connected actual finite-etale cover of a normal affine domain remains
connected after the literal fraction-field scheme base change. -/
theorem generic_cover_connected (R K : Type u)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (Y : Scheme.FiniteEtale (Spec (.of R))) [ConnectedSpace Y.obj.left] :
    ConnectedSpace ((baseChange (genericInclusion R K)).obj Y).obj.left := by
  let : IsAffine Y.obj.left := isAffine_of_isAffineHom Y.obj.hom
  let B : Type u := Γ(Y.obj.left, ⊤)
  let : CommRing B := inferInstance
  let : Algebra R B :=
    (((Scheme.ΓSpecIso (.of R)).inv ≫ Y.obj.hom.appTop).hom).toAlgebra
  have hcoord : Y.obj.left.isoSpec.inv ≫ Y.obj.hom = Spec.algebraMap R B := by
    change Y.obj.left.isoSpec.inv ≫ Y.obj.hom =
      Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ Y.obj.hom.appTop)
    rw [Spec.map_comp]
    simpa only [Scheme.isoSpec_Spec_inv] using (Scheme.isoSpec_inv_naturality Y.obj.hom).symm
  have : Etale (Spec.algebraMap R B) := by
    rw [← hcoord]
    infer_instance
  have : Algebra.Etale R B :=
    RingHom.etale_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Etale)).mp
      (inferInstance : Etale (Spec.algebraMap R B)))
  have : ConnectedSpace (PrimeSpectrum B) :=
    Y.obj.left.isoSpec.hom.homeomorph.connectedSpace_iff.mp inferInstance
  let := Algebra.Smooth.generic_primeSpectrum_connected R K B
  have hc : Y.obj.hom ≫ 𝟙 _ = Y.obj.left.isoSpec.hom ≫ Spec.algebraMap R B := by
    rw [← hcoord, ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
  let e : pullback Y.obj.hom (genericInclusion R K) ≅
      pullback (Spec.algebraMap R B) (genericInclusion R K) :=
    asIso (pullback.map Y.obj.hom (genericInclusion R K)
      (Spec.algebraMap R B) (genericInclusion R K)
      Y.obj.left.isoSpec.hom (𝟙 _) (𝟙 _) hc (by simp))
  exact (e ≪≫ pullbackSpecIso R B K).hom.homeomorph.connectedSpace_iff.mpr
    (Algebra.Smooth.generic_primeSpectrum_connected R K B)

/-- Transitivity on the pointed Galois fibres makes a compact group's image
dense in the actual automorphism group; compactness then makes it surjective. -/
private theorem surjective_of_galois_fibre_transitive
    {C : Type v} [Category.{w} C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{u}) [PreGaloisCategory.FiberFunctor F]
    {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    (φ : G →ₜ* Aut F)
    (htrans : ∀ (P : PreGaloisCategory.PointedGaloisObject F) (b : F.obj P.obj),
      ∃ g : G, φ g • P.pt = b) :
    Function.Surjective φ := by
  have hclosed : IsClosed (Set.range φ) := (isCompact_range φ.continuous).isClosed
  intro γ
  have hmem : γ ∈ closure (Set.range φ) := by
    rw [mem_closure_iff]
    intro U hU hγ
    have hopen : IsOpen ((fun a : Aut F => γ * a) ⁻¹' U) :=
      hU.preimage (continuous_const.mul continuous_id)
    have h1 : (1 : Aut F) ∈ (fun a : Aut F => γ * a) ⁻¹' U := by
      simpa using hγ
    obtain ⟨P, _, hP⟩ :=
      (PreGaloisCategory.nhds_one_has_basis_stabilizers F).mem_iff.mp (hopen.mem_nhds h1)
    obtain ⟨g, hg⟩ := htrans P (γ • P.pt)
    have hstab : γ⁻¹ * φ g ∈ MulAction.stabilizer (Aut F) P.pt := by
      change (γ⁻¹ * φ g) • P.pt = P.pt
      rw [mul_smul, hg, inv_smul_smul]
    refine ⟨φ g, ?_, ⟨g, rfl⟩⟩
    simpa using hP hstab
  simpa only [hclosed.closure_eq, Set.mem_range] using hmem

private theorem pointedMap_sends_of_fibre_sends {F : Type u} [Field F]
    {S X : PointedScheme F} (fp : S ⟶ X)
    (γ : FiberAutGroup S.hom) (Y : Scheme.FiniteEtale X.right) (p q : Fiber X.hom Y)
    (hγ : γ.hom.app ((baseChange fp.right).obj Y) (pointedFiberEquiv fp Y p) =
      pointedFiberEquiv fp Y q) :
    (pointedMap fp γ).hom.app Y p = q := by
  rw [pointedMap_apply, hγ]
  exact (pointedFiberEquiv fp Y).symm_apply_apply q

/-- The general pointed-scheme implication is proved before specializing the
pointed map to a fraction-field algebra map. Its connectedness hypothesis is
discharged geometrically in genericFibreMap_surjective below. -/
private theorem pointedGroupHom_surjective_of_connected
    {S X : Scheme.{u}} {F : Type u} [Field F]
    (f : S ⟶ X) (s : Spec (.of F) ⟶ S) (x : Spec (.of F) ⟶ X) (hx : s ≫ f = x)
    [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite x)]
    [GaloisCategory (Scheme.FiniteEtale S)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
    (hconn : ∀ (Y : Scheme.FiniteEtale X), ConnectedSpace Y.obj.left →
      ConnectedSpace ((baseChange f).obj Y).obj.left) :
    Function.Surjective (_root_.AlgebraicGeometry.Scheme.EtaleH1.Naturality.pointedGroupHom f s x
      hx) := by
  apply surjective_of_galois_fibre_transitive
    (fiberToFinite x) (_root_.AlgebraicGeometry.Scheme.EtaleH1.Naturality.pointedGroupHom f s x hx)
  intro P b
  have : ConnectedSpace P.obj.obj.left :=
    _root_.AlgebraicGeometry.Scheme.FiniteEtale.Connectedness.connectedSpace_of_categoricalConnected
      P.obj
  have : ConnectedSpace ((baseChange f).obj P.obj).obj.left := hconn P.obj inferInstance
  have ht :=
    (_root_.AlgebraicGeometry.Scheme.FiniteEtale.Connectedness.connectedSpace_iff_transitive s
    ((baseChange f).obj P.obj)).mp
    inferInstance
  let := ht.2
  let fp : Under.mk s ⟶ Under.mk x := Under.homMk f hx
  let q : (fiberToFinite s).obj ((baseChange f).obj P.obj) := pointedFiberEquiv fp P.obj P.pt
  let z : (fiberToFinite s).obj ((baseChange f).obj P.obj) := pointedFiberEquiv fp P.obj b
  obtain ⟨γ, hγ⟩ := MulAction.IsPretransitive.exists_smul_eq (M := FiberAutGroup s) q z
  refine ⟨γ, ?_⟩
  exact pointedMap_sends_of_fibre_sends fp γ P.obj P.pt b hγ

/-- Source K2-018#prop:k2018-arithmetic-characters, revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982: local generic uniqueness prerequisite.
The literal generic pointed fibre-group map is surjective over a normal domain.
Connected generic fibres are derived above; surjectivity is not an input. -/
theorem genericFibreMap_surjective (R K Ω : Type u)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of R)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (basePoint R Ω))]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (basePoint K Ω))] :
    Function.Surjective (genericFibreMap R K Ω) := by
  apply pointedGroupHom_surjective_of_connected (genericInclusion R K)
    (basePoint K Ω) (basePoint R Ω) (genericPoint_compat R K Ω)
  intro Y hY
  let := hY
  exact generic_cover_connected R K Y

/-- Surjective continuous group restriction is injective on native continuous
H1: the same coboundary coefficient descends through the surjection. -/
theorem restriction_injective_of_surjective {G J M : Type*}
    [Group G] [TopologicalSpace G] [Group J] [TopologicalSpace J]
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
    (φ : J →ₜ* G) (hφ : Function.Surjective φ) :
    Function.Injective (restriction M φ) := by
  let := restrictedAction M φ
  let := restrictedAction_continuous M φ
  intro x y hxy
  obtain ⟨c, rfl⟩ := classOf_surjective G M x
  obtain ⟨d, rfl⟩ := classOf_surjective G M y
  rw [restriction_classOf, restriction_classOf, classOf_eq_iff] at hxy
  obtain ⟨m, hm⟩ := hxy
  apply (classOf_eq_iff G M c d).mpr
  refine ⟨m, ?_⟩
  apply _root_.GroupCohomology.ContinuousH1.Cocycle.ext
  intro g
  obtain ⟨j, rfl⟩ := hφ g
  exact congrArg (fun c : Cocycle J M => c.val j) hm

/-- Source K2-018#prop:k2018-arithmetic-characters, revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982, local class-uniqueness subset.
Actual generic restriction is injective on every continuous model H1 class;
no finiteness of the coefficients is needed for this group-cohomology step. -/
theorem generic_restriction_injective (R K Ω M : Type u)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of R)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (basePoint R Ω))]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (basePoint K Ω))]
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction (FiberAutGroup (basePoint R Ω)) M]
    [ContinuousSMul (FiberAutGroup (basePoint R Ω)) M] :
    Function.Injective (restriction M (genericFibreMap R K Ω)) :=
  restriction_injective_of_surjective (genericFibreMap R K Ω)
    (genericFibreMap_surjective R K Ω)

universe wR wK

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Source K2-018#prop:k2018-arithmetic-characters, revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982, conditional local class uniqueness.
The genuine etale h1Pullback is injective on arbitrary model classes with a
finite-etale represented coefficient and its actual equivariant fibre marking.
General Stacks03AJ/03RV and Galois-category/fibre-functor inputs remain explicit. -/
theorem generic_represented_h1Pullback_injective (R K Ω : Type u)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of R)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (basePoint R Ω))]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (basePoint K Ω))]
    [HasExt.{wR} (AbelianSheaf.{u, u + 1} (Spec (.of R)))]
    [HasExt.{wK} (AbelianSheaf.{u, u + 1} (Spec (.of K)))]
    (A : Grp (Over (Spec (.of R)))) [IsCommMonObj A.X] [IsFinite A.X.hom] [Etale A.X.hom]
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [IsTopologicalAddGroup M]
    [DistribMulAction (FiberAutGroup (basePoint R Ω)) M]
    [ContinuousSMul (FiberAutGroup (basePoint R Ω)) M]
    (mark : (Over.mk (basePoint R Ω) ⟶ A.X) ≃* Multiplicative M)
    (hmark : ∀ (γ : FiberAutGroup (basePoint R Ω)) a,
      mark (γ.hom.app (coefficientCover A) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))
    (hAR : Stacks03AJ.{u, wR} (Spec (.of R))) (hRR : Stacks03RV (Spec (.of R)))
    (hAK : Stacks03AJ.{u, wK} (Spec (.of K))) (hRK : Stacks03RV (Spec (.of K)))
    (hcoeff : FiniteCoefficient (representedSheaf A)) :
    Function.Injective (h1Pullback (genericInclusion R K) (representedSheaf A)) := by
  let : Finite M := Finite.of_equiv
    ((fiberToFinite (basePoint R Ω)).obj (coefficientCover A)) mark.toAdditiveLeft.toEquiv
  intro a b hab
  apply (_root_.AlgebraicGeometry.Scheme.EtaleH1.FundamentalGroupComparison.representedH1AddEquiv
    (basePoint R Ω) A
    hAR hRR M mark hmark hcoeff).injective
  apply generic_restriction_injective R K Ω M
  have ha :=
    _root_.AlgebraicGeometry.Scheme.EtaleH1.Naturality.pointedInverseImageH1AddEquiv_pullback
    (genericInclusion R K)
    (basePoint K Ω) (basePoint R Ω) (genericPoint_compat R K Ω) A M mark hmark
    hAR hAK hRR hRK hcoeff a
  have hb :=
    _root_.AlgebraicGeometry.Scheme.EtaleH1.Naturality.pointedInverseImageH1AddEquiv_pullback
    (genericInclusion R K)
    (basePoint K Ω) (basePoint R Ω) (genericPoint_compat R K Ω) A M mark hmark
    hAR hAK hRR hRK hcoeff b
  exact ha.symm.trans ((congrArg
    (_root_.AlgebraicGeometry.Scheme.EtaleH1.Naturality.pointedInverseImageH1AddEquiv
      (genericInclusion R K)
      (basePoint K Ω) (basePoint R Ω) (genericPoint_compat R K Ω) A M mark hmark
      hAK hRK hcoeff) hab).trans hb)

end AlgebraicGeometry.Scheme.FiniteEtale.GenericRestriction
