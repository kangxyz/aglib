/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface
public import Aglib.RingTheory.RegularLocalRing.NormalQuotientExt
public import Mathlib.Topology.Separation.Basic

/-!
# Chosen-embedding concentration for curves with regular closed-stalk parameters

The coefficient is the original top differential coefficient functor at the
structure module over an arbitrary field. At each closed source point, an
actual nonzerodivisor with maximal-primary principal ideal gives a length-one
regular sequence for the original ambient local-ring action. Its quotient
has finite length, so the original local Ext is concentrated in ambient
dimension minus one.

Coherence and closed support of the original derived homology globalize
this calculation without integrality, reducedness, normality or separability.
The canonical module is the original homology in degree `n - 1`, with its
native single-homology normalization. The closed-stalk parameter condition is
an explicit input; no general Cohen--Macaulay predicate is introduced here.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.FiniteSourceStalk
open RingTheory.Sequence IsLocalRing
open scoped ModuleCat.Algebra

private theorem regularParameter_of_ringEquiv
    {B B' : Type u} [CommRing B] [CommRing B'] [IsLocalRing B] [IsLocalRing B']
    (e : B ≃+* B')
    (hB : ∃ b ∈ maximalIdeal B, IsSMulRegular B b ∧
      (Ideal.span {b}).radical = maximalIdeal B) :
    ∃ b ∈ maximalIdeal B', IsSMulRegular B' b ∧
      (Ideal.span {b}).radical = maximalIdeal B' := by
  let : IsLocalHom e.toRingHom := IsLocalHom.of_surjective e.toRingHom e.surjective
  obtain ⟨b, hb, hreg, hrad⟩ := hB
  refine ⟨e b, map_nonunit e.toRingHom b hb, ?_, ?_⟩
  · intro x y hxy
    apply e.symm.injective
    apply hreg
    have h := congrArg e.symm hxy
    change e.symm (e b * x) = e.symm (e b * y) at h
    change b * e.symm x = b * e.symm y
    simpa only [map_mul, e.symm_apply_apply] using h
  · have hker : RingHom.ker e.toRingHom ≤ Ideal.span {b} := by
      rw [(RingHom.injective_iff_ker_eq_bot e.toRingHom).mp e.injective]
      exact bot_le
    have h := congrArg (Ideal.map e.toRingHom) hrad
    rw [Ideal.map_radical_of_surjective e.surjective hker, Ideal.map_span,
      Set.image_singleton, map_maximalIdeal_of_surjective e.toRingHom e.surjective] at h
    exact h

private theorem subsingleton_ext_of_surjective_regularParameter
    {S B : Type u} [CommRing S] [CommRing B] [IsRegularLocalRing S] [IsLocalRing B]
    (f : S →+* B) [IsLocalHom f] (hf : Function.Surjective f)
    (hB : ∃ b ∈ maximalIdeal B, IsSMulRegular B b ∧
      (Ideal.span {b}).radical = maximalIdeal B)
    (n q : ℕ) (hn : ringKrullDim S = (n : ℕ)) (hq : q + 1 ≠ n) :
    letI := f.toAlgebra
    Subsingleton (Ext.{u} (ModuleCat.of S B) (ModuleCat.of S S) q) := by
  let := f.toAlgebra
  let : Module.Finite S B := Module.Finite.of_surjective (Algebra.linearMap S B) hf
  obtain ⟨b, hb, hreg, hrad⟩ := hB
  obtain ⟨a, ha⟩ := hf b
  have ha' : algebraMap S B a = b := ha
  have haM : a ∈ maximalIdeal S := by
    rw [← maximalIdeal_comap f]
    change f a ∈ maximalIdeal B
    rwa [ha]
  have hregB : IsWeaklyRegular B [b] :=
    IsWeaklyRegular.cons hreg (IsWeaklyRegular.nil _ _)
  have hregS : IsWeaklyRegular B [a] := by
    apply (isWeaklyRegular_map_algebraMap_iff B B [a]).mp
    simpa only [List.map_cons, List.map_nil, ha'] using hregB
  have hQ : IsFiniteLength S (B ⧸ (Ideal.ofList [a] • ⊤ : Submodule S B)) :=
    isFiniteLength_quotient_ofList_of_radical_eq_maximalIdeal [a] (by
      simpa only [List.map_cons, List.map_nil, Ideal.ofList_singleton, ha'] using hrad)
  exact IsRegularLocalRing.subsingleton_ext_of_regular_sequence S (ModuleCat.of S B)
    [a] hregS (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact haM)
    hQ n hn q (by simpa only [List.length_singleton] using hq)

@[expose] public section

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The standard derived-category model for module sheaves on the given scheme. -/
local instance cmCurveHasDerivedCategoryModules (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

variable (k : Type u) [Field k] (ι : Type u)

/-- The original unit coefficient for the chosen projective embedding. -/
abbrev cmCurveAmbientCoefficient (n : ℕ) : (ProjectiveSpace k ι).Modules :=
  normalSurfaceAmbientCoefficient k ι n

/-- The original closed right adjoint with its original top differential coefficient. -/
abbrev cmCurveDualizingObject {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j] (n : ℕ) :
    DerivedCategory.Plus C.Modules := normalSurfaceDualizingObject k ι j n

/-- The coefficient-unit isomorphism is the existing original differential normalization. -/
def cmCurveDualizingObjectUnitIso {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j] (n : ℕ) :
    cmCurveDualizingObject k ι j n ≅ normalSurfaceTopDifferentialObject k ι j n :=
  normalSurfaceDualizingObjectUnitIso k ι j n

/-- Native homology of the same original chosen-embedding object. -/
abbrev cmCurveHomology {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j] (n : ℕ) (q : ℤ) : C.Modules :=
  derivedClosedImmersionRightAdjointHomology j (cmCurveAmbientCoefficient k ι n) q

/-- The canonical module is the original homology in integer degree `n - 1`.
No invertibility or local freeness is part of this definition. -/
abbrev cmCurveCanonicalModule {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j] (n : ℕ) : C.Modules :=
  cmCurveHomology k ι j n ((n : ℤ) - 1)

/-- All original homology sheaves are coherent before the concentration argument. -/
theorem cmCurveHomology_finitePresentation {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (q : ℤ) :
    (cmCurveHomology k ι j n q).IsFinitePresentation :=
  normalSurfaceHomology_finitePresentation k ι j n e q

/-- The actual canonical module is coherent, without a local-freeness assertion. -/
theorem cmCurveCanonicalModule_finitePresentation {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    (cmCurveCanonicalModule k ι j n).IsFinitePresentation :=
  cmCurveHomology_finitePresentation k ι j n e ((n : ℤ) - 1)

private theorem polynomialStalk_dimension_of_isClosed
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (a : ι)
    (y : Spec (.of (MvPolynomial {b : ι // b ≠ a} k)))
    (hy : IsClosed ({y} : Set (Spec (.of (MvPolynomial {b : ι // b ≠ a} k))))) :
    ringKrullDim ((Spec (.of (MvPolynomial {b : ι // b ≠ a} k))).presheaf.stalk y) =
      (n : ℕ) := by
  let : Finite ι := Finite.of_equiv _ e.symm
  let : y.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hy
  have hcard : Nat.card {b : ι // b ≠ a} = n := by
    rw [Nat.card_congr (determinantComplementEquiv ι n e a)]
    simp only [Nat.card_ulift, Nat.card_fin]
  have hpoly := MvPolynomial.mvPolynomial_localizationAtPrime_dimension_of_isMaximal
    k {b : ι // b ≠ a} y.asIdeal
  exact (ringKrullDim_eq_of_ringEquiv
    (Spec.stalkIso (.of (MvPolynomial {b : ι // b ≠ a} k)) y).commRingCatIsoToRingEquiv).trans
      (by simpa only [hcard] using hpoly)

section Concentration

variable {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
  (n : ℕ) (e : ι ≃ Fin (n + 1))
  (hCM : ∀ x : C, IsClosed ({x} : Set C) →
    ∃ b ∈ maximalIdeal (C.presheaf.stalk x), IsSMulRegular (C.presheaf.stalk x) b ∧
      (Ideal.span {b}).radical = maximalIdeal (C.presheaf.stalk x))

include e hCM

/-- At each closed source point, the elementary regular parameter gives
vanishing of the actual derived homology stalk outside degree `n - 1`. -/
theorem cmCurveHomology_closedStalk_isZero (x : C) (hx : IsClosed ({x} : Set C))
    (q : ℕ) (hq : q + 1 ≠ n) :
    IsZero ((stalkFunctor C x).obj (cmCurveHomology k ι j n (q : ℤ))) := by
  let : Finite ι := Finite.of_equiv _ e.symm
  have := normalSurfaceAmbientCoefficient_finitePresentation k ι n e
  obtain ⟨a, y, hy⟩ := normalSurface_exists_polynomialPoint k ι (j x)
  let P : CommRingCat.{u} := .of (MvPolynomial {b : ι // b ≠ a} k)
  let v := eulerPolynomialChart k ι a
  let Q := closedImmersionAffineQuotientChart j P v
  let : IsClosedImmersion (Spec.map (quotientMap Q.ideal)) := quotientClosedImmersion Q.ideal
  obtain ⟨z, hz, hzy⟩ := Q.exists_point x y hy.symm
  let y' : Spec P := imagePoint Q.ideal z
  have hy' : v y' = j x := (congrArg v hzy).trans hy
  have hjx : IsClosed ({j x} : Set (ProjectiveSpace k ι)) := by
    simpa only [Set.image_singleton] using j.isClosedEmbedding.isClosedMap _ hx
  have hyclosed : IsClosed ({y'} : Set (Spec P)) := by
    have h := hjx.preimage v.continuous
    convert h using 1
    ext t
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    rw [← hy']
    exact v.isOpenEmbedding.injective.eq_iff.symm
  let S : CommRingCat.{u} := ambientRing Q.ideal z
  let B : CommRingCat.{u} := sourceRing Q.ideal z
  let : IsRegularLocalRing S := normalSurface_polynomialStalk_regular k ι a y'
  have hSdim : ringKrullDim S = (n : ℕ) :=
    polynomialStalk_dimension_of_isClosed k ι n e a y' hyclosed
  let eB := (asIso (Q.sourceMap.stalkMap z)).commRingCatIsoToRingEquiv
  have hpoint : IsClosed ({Q.sourceMap z} : Set C) := hz.symm ▸ hx
  have hB : ∃ b ∈ maximalIdeal B, IsSMulRegular B b ∧
      (Ideal.span {b}).radical = maximalIdeal B :=
    regularParameter_of_ringEquiv eB (hCM (Q.sourceMap z) hpoint)
  let f : S →+* B := (FiniteSourceStalk.stalkMap Q.ideal z).hom
  let := f.toAlgebra
  let L := (cmCurveAmbientCoefficient k ι n).restrict v
  have : L.IsFinitePresentation := finitePresentation_restrict v _
  let J := injectiveResolution L
  let eSource : ModuleCat.of S B ≅
      (ModuleCat.restrictScalars f).obj (ModuleCat.of B B) :=
    (LinearEquiv.refl S B).toModuleIso
  let E := (derivedClosedImmersionRightAdjointQuotientStalkExtLinearEquiv Q.ideal J z q).trans
    (extIsoTransport eSource (normalSurfacePolynomialCoefficientStalkIso k ι n e a y') q)
  let : Subsingleton (Ext.{u} (ModuleCat.of S B) (ModuleCat.of S S) q) :=
    subsingleton_ext_of_surjective_regularParameter f
      ((Spec.map (quotientMap Q.ideal)).stalkMap_surjective z) hB n q hSdim hq
  let : Subsingleton ((stalkFunctor (Spec (quotientRing Q.ideal)) z).obj
      (derivedClosedImmersionRightAdjointHomology
        (Spec.map (quotientMap Q.ideal)) L (q : ℤ))) := E.toEquiv.subsingleton
  have hzero := AddCommGrpCat.isZero_of_subsingleton
    ((stalkFunctor (Spec (quotientRing Q.ideal)) z).obj
      (derivedClosedImmersionRightAdjointHomology
        (Spec.map (quotientMap Q.ideal)) L (q : ℤ)))
  simpa only [hz] using hzero.of_iso
    (Q.homologyStalkIso (cmCurveAmbientCoefficient k ι n) (q : ℤ) z)

/-- Closed coherent support globalizes the closed-stalk calculation, including
nonreduced curves over arbitrary fields. Negative degrees use the original model. -/
theorem cmCurveHomology_isZero (q : ℤ) (hq : q ≠ (n : ℤ) - 1) :
    IsZero (cmCurveHomology k ι j n q) := by
  by_cases hneg : q < 0
  · exact derivedClosedImmersionRightAdjointHomology_isZero_of_neg j _ q hneg
  obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
  let : Finite ι := Finite.of_equiv _ e.symm
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace (j ≫ toSpec k ι)
  have := normalSurfaceAmbientCoefficient_finitePresentation k ι n e
  have hs := derivedClosedImmersionRightAdjointHomology_isClosed_support
    j (cmCurveAmbientCoefficient k ι n) (r : ℤ)
  apply (support_eq_empty_iff _).mp
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨y, hy, hyclosed⟩ := hs.exists_closed_singleton ⟨x, hx⟩
  exact hy (cmCurveHomology_closedStalk_isZero k ι j n e hCM y hyclosed r (by omega))

/-- The original derived object has the asserted lower homology bound. -/
theorem cmCurveDualizingObject_isGE :
    (cmCurveDualizingObject k ι j n).IsGE ((n : ℤ) - 1) := by
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
  intro q hq
  exact cmCurveHomology_isZero k ι j n e hCM q (ne_of_lt hq)

/-- The original derived object has the asserted upper homology bound. -/
theorem cmCurveDualizingObject_isLE :
    (cmCurveDualizingObject k ι j n).IsLE ((n : ℤ) - 1) := by
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff, DerivedCategory.isLE_iff]
  intro q hq
  exact cmCurveHomology_isZero k ι j n e hCM q (ne_of_gt hq)

/-- The chosen-embedding object is the single of its actual canonical module,
through the original homology-normalized reconstruction. -/
def cmCurveCanonicalIso :
    cmCurveDualizingObject k ι j n ≅
      (DerivedCategory.Plus.singleFunctor C.Modules ((n : ℤ) - 1)).obj
        (cmCurveCanonicalModule k ι j n) := by
  let := cmCurveDualizingObject_isGE k ι j n e hCM
  let := cmCurveDualizingObject_isLE k ι j n e hCM
  exact DerivedCategory.Plus.isoSingleHomology
    (cmCurveDualizingObject k ι j n) ((n : ℤ) - 1)

/-- The reconstruction induces the identity on its original canonical homology. -/
theorem cmCurveCanonicalIso_homology :
    (DerivedCategory.Plus.homologyFunctor C.Modules ((n : ℤ) - 1)).map
        (cmCurveCanonicalIso k ι j n e hCM).hom ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
        (C := C.Modules) ((n : ℤ) - 1)).hom.app (cmCurveCanonicalModule k ι j n) = 𝟙 _ := by
  let := cmCurveDualizingObject_isGE k ι j n e hCM
  let := cmCurveDualizingObject_isLE k ι j n e hCM
  change (DerivedCategory.homologyFunctor C.Modules ((n : ℤ) - 1)).map
    ((DerivedCategory.Plus.ι : _ ⥤ DerivedCategory C.Modules).map
      (DerivedCategory.Plus.isoSingleHomology
        (cmCurveDualizingObject k ι j n) ((n : ℤ) - 1)).hom) ≫ _ = _
  rw [DerivedCategory.Plus.ι_map_isoSingleHomology_hom]
  exact DerivedCategory.isoSingleHomology_homology _ ((n : ℤ) - 1)

/-- Raw top differentials use only the original coefficient-unit isomorphism
and the same normalized canonical module. -/
def cmCurveTopDifferentialCanonicalIso :
    normalSurfaceTopDifferentialObject k ι j n ≅
      (DerivedCategory.Plus.singleFunctor C.Modules ((n : ℤ) - 1)).obj
        (cmCurveCanonicalModule k ι j n) :=
  (cmCurveDualizingObjectUnitIso k ι j n).symm ≪≫ cmCurveCanonicalIso k ι j n e hCM

end Concentration

end AlgebraicGeometry.Scheme.Cohomology
