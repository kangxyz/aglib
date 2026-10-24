/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Ext.ScalarRegularity
public import Aglib.Algebra.Homology.DerivedCategory.Ext.LinearEquiv
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface
public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.Cartier.Purity
public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.Affine
public import Aglib.AlgebraicGeometry.Modules.Flat.Locality
public import Aglib.AlgebraicGeometry.Modules.Locality.Sections
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Sections
public import Aglib.AlgebraicGeometry.Modules.Tensor.Stalk.Bilinear
public import Aglib.RingTheory.RegularLocalRing.NormalQuotientExt
public import Mathlib.RingTheory.KrullDimension.LocalRing

/-!
# Cartier regularity of the original normal-surface canonical module

At an actual ambient regular local quotient, a prescribed nonzero equation
is regular on the original canonical Ext module. Its scalar quotient has
vanishing Ext in the canonical degree: dimension one uses finite length,
and dimension two uses a regular parameter pair containing that equation.

The original ambient-linear quotient-stalk comparison, coefficient frame
and module-valued open exchange transport this result to the OWN canonical
homology stalk. The original Cartier tensor section is then monic by its
positive evaluation and cancellation maps. The canonical module need not
be locally free, and no canonical regularity predicate is assumed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open AlgebraicGeometry Opposite IsLocalRing RingTheory.Sequence
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open scoped Pointwise TensorProduct ModuleCat.Algebra

private theorem canonicalQuotientExt_vanish
    (S B : Type u) [CommRing S] [IsRegularLocalRing S]
    [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [IsDomain B] [IsIntegrallyClosed B] [Algebra S B]
    [IsLocalHom (algebraMap S B)] (hsurj : Function.Surjective (algebraMap S B))
    (d r q : ℕ) (hd : ringKrullDim S = (d : ℕ))
    (hr : ringKrullDim B = (r : ℕ)) (hr2 : r ≤ 2) (hqr : q + r = d)
    (a : S) (ha0 : algebraMap S B a ≠ 0)
    (ham : algebraMap S B a ∈ maximalIdeal B) :
    Subsingleton (Ext.{u} (ModuleCat.of S (QuotSMulTop a B)) (ModuleCat.of S S) q) := by
  let : Module.Finite S B := Module.Finite.of_surjective (Algebra.linearMap S B) hsurj
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with rfl | rfl | rfl
  · let : Ring.KrullDimLE 0 B := Ring.krullDimLE_iff.mpr (by simpa using hr.le)
    have hfield : IsField B := Ring.KrullDimLE.isField_of_isDomain
    obtain ⟨b, hb⟩ := hfield.mul_inv_cancel ha0
    exact False.elim (ham (isUnit_iff_exists_inv.mpr ⟨b, hb⟩))
  · have hrad : (Ideal.span {algebraMap S B a}).radical = maximalIdeal B := by
      apply le_antisymm
      · exact (maximalIdeal.isMaximal B).isPrime.radical_le_iff.mpr
          (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ham))
      · exact (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp
          (by simpa using hr)).2 _ ha0
    have hQ := isFiniteLength_quotient_ofList_of_radical_eq_maximalIdeal
      (S := S) (B := B) [a] (by
        simpa only [List.map_cons, List.map_nil, Ideal.ofList_cons,
          Ideal.ofList_nil, sup_bot_eq] using hrad)
    have hfinite : IsFiniteLength S (QuotSMulTop a B) := by
      have heq : (Ideal.ofList [a] • ⊤ : Submodule S B) = a • ⊤ := by
        rw [Ideal.ofList_cons, Ideal.ofList_nil, sup_bot_eq,
          Submodule.ideal_span_singleton_smul]
      exact (Submodule.quotEquivOfEq _ _ heq).isFiniteLength hQ
    exact IsRegularLocalRing.subsingleton_ext_of_isFiniteLength_ne_dimension S
      (ModuleCat.of S (QuotSMulTop a B)) hfinite d hd q (by omega)
  · let : Ring.KrullDimLE 2 B := Ring.krullDimLE_iff.mpr (by simpa using hr.le)
    obtain ⟨b, hb, hparam⟩ := exists_parameter_pair_containing B
      (algebraMap S B a) ha0 ham
    have hrad : (Ideal.ofList [algebraMap S B a, b]).radical = maximalIdeal B := by
      simpa only [Ideal.ofList_cons, Ideal.ofList_nil, sup_bot_eq] using hparam
    have hregB : IsRegular B [algebraMap S B a, b] :=
      IsIntegrallyClosed.isRegular_pair_of_radical_eq_maximalIdeal
        (algebraMap S B a) b ha0 (by simpa using hr.ge) hrad
    obtain ⟨c, hc⟩ := hsurj b
    have hmap : [a, c].map (algebraMap S B) = [algebraMap S B a, b] := by
      simp only [List.map_cons, List.map_nil, hc]
    have hregS : IsWeaklyRegular B [a, c] := by
      apply (isWeaklyRegular_map_algebraMap_iff B B [a, c]).mp
      rw [hmap]
      exact hregB.toIsWeaklyRegular
    have hcmax : c ∈ maximalIdeal S := by
      rw [← maximalIdeal_comap (algebraMap S B)]
      change algebraMap S B c ∈ maximalIdeal B
      rwa [hc]
    have hQ : IsFiniteLength S
        (B ⧸ (Ideal.ofList [a, c] • ⊤ : Submodule S B)) :=
      isFiniteLength_quotient_ofList_of_radical_eq_maximalIdeal [a, c]
        (by rwa [hmap])
    let Q := ModuleCat.of S (QuotSMulTop a B)
    have hQ' : IsFiniteLength S (Q ⧸ (Ideal.ofList [c] • ⊤ : Submodule S Q)) :=
      (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner B a [c]).isFiniteLength hQ
    have hrest : IsWeaklyRegular Q [c] :=
      ((isWeaklyRegular_cons_iff B a [c]).mp hregS).2
    exact IsRegularLocalRing.subsingleton_ext_of_regular_sequence S Q [c] hrest
      (fun z hz => by
        obtain rfl := List.mem_singleton.mp hz
        exact hcmax)
      hQ' d hd q (by change q + 1 ≠ d; omega)

private theorem canonicalExt_regular
    (S B : Type u) [CommRing S] [IsRegularLocalRing S]
    [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [IsDomain B] [IsIntegrallyClosed B] [Algebra S B]
    [IsLocalHom (algebraMap S B)] (hsurj : Function.Surjective (algebraMap S B))
    (d r q : ℕ) (hd : ringKrullDim S = (d : ℕ))
    (hr : ringKrullDim B = (r : ℕ)) (hr2 : r ≤ 2) (hqr : q + r = d)
    (a : S) (ha0 : algebraMap S B a ≠ 0) :
    IsSMulRegular (Ext.{u} (ModuleCat.of S B) (ModuleCat.of S S) q) a := by
  by_cases ha : IsUnit a
  · exact ha.isSMulRegular (Ext.{u} (ModuleCat.of S B) (ModuleCat.of S S) q)
  have haReg : IsSMulRegular B a := by
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro b hb
    exact (mul_eq_zero.mp ((Algebra.smul_def a b).symm.trans hb)).resolve_left ha0
  let : Subsingleton (Ext.{u} (ModuleCat.of S (QuotSMulTop a B))
      (ModuleCat.of S S) q) :=
    canonicalQuotientExt_vanish S B hsurj d r q hd hr hr2 hqr a ha0
      (map_nonunit (algebraMap S B) a ha)
  exact ModuleCat.isSMulRegular_ext_of_subsingleton_quotSMulTop
    (ModuleCat.of S B) (ModuleCat.of S S) a haReg q

private theorem cartierTensorSection_section {D X : Scheme.{u}} (i : D ⟶ X)
    (M : X.Modules) (U : X.Opens) (m : Γ(M, U)) :
    ((cartierTensorSection i).app M).val.app (op U) m =
      moduleTensorSection X (dualSheaf X (idealModule i)) M U
        ((cartierDualIdealSection i).val.app (op U) (1 : Γ(X, U))) m := by
  let f := (moduleTensorCoefficientMap X (cartierDualIdealSection i)).app M
  change f.val.app (op U) ((tensorSheafLeftUnit X M).inv.val.app (op U) m) = _
  exact (congrArg (fun z : Γ((moduleTensorLeftFunctor X
      (SheafOfModules.unit X.ringCatSheaf)).obj M, U) => f.val.app (op U) z)
    (leftUnitor_inv_moduleTensorSection M U m)).trans
      (moduleTensorCoefficientMap_section (cartierDualIdealSection i) M U (1 : Γ(X, U)) m)

private theorem cartierTensorSection_kernel_smul {D X : Scheme.{u}} (i : D ⟶ X)
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules)
    (U : X.Opens) (σ : Γ(idealModule i, U)) (m : Γ(M, U))
    (hm : ((cartierTensorSection i).app M).val.app (op U) m = 0) :
    (show Γ(X, U) from (idealInclusion i).val.app (op U) σ) • m = 0 := by
  let I : X.Modules := idealModule i
  let L : X.Modules := dualSheaf X I
  let s : Γ(L, U) := (cartierDualIdealSection i).val.app (op U) (1 : Γ(X, U))
  let e₀ := dualEvaluationIso X ⟨idealModule i, hI⟩
  let e : (L ⊗ I : X.Modules) ≅ 𝟙_ X.Modules :=
    ⟨e₀.hom, e₀.inv, e₀.hom_inv_id, e₀.inv_hom_id⟩
  have hev : (show Γ(X, U) from e.hom.val.app (op U)
      (moduleTensorSection X L I U s σ)) =
      (show Γ(X, U) from (idealInclusion i).val.app (op U) σ) := by
    have h := congrArg (fun f : I ⟶ SheafOfModules.unit X.ringCatSheaf =>
      f.val.app (op U) σ) (cartierTensorSection_evaluation i hI)
    change e.hom.val.app (op U)
      (((cartierTensorSection i).app I).val.app (op U) σ) = _ at h
    rw [cartierTensorSection_section] at h
    exact h
  have hc : (cartierCoefficientCancellationIso i hI M).hom.val.app (op U)
      (moduleTensorSection X (L ⊗ M) I U
        (((cartierTensorSection i).app M).val.app (op U) m) σ) =
      (show Γ(X, U) from (idealInclusion i).val.app (op U) σ) • m := by
    let f₁ : Γ((L ⊗ M) ⊗ I, U) → Γ(L ⊗ (M ⊗ I), U) :=
      fun t => (α_ L M I).hom.val.app (op U) t
    let f₂ : Γ(L ⊗ (M ⊗ I), U) → Γ(L ⊗ (I ⊗ M), U) :=
      fun t => (L ◁ (β_ M I).hom).val.app (op U) t
    let f₃ : Γ(L ⊗ (I ⊗ M), U) → Γ((L ⊗ I) ⊗ M, U) :=
      fun t => (α_ L I M).inv.val.app (op U) t
    let f₄ : Γ((L ⊗ I) ⊗ M, U) →
        Γ((moduleTensorLeftFunctor X (SheafOfModules.unit X.ringCatSheaf)).obj M, U) :=
      fun t => (e.hom ▷ M).val.app (op U) t
    let f₅ : Γ((moduleTensorLeftFunctor X (SheafOfModules.unit X.ringCatSheaf)).obj M, U) →
        Γ(M, U) := fun t => (λ_ M).hom.val.app (op U) t
    let ev : Γ(X, U) := e.hom.val.app (op U) (moduleTensorSection X L I U s σ)
    have h₀ : f₁ (moduleTensorSection X (L ⊗ M) I U
        (((cartierTensorSection i).app M).val.app (op U) m) σ) =
        moduleTensorSection X L (M ⊗ I) U s (moduleTensorSection X M I U m σ) :=
      (congrArg (fun t : Γ(L ⊗ M, U) =>
        f₁ (moduleTensorSection X (L ⊗ M) I U t σ))
        (cartierTensorSection_section i M U m)).trans
          (associator_hom_moduleTensorSection L M I U s m σ)
    have h₂ : f₂ (moduleTensorSection X L (M ⊗ I) U s
        (moduleTensorSection X M I U m σ)) =
        moduleTensorSection X L (I ⊗ M) U s (moduleTensorSection X I M U σ m) :=
      (whiskerLeft_moduleTensorSection L (β_ M I).hom U s
        (moduleTensorSection X M I U m σ)).trans
          (congrArg (fun t : Γ(I ⊗ M, U) => moduleTensorSection X L (I ⊗ M) U s t)
            (braiding_hom_moduleTensorSection M I U m σ))
    have h₃ : f₃ (moduleTensorSection X L (I ⊗ M) U s
        (moduleTensorSection X I M U σ m)) =
        moduleTensorSection X (L ⊗ I) M U (moduleTensorSection X L I U s σ) m :=
      associator_inv_moduleTensorSection L I M U s σ m
    have h₄ : f₄ (moduleTensorSection X (L ⊗ I) M U
        (moduleTensorSection X L I U s σ) m) =
        moduleTensorSection X (SheafOfModules.unit X.ringCatSheaf) M U ev m :=
      whiskerRight_moduleTensorSection e.hom M U (moduleTensorSection X L I U s σ) m
    have h₅ : f₅ (moduleTensorSection X (SheafOfModules.unit X.ringCatSheaf) M U ev m) =
        ev • m := tensorLeftUnitIso_hom_section X M U ev m
    change f₅ (f₄ (f₃ (f₂ (f₁ (moduleTensorSection X (L ⊗ M) I U
      (((cartierTensorSection i).app M).val.app (op U) m) σ))))) = _
    exact (congrArg (fun t => f₅ (f₄ (f₃ (f₂ t)))) h₀).trans
      ((congrArg (fun t => f₅ (f₄ (f₃ t))) h₂).trans
        ((congrArg (fun t => f₅ (f₄ t)) h₃).trans
          ((congrArg f₅ h₄).trans
            (h₅.trans (congrArg (fun r : Γ(X, U) => r • m) hev)))))
  have hz : moduleTensorSection X (L ⊗ M) I U
      (((cartierTensorSection i).app M).val.app (op U) m) σ = 0 := by
    rw [hm]
    change moduleTensorSectionLinear X (L ⊗ M) I U
      ((0 : Γ(L ⊗ M, U)) ⊗ₜ[Γ(X, U)] σ) = 0
    rw [TensorProduct.zero_tmul, map_zero]
  exact hc.symm.trans ((congrArg
    (fun t : Γ((L ⊗ M) ⊗ I, U) =>
      (cartierCoefficientCancellationIso i hI M).hom.val.app (op U) t) hz).trans
        ((cartierCoefficientCancellationIso i hI M).hom.val.app (op U)).hom.map_zero)

private theorem cartierTensorSection_mono_of_stalk_regular
    {D X : Scheme.{u}} [IsIntegral X] (i : D ⟶ X)
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules)
    (hM : ∀ (x : X) (a : X.presheaf.stalk x), a ≠ 0 →
      IsSMulRegular ((moduleStalk X x).obj M) a) :
    Mono ((cartierTensorSection i).app M) := by
  let τ := (cartierTensorSection i).app M
  let N := (moduleTensorLeftFunctor X (dualSheaf X (idealModule i))).obj M
  apply moduleHom_mono_of_app_injective τ
  intro U
  rw [injective_iff_map_eq_zero]
  intro m hm
  apply TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) U m 0
  intro x hxU
  obtain ⟨V, _, hxV, a, ha, hker⟩ :=
    exists_affine_regular_idealGenerator_of_isLocallyRankOne i hI x
  let : Nonempty V := ⟨⟨x, hxV⟩⟩
  have ha0 : a ≠ 0 := by
    intro h
    have hone : (1 : Γ(X, V)) = 0 := ha (by simp only [h, zero_smul])
    exact one_ne_zero hone
  let aI : RingHom.ker (i.app V).hom := ⟨a, by
    rw [hker]
    exact Ideal.mem_span_singleton_self a⟩
  let EI : Γ(idealModule i, V) ≃ₗ[Γ(X, V)] RingHom.ker (i.app V).hom :=
    idealSectionsEquiv i V
  let σ : Γ(idealModule i, V) := EI.symm aI
  have hσ : (show Γ(X, V) from (idealInclusion i).val.app (op V) σ) = a :=
    (idealSectionsEquiv_val i V σ).symm.trans
      (congrArg Subtype.val (EI.apply_symm_apply aI))
  let W : X.Opens := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let u : W ⟶ U := homOfLE inf_le_left
  let v : W ⟶ V := homOfLE inf_le_right
  let mW : Γ(M, W) := M.presheaf.map u.op m
  let σW : Γ(idealModule i, W) := (idealModule i).presheaf.map v.op σ
  let aW : Γ(X, W) := X.presheaf.map v.op a
  have hmW : τ.val.app (op W) mW = 0 := by
    have h := ConcreteCategory.congr_hom (τ.mapPresheaf.naturality u.op) m
    change τ.app W mW = N.presheaf.map u.op (τ.app U m) at h
    exact h.trans ((congrArg (fun z : Γ(N, U) => N.presheaf.map u.op z) hm).trans
      (N.presheaf.map u.op).hom.map_zero)
  have hσW : (show Γ(X, W) from (idealInclusion i).val.app (op W) σW) = aW := by
    have h := ConcreteCategory.congr_hom
      ((idealInclusion i).mapPresheaf.naturality v.op) σ
    change (idealInclusion i).val.app (op W) σW =
      X.presheaf.map v.op ((idealInclusion i).val.app (op V) σ) at h
    exact h.trans (congrArg (fun b : Γ(X, V) => X.presheaf.map v.op b) hσ)
  have hmul : aW • mW = 0 := by
    have h := cartierTensorSection_kernel_smul i hI M W σW mW hmW
    rwa [hσW] at h
  have hagerm : X.presheaf.germ W x hxW aW ≠ 0 := by
    intro h
    apply ha0
    apply germ_injective_of_isIntegral X x hxV
    exact (X.presheaf.germ_res_apply v x hxW a).symm.trans
      (h.trans (X.presheaf.germ V x hxV).hom.map_zero.symm)
  have hsmul : M.presheaf.germ W x hxW (aW • mW) =
      X.presheaf.germ W x hxW aW • M.presheaf.germ W x hxW mW :=
    PresheafOfModules.germ_smul M.val x W hxW aW mW
  have hg : X.presheaf.germ W x hxW aW • M.presheaf.germ W x hxW mW = 0 :=
    hsmul.symm.trans ((congrArg (fun z : Γ(M, W) => M.presheaf.germ W x hxW z) hmul).trans
      (M.presheaf.germ W x hxW).hom.map_zero)
  have hz : M.presheaf.germ W x hxW mW = 0 :=
    (hM x (X.presheaf.germ W x hxW aW) hagerm).right_eq_zero_of_smul hg
  change M.presheaf.germ U x hxU m = M.presheaf.germ U x hxU 0
  exact (M.presheaf.germ_res_apply u x hxW m).symm.trans
    (hz.trans (M.presheaf.germ U x hxU).hom.map_zero.symm)

@[expose] public section

namespace AlgebraicGeometry.Scheme.Cohomology

open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.FiniteSourceStalk

/-- The standard derived-category model for module sheaves in the Cartier regularity comparison. -/
local instance cartierRegularitySchemeDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
  (ι : Type u) {X : Scheme.{u}} [IsIntegral X]
  (j : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion j]
  [IsDominant (j ≫ toSpec R ι)]
  (hX : NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
  (n : ℕ) (e : ι ≃ Fin (n + 1))
  (hfin : (genericImageBaseMap R ι j).Finite)

include hX hXdim e hfin

/-- Every nonzero original local scalar is regular on the OWN canonical
homology stalk, through the original ambient-linear Ext comparison. -/
theorem normalSurfaceCanonical_stalk_regular (x : X) (b : X.presheaf.stalk x)
    (hb : b ≠ 0) :
    IsSMulRegular ((moduleStalk X x).obj (normalSurfaceCanonicalModule R ι j n)) b := by
  let : Finite ι := Finite.of_equiv _ e.symm
  have := normalSurfaceAmbientCoefficient_finitePresentation R ι n e
  obtain ⟨k, y, hy⟩ := normalSurface_exists_polynomialPoint R ι (j x)
  let P : CommRingCat.{u} := .of (MvPolynomial {l : ι // l ≠ k} R)
  let v := eulerPolynomialChart R ι k
  let C := closedImmersionAffineQuotientChart j P v
  let : IsClosedImmersion (Spec.map (quotientMap C.ideal)) :=
    quotientClosedImmersion C.ideal
  obtain ⟨z, rfl, hzy⟩ := C.exists_point x y hy.symm
  let y' : Spec P := imagePoint C.ideal z
  let S : CommRingCat.{u} := ambientRing C.ideal z
  let B : CommRingCat.{u} := sourceRing C.ideal z
  let f : S ⟶ B := FiniteSourceStalk.stalkMap C.ideal z
  let eB := (asIso (C.sourceMap.stalkMap z)).commRingCatIsoToRingEquiv
  let eS := (asIso (v.stalkMap y')).commRingCatIsoToRingEquiv
  let : IsDomain (X.presheaf.stalk (C.sourceMap z)) := (hX _).1
  let : IsIntegrallyClosed (X.presheaf.stalk (C.sourceMap z)) := (hX _).2
  let : IsDomain B := eB.symm.toMulEquiv.isDomain _
  let : IsIntegrallyClosed B := IsIntegrallyClosed.of_equiv eB
  let : IsRegularLocalRing S := normalSurface_polynomialStalk_regular R ι k y'
  let := f.hom.toAlgebra
  have hf : Function.Surjective f.hom :=
    (Spec.map (quotientMap C.ideal)).stalkMap_surjective z
  let : IsLocalHom (algebraMap S B) := IsLocalHom.of_surjective (algebraMap S B) hf
  obtain ⟨a, ha⟩ := hf (eB b)
  have ha0 : algebraMap S B a ≠ 0 := by
    change f.hom a ≠ 0
    rw [ha]
    exact fun h => hb (eB.injective (h.trans eB.map_zero.symm))
  obtain ⟨d, r, hdX, hrX, hr2, _⟩ :=
    normalSurface_localVanishing R ι j hX hXdim n e (C.sourceMap z)
  have hv : v y' = j (C.sourceMap z) := (congrArg v hzy).trans hy
  have hd : ringKrullDim S = (d : ℕ) := by
    rw [← ringKrullDim_eq_of_ringEquiv eS, hv]
    exact hdX
  have hr : ringKrullDim B = (r : ℕ) := by
    rw [← ringKrullDim_eq_of_ringEquiv eB]
    exact hrX
  have hnr : n + r = d := by
    have h := normalSurface_stalk_dimension R ι j hX hXdim n e hfin (C.sourceMap z)
    rw [hdX, hrX] at h
    exact_mod_cast h.symm
  let L := (normalSurfaceAmbientCoefficient R ι n).restrict v
  have : L.IsFinitePresentation := finitePresentation_restrict v _
  let J := injectiveResolution L
  let Q := (moduleStalk (Spec (.of (P ⧸ C.ideal))) z).obj
    (derivedClosedImmersionRightAdjointHomology (Spec.map (quotientMap C.ideal)) L (n : ℤ))
  let eSource : ModuleCat.of S B ≅
      (ModuleCat.restrictScalars f.hom).obj (ModuleCat.of B B) :=
    (LinearEquiv.refl S B).toModuleIso
  let E := (derivedClosedImmersionRightAdjointQuotientStalkExtLinearEquiv C.ideal J z n).trans
    ((Ext.precompLinearEquiv S eSource ((moduleStalk (Spec P) y').obj L) n).trans
      (Ext.postcompLinearEquiv S (normalSurfacePolynomialCoefficientStalkIso R ι n e k y')
        (ModuleCat.of S B) n))
  have hExt : IsSMulRegular (Ext.{u} (ModuleCat.of S B) (ModuleCat.of S S) n) a :=
    canonicalExt_regular S B hf d r n hd hr hr2 hnr a ha0
  have hQres : IsSMulRegular ((ModuleCat.restrictScalars f.hom).obj Q) a :=
    (E.isSMulRegular_congr a).mpr hExt
  have hQ : IsSMulRegular Q (eB b) := by
    intro m₁ m₂ h
    apply hQres
    change f.hom a • m₁ = f.hom a • m₂
    simpa only [ha] using h
  let eOpen := (moduleStalk (Spec (.of (P ⧸ C.ideal))) z).mapIso
    (derivedClosedImmersionRightAdjointOpenHomologyIso C.sourceMap
      (Spec.map (quotientMap C.ideal)) j v C.square (normalSurfaceAmbientCoefficient R ι n)
      (n : ℤ))
  let QOpen := (moduleStalk (Spec (.of (P ⧸ C.ideal))) z).obj
    ((Scheme.Modules.restrictFunctor C.sourceMap).obj (normalSurfaceCanonicalModule R ι j n))
  have hOpen : IsSMulRegular QOpen (eB b) :=
    (eOpen.toLinearEquiv.isSMulRegular_congr (eB b)).mpr hQ
  have hRestricted : IsSMulRegular
      ((ModuleCat.restrictScalars (C.sourceMap.stalkMap z).hom).obj QOpen) b := by
    intro m₁ m₂ h
    have h' : (eB b) • (show QOpen from m₁) = (eB b) • (show QOpen from m₂) := h
    exact hOpen h'
  let eOriginal := (restrictModuleStalkIso C.sourceMap z).app
    (normalSurfaceCanonicalModule R ι j n)
  exact (eOriginal.toLinearEquiv.isSMulRegular_congr b).mp hRestricted

/-- The original Cartier tensor section is monic on the actual chosen-embedding
normal-surface canonical module. Its coefficient regularity is derived. -/
theorem normalSurfaceCanonical_cartierSection_mono {D : Scheme.{u}}
    (i : D ⟶ X)
    (hI : IsLocallyRankOne X (idealModule i)) :
    Mono ((cartierTensorSection i).app (normalSurfaceCanonicalModule R ι j n)) :=
  cartierTensorSection_mono_of_stalk_regular i hI (normalSurfaceCanonicalModule R ι j n)
    (normalSurfaceCanonical_stalk_regular R ι j hX hXdim n e hfin)

end AlgebraicGeometry.Scheme.Cohomology
