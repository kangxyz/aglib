/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.Proper
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.PGroupModuleSheaves
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteEtaleTrivialization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureKernels
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureCokernels
public import Aglib.AlgebraicGeometry.EtaleCohomology.ModuleCoefficients.FiniteEtaleDescent
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisSylowCover
public import Aglib.AlgebraicGeometry.Geometrically.Connected.PointedCurve
public import Aglib.AlgebraicGeometry.EtaleCohomology.Coefficients.ModuleCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying
public import Aglib.CategoryTheory.Sites.SheafCohomology.Vanishing.ExactSequence
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ConstantUnderlyingCohomology
public import Mathlib.Algebra.Field.ZMod

/-!
# Proper-curve vanishing for actual finite coefficient modules

The proof uses cyclic vanishing, the original tensor comparison, genuine
p-group extension induction, the actual Sylow quotient and coprime trace
retraction, and kernel/cokernel induction on a positive annihilator. Native
lifted-ZMod module-unit Ext vanishing retains independent Ext universes.
No curve duality, Weil pairing, rank formula or open completion is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

open Constructible.Modules

universe u r w w'

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  Coefficients.hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

private theorem nsmul_id_naturality {C : Type*} [Category* C] [Preadditive C]
    (p : ℕ) {A B : C} (f : A ⟶ B) :
    f ≫ (p • 𝟙 B) = (p • 𝟙 A) ≫ f := by
  simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id, Category.id_comp]

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : FScheme k) (hX : Curve.Properties X)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)]

include hX

/-- The actual prime-field constant coefficient has zero cohomology above
degree two, by the existing cyclic and roots vanishing theorem. -/
theorem primeField_subsingleton_H_of_proper_curve
    (p : ℕ) [Fact p.Prime] (hunit : IsUnit (p : k)) (q : ℕ) (hq : 2 < q) :
    Subsingleton (Sheaf.H.{w} (primeFieldSheaf X.left p) q) := by
  have hinv : IsUnit (p : Γ(X.left, ⊤)) := by
    simpa only [map_natCast] using
      hunit.map (((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop).hom)
  let : Subsingleton (Sheaf.H.{w}
      (ConstantFinite.coefficient (ULift.{u} (ZMod p)) X.left) q) :=
    constant_subsingleton_H_of_curve hX p (Fact.out : p.Prime).pos hunit hinv q hq
  let e : Sheaf.H.{w} (primeFieldSheaf X.left p) q ≃+
      Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod p)) X.left) q :=
    ((Sheaf.functorH X.left.smallEtaleTopology q).mapIso
      (cyclicPrimeFieldIso X.left p).symm).addCommGroupIsoToAddEquiv
  exact e.injective.subsingleton

/-- Every original finite constant module killed by an invertible prime has
zero cohomology above degree two, retaining its original coefficient action. -/
theorem constantModuleSheaf_subsingleton_H_of_prime_nsmul
    (R : Type r) [CommRing R] [Finite R]
    (p : ℕ) [Fact p.Prime] (hunit : IsUnit (p : k)) (q : ℕ) (hq : 2 < q)
    (M : ModuleCat.{u + 1} R) [Module.Finite R M] (hM : ∀ m : M, p • m = 0) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).obj
      ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)) := by
  let : Finite M := Module.finite_of_finite R
  let mFp : Module (ZMod p) M := AddCommGroup.zmodModule hM
  let : Module (ZMod p) M := mFp
  let fpFinite : Module.Finite (ZMod p) M := Module.Finite.of_finite
  let fpFree : Module.Free (ZMod p) M :=
    @Module.Free.of_divisionRing (ZMod p) M inferInstance inferInstance mFp
  let b : Module.Basis (Fin (Module.finrank (ZMod p) M)) (ZMod p) M :=
    @Module.finBasis (ZMod p) M inferInstance inferInstance mFp fpFree inferInstance fpFinite
  let V : ModuleCat.{u + 1} (ZMod p) := ModuleCat.of (ZMod p) M
  let H : ModuleCat.{u + 1} (ZMod p) ⥤ ModuleCat.{w} (ZMod p) :=
    ModuleCat.Sheaf.constantCohomology X.left.smallEtaleTopology (ZMod p) q
  let : Subsingleton (H.obj (ModuleCat.liftedUnit.{0, u + 1} (ZMod p))) :=
    primeField_subsingleton_H_of_proper_curve X hX p hunit q hq
  have hsurj := ModuleCat.functorTensorComparison_surjective_of_basis.{0, u + 1, w, 0}
    H (M := V) b
  let ht : Unique (H.obj (ModuleCat.liftedUnit.{0, u + 1} (ZMod p)) ⊗[ZMod p] V) :=
    TensorProduct.uniqueLeft (R := ZMod p)
      (M := H.obj (ModuleCat.liftedUnit.{0, u + 1} (ZMod p))) (N := V)
  have hv : Subsingleton (H.obj V) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨a, ha⟩ := hsurj x
    obtain ⟨c, hc⟩ := hsurj y
    have hac : a = c := (ht.uniq a).trans ((ht.uniq c).symm)
    subst c
    exact ha.symm.trans hc
  let : Subsingleton
      ((ModuleCat.Sheaf.constantCohomology X.left.smallEtaleTopology R q).obj M) := by
    change Subsingleton (H.obj V)
    exact hv
  exact ((ModuleCat.Sheaf.constantUnderlyingCohomologyIso
    X.left.smallEtaleTopology R q).app M).toLinearEquiv.injective.subsingleton

/-- Actual prime-killed modules trivialized by an actual p-group finite étale
cover have zero cohomology above degree two on the original proper curve. -/
theorem moduleSheaf_subsingleton_H_of_pGroup_trivialization
    [ConnectedSpace X.left] (R : Type r) [CommRing R] [Finite R]
    (p : ℕ) [Fact p.Prime] (hunit : IsUnit (p : k))
    (Y : Scheme.FiniteEtale X.left) [PreGaloisCategory.IsGalois Y]
    [Surjective Y.obj.hom] [ConnectedSpace Y.obj.left]
    [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]
    (hY : IsPGroup p (Aut Y)) (q : ℕ) (hq : 2 < q)
    (F : ModuleSheaf R X.left) (M : ModuleCat.{u + 1} R) [Module.Finite R M]
    (hM : ∀ m : M, p • m = 0)
    (t : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).obj F) := by
  let : ConnectedSpace X.left := Curve.curveProperties_connectedSpace hX
  apply property_of_pGroup_trivialization Y p hY
    (fun A => Subsingleton
      ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).obj A))
    ?_ ?_ ?_ F M hM t
  · intro N _ hN
    exact constantModuleSheaf_subsingleton_H_of_prime_nsmul X hX R p hunit q hq N hN
  · intro A B e hA
    let := hA
    exact ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).mapIso e).symm.toLinearEquiv
      |>.injective.subsingleton
  · intro S hS h₁ h₃
    let : Subsingleton (Sheaf.H ((S.map (moduleUnderlying R X.left)).X₁) q) := h₁
    let : Subsingleton (Sheaf.H ((S.map (moduleUnderlying R X.left)).X₃) q) := h₃
    exact Sheaf.H.subsingleton_middle_of_shortExact
      (hS.map_of_exact (moduleUnderlying R X.left)) q

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)] in
/-- A connected actual finite étale cover of the original proper curve is
again a proper smooth geometrically connected curve over the same field. -/
theorem curveProperties_of_connected_finiteEtale
    (Y : Scheme.FiniteEtale X.left) [ConnectedSpace Y.obj.left] :
    Curve.Properties (Over.mk (Y.obj.hom ≫ X.hom)) := by
  let Z : FScheme k := Over.mk (Y.obj.hom ≫ X.hom)
  change Curve.Properties Z
  let : ConnectedSpace Z.left := inferInstanceAs (ConnectedSpace Y.obj.left)
  let := hX.smooth
  let := hX.proper
  let : SmoothOfRelativeDimension 1 Z.hom := by
    change SmoothOfRelativeDimension 1 (Y.obj.hom ≫ X.hom)
    have h := smoothOfRelativeDimension_comp 0 1 Y.obj.hom X.hom
    simpa only [Nat.zero_add] using h
  let : IsProper Z.hom := inferInstanceAs (IsProper (Y.obj.hom ≫ X.hom))
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  let : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  let : IsNoetherian Z.left := ⟨⟩
  let : JacobsonSpace Z.left := LocallyOfFiniteType.jacobsonSpace Z.hom
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set Z.left).Nonempty) isOpen_univ.isLocallyClosed
  exact ⟨inferInstance, inferInstance,
    Scheme.geometricallyConnected_of_pointed_proper_smooth_curve Z.hom
      (pointOfClosedPoint Z.hom x hx) (pointOfClosedPoint_comp Z.hom x hx)⟩

omit hX [IsAlgClosed k] in
private theorem moduleSheaf_subsingleton_H_of_finiteEtale_coprime
    (R : Type r) [CommRing R] (Y : Scheme.FiniteEtale X.left)
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y.obj.left)]
    (d : ℕ) (hd : ∀ x : X.left, Y.obj.hom.finrank x = d)
    (F : ModuleSheaf R X.left) (p : ℕ) (hcop : d.Coprime p)
    (hp : p • 𝟙 F = 0) (q : ℕ)
    (hzero : Subsingleton ((ModuleCat.Sheaf.cohomology Y.obj.left.smallEtaleTopology R q).obj
      ((moduleInverseImage R Y.obj.hom).obj F))) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).obj F) := by
  let H := ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q
  let : Subsingleton (Sheaf.H.{w'} ((moduleUnderlying R Y.obj.left).obj
      ((moduleInverseImage R Y.obj.hom).obj F)) q) :=
    hzero
  let : Subsingleton (H.obj ((moduleDirectImage R Y.obj.hom).obj
      ((moduleInverseImage R Y.obj.hom).obj F))) :=
    (Finite.finiteModuleCohomologyDirectImageLinearEquiv R Y.obj.hom
      ((moduleInverseImage R Y.obj.hom).obj F) q).injective.subsingleton
  obtain ⟨r, hr⟩ := exists_finiteEtale_moduleSheafRetraction_map R Y d hd F p hcop hp H
  have hsurj : Function.Surjective r := by
    intro x
    refine ⟨H.map ((moduleImageAdjunction R Y.obj.hom).unit.app F) x, ?_⟩
    exact congrArg (fun a => a x) hr
  exact hsurj.subsingleton

/-- The actual Sylow quotient and the original coprime trace retraction remove
the p-group condition on the finite Galois cover. Its degree need not be
coprime to the coefficient prime. -/
theorem moduleSheaf_subsingleton_H_of_galois_prime_trivialization
    [ConnectedSpace X.left] (R : Type r) [CommRing R] [Finite R]
    (p : ℕ) [Fact p.Prime] (hunit : IsUnit (p : k))
    (Y : Scheme.FiniteEtale X.left) [PreGaloisCategory.IsGalois Y]
    [Surjective Y.obj.hom]
    [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]
    (q : ℕ) (hq : 2 < q)
    (F : ModuleSheaf R X.left) (M : ModuleCat.{u + 1} R) [Module.Finite R M]
    (hM : ∀ m : M, p • m = 0)
    (t : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).obj F) := by
  let : ConnectedSpace X.left := Curve.curveProperties_connectedSpace hX
  let P : Sylow p (Aut Y) := Classical.choice inferInstance
  let Z₀ := Scheme.FiniteEtale.galoisSubgroupQuotient Y P.toSubgroup
  let Z : FScheme k := Over.mk (Z₀.obj.hom ≫ X.hom)
  let V := Scheme.FiniteEtale.galoisSubgroupRelative Y P.toSubgroup
  let : ConnectedSpace Z.left := inferInstanceAs (ConnectedSpace Z₀.obj.left)
  let hZ : Curve.Properties Z := curveProperties_of_connected_finiteEtale X hX Z₀
  let hExtZ : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Z₀.obj.left) := hasExtStandard Z₀.obj.left
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Z₀.obj.left) := hExtZ
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Z.left) := hExtZ
  let : PreGaloisCategory.IsGalois V :=
    Scheme.FiniteEtale.galoisSubgroupRelative_isGalois Y P.toSubgroup
  let : Surjective V.obj.hom :=
    Scheme.FiniteEtale.galoisSubgroupRelative_surjective Y P.toSubgroup
  let : CompactSpace V.obj.left := inferInstanceAs (CompactSpace Y.obj.left)
  let : QuasiSeparatedSpace V.obj.left := inferInstanceAs (QuasiSeparatedSpace Y.obj.left)
  let E := (moduleInverseImage R Z₀.obj.hom).obj F
  have htriangle : V.obj.hom ≫ Z₀.obj.hom = Y.obj.hom :=
    Scheme.FiniteEtale.galoisSubgroupQuotientπ_structure Y P.toSubgroup
  let t' : (moduleInverseImage R V.obj.hom).obj E ≅
      (constantSheaf V.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M :=
    ((moduleInverseImageComp R Z₀.obj.hom V.obj.hom).app F).symm ≪≫
      eqToIso (congrArg (fun f => (moduleInverseImage R f).obj F) htriangle) ≪≫ t
  have hzero : Subsingleton ((ModuleCat.Sheaf.cohomology Z.left.smallEtaleTopology R q).obj E) :=
    moduleSheaf_subsingleton_H_of_pGroup_trivialization Z hZ R p hunit V
      (Scheme.FiniteEtale.galoisSylowRelative_isPGroup Y P) q hq E M hM t'
  exact moduleSheaf_subsingleton_H_of_finiteEtale_coprime X R Z₀
    P.toSubgroup.index (Scheme.FiniteEtale.galoisSubgroupQuotient_finrank Y P.toSubgroup)
    F p (Scheme.FiniteEtale.galoisSylow_index_coprime Y P)
    (moduleSheaf_nsmul_id_eq_zero_of_trivialization R Y.obj.hom F M p hM t) q hzero

omit hX [IsAlgClosed k] [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)] in
private theorem constant_value_nsmul_eq_zero_of_trivialization
    (R : Type r) [CommRing R] [Finite R]
    {S : Scheme.{u}} (f : S ⟶ X.left) [Etale f]
    [ConnectedSpace S] [CompactSpace S] [QuasiSeparatedSpace S]
    (F : ModuleSheaf R X.left) (M : ModuleCat.{u + 1} R) [Module.Finite R M]
    (p : ℕ) (hp : p • 𝟙 F = 0)
    (t : (moduleInverseImage R f).obj F ≅
      (constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    ∀ m : M, p • m = 0 := by
  let Q := moduleInverseImage R f
  let C := constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} R)
  let : (moduleEtaleRestriction R f).Additive :=
    { map_add := by intro A B a b; rfl }
  let : Q.Additive := Functor.additive_of_iso (moduleInverseImageEtaleIso R f).symm
  have hpull : p • 𝟙 (Q.obj F) = 0 := by
    have hmap : Q.map (p • 𝟙 F) = 0 := (congrArg Q.map hp).trans (Q.map_zero F F)
    have hscalar : Q.map (p • 𝟙 F) = p • 𝟙 (Q.obj F) :=
      Q.map_nsmul.trans (congrArg (fun a => p • a) (Q.map_id F))
    exact hscalar.symm.trans hmap
  have hc : p • 𝟙 (C.obj M) = 0 := by
    apply (cancel_epi t.hom).mp
    rw [comp_zero]
    exact (nsmul_id_naturality p t.hom).trans
      ((congrArg (fun a : Q.obj F ⟶ Q.obj F => a ≫ t.hom) hpull).trans zero_comp)
  let : Finite M := Module.finite_of_finite R
  let : IsIso ((moduleConstantAdjunction R S).unit.app M) :=
    moduleConstantUnit_isIso_of_isAddTorsion R S M _root_.isAddTorsion_of_finite
  have hCinj : Function.Injective (C.map : (M ⟶ M) → _) :=
    ((moduleConstantAdjunction R S).bijective_map_of_isIso_unit_app M M).injective
  have hm : p • 𝟙 M = 0 := by
    apply hCinj
    exact (C.map_nsmul.trans (congrArg (fun a => p • a) (C.map_id M))).trans
      (hc.trans (C.map_zero M M).symm)
  intro m
  simpa using congrArg (fun a : M ⟶ M => a m) hm

/-- Every finite-LCC coefficient killed by an invertible prime has zero
original module cohomology above degree two. Its global cover is constructed. -/
theorem moduleSheaf_subsingleton_H_of_prime_nsmul
    (R : Type r) [CommRing R] [Finite R]
    [(forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).Full]
    (p : ℕ) [Fact p.Prime] (hunit : IsUnit (p : k)) (q : ℕ) (hq : 2 < q)
    (F : ModuleSheaf R X.left) (hF : IsFiniteTypeLocallyConstant F)
    (hp : p • 𝟙 F = 0) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).obj F) := by
  let : ConnectedSpace X.left := Curve.curveProperties_connectedSpace hX
  let := hX.proper
  let T := Classical.choice (nonempty_galoisCoverConstantTrivialization F hF)
  let Y := T.cover
  let : PreGaloisCategory.IsGalois Y := T.galois_cover
  let : ConnectedSpace Y.obj.left := T.connected_cover
  let : Surjective Y.obj.hom := T.surjective_cover
  let : CompactSpace Y.obj.left :=
    QuasiCompact.compactSpace_of_compactSpace (Y.obj.hom ≫ X.hom)
  let : QuasiSeparatedSpace Y.obj.left :=
    quasiSeparatedSpace_of_quasiSeparated (Y.obj.hom ≫ X.hom)
  let : Module.Finite R T.value := T.finite_value
  have hM : ∀ m : T.value, p • m = 0 :=
    constant_value_nsmul_eq_zero_of_trivialization X R Y.obj.hom F T.value p hp T.iso
  exact moduleSheaf_subsingleton_H_of_galois_prime_trivialization X hX R p hunit
    Y q hq F T.value hM T.iso

/-- Every finite-LCC coefficient with a positive invertible annihilator has
zero original cohomology above degree two. The prime dévissage uses the actual
kernel and cokernel of scalar multiplication on the same coefficient sheaf. -/
theorem moduleSheaf_subsingleton_H_of_pos_nsmul
    (R : Type r) [CommRing R] [Finite R]
    [(forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).Full]
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (q : ℕ) (hq : 2 < q)
    (F : ModuleSheaf R X.left) (hF : IsFiniteTypeLocallyConstant F)
    (hkill : n • 𝟙 F = 0) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).obj F) := by
  let : IsNoetherianRing R := inferInstance
  induction n using Nat.strong_induction_on generalizing F with
  | h n ih =>
    by_cases h1 : n = 1
    · subst n
      have hzero : IsZero F := (IsZero.iff_id_eq_zero F).mpr
        (by simpa only [one_nsmul] using hkill)
      exact ModuleCat.subsingleton_of_isZero
        ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).map_isZero hzero)
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
      let : Fact p.Prime := ⟨hp⟩
      let m := n / p
      have hm : 0 < m := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
      have hlt : m < n := Nat.div_lt_self hn hp.one_lt
      have hmp : m * p = n := Nat.div_mul_cancel hpn
      have humul : IsUnit ((m : k) * (p : k)) := by
        rw [← Nat.cast_mul, hmp]
        exact hunit
      obtain ⟨hum, hup⟩ := IsUnit.mul_iff.mp humul
      let a : F ⟶ F := m • 𝟙 F
      let i := kernel.ι a
      let S := ShortComplex.cokernelSequence i
      have hS : S.ShortExact := {
        exact := ShortComplex.cokernelSequence_exact i
        mono_f := by change Mono (kernel.ι a); infer_instance
        epi_g := by change Epi (cokernel.π i); infer_instance }
      have hK : IsFiniteTypeLocallyConstant (kernel a) :=
        isFiniteTypeLocallyConstant_kernel a hF hF
      have hQ : IsFiniteTypeLocallyConstant (cokernel i) :=
        isFiniteTypeLocallyConstant_cokernel i hK hF
      have hmK : m • 𝟙 (kernel a) = 0 := by
        apply (cancel_mono i).mp
        rw [Preadditive.nsmul_comp, Category.id_comp, zero_comp]
        simpa only [a, Preadditive.comp_nsmul, Category.comp_id] using kernel.condition a
      have hpa : (p • 𝟙 F) ≫ a = 0 := by
        simpa only [a, Preadditive.nsmul_comp, Category.id_comp, ← mul_nsmul, hmp] using hkill
      let l : F ⟶ kernel a := kernel.lift a (p • 𝟙 F) hpa
      have hl : l ≫ i = p • 𝟙 F := kernel.lift_ι a (p • 𝟙 F) hpa
      have hpQ : p • 𝟙 (cokernel i) = 0 := by
        apply (cancel_epi (cokernel.π i)).mp
        rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero]
        calc
          p • cokernel.π i = (p • 𝟙 F) ≫ cokernel.π i := by
            rw [Preadditive.nsmul_comp, Category.id_comp]
          _ = (l ≫ i) ≫ cokernel.π i := by rw [hl]
          _ = 0 := by rw [Category.assoc, cokernel.condition, comp_zero]
      have hleft : Subsingleton
          ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).obj (kernel a)) :=
        ih m hlt hm hum (kernel a) hK hmK
      have hright : Subsingleton
          ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).obj (cokernel i)) :=
        moduleSheaf_subsingleton_H_of_prime_nsmul X hX R p hup q hq (cokernel i) hQ hpQ
      let : Subsingleton (Sheaf.H ((S.map (moduleUnderlying R X.left)).X₁) q) := hleft
      let : Subsingleton (Sheaf.H ((S.map (moduleUnderlying R X.left)).X₃) q) := hright
      exact Sheaf.H.subsingleton_middle_of_shortExact
        (hS.map_of_exact (moduleUnderlying R X.left)) q

/-- Positive lifted-ZMod finite local systems on the proper curve have zero
original cohomology above degree two, including composite levels and level one. -/
theorem uLiftZMod_moduleSheaf_subsingleton_H_of_curve
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (q : ℕ) (hq : 2 < q)
    (F : ModuleSheaf (ULift.{u + 1} (ZMod n)) X.left)
    (hF : IsFiniteTypeLocallyConstant F) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology
      (ULift.{u + 1} (ZMod n)) q).obj F) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1}).Full :=
    ModuleCat.uLiftZMod_forget₂_full n
  apply moduleSheaf_subsingleton_H_of_pos_nsmul X hX
    (ULift.{u + 1} (ZMod n)) n hn hunit q hq F hF
  apply ObjectProperty.hom_ext
  ext V m
  change n • m = 0
  rw [← Nat.cast_smul_eq_nsmul (R := ULift.{u + 1} (ZMod n))]
  have hnzero : (n : ULift.{u + 1} (ZMod n)) = 0 := by
    apply ULift.ext
    simp
  rw [hnzero, zero_smul]

/-- The same proper finite-LCC vanishing on the original native unit-Ext
carrier. Module and abelian Ext universes remain independent. -/
theorem moduleUnitExt_subsingleton_of_finiteLocallyConstant
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (q : ℕ) (hq : 2 < q)
    [HasExt.{w'} (Coefficients.ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
    (M : Coefficients.ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))
    (hM : IsFiniteTypeLocallyConstant
      ((Coefficients.moduleSheafEquivalence X.left (ULift.{u + 1} (ZMod n))).inverse.obj M)) :
    Subsingleton (CategoryTheory.Abelian.Ext.{w'}
      (moduleUnit X.left (ULift.{u + 1} (ZMod n))) M q) := by
  let F := (Coefficients.moduleSheafEquivalence X.left (ULift.{u + 1} (ZMod n))).inverse.obj M
  let : Subsingleton (Sheaf.H.{w}
      ((moduleUnderlying (ULift.{u + 1} (ZMod n)) X.left).obj F) q) :=
    uLiftZMod_moduleSheaf_subsingleton_H_of_curve X hX n hn hunit q hq F hM
  let E : CategoryTheory.Abelian.Ext.{w'}
      (moduleUnit X.left (ULift.{u + 1} (ZMod n))) M q ≃+
      Sheaf.H.{w} ((moduleUnderlying (ULift.{u + 1} (ZMod n)) X.left).obj F) q :=
    (etaleModuleExtCohomologyAddEquivLargeScalars X.left
    (Coefficients.constantRing X.left (ULift.{u + 1} (ZMod n))) M q).trans
      (((Sheaf.functorH X.left.smallEtaleTopology q).mapIso
        ((Coefficients.moduleSheafInverseUnderlyingIso X.left
          (ULift.{u + 1} (ZMod n))).app M).symm).addCommGroupIsoToAddEquiv)
  exact E.injective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
