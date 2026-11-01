/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.PGroupModuleSheaves
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteEtaleTrivialization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureKernels
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureCokernels
public import Aglib.AlgebraicGeometry.EtaleCohomology.ModuleCoefficients.FiniteEtaleDescent
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisSylowCover
public import Aglib.CategoryTheory.Sites.SheafCohomology.Vanishing.ExactSequence
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ConstantUnderlyingCohomology
public import Mathlib.Algebra.Field.ZMod
public import Aglib.CategoryTheory.Adjunction.Unit

/-!
# Finite local systems from their original finite-étale prime constant tests

This coefficient-level family uses the existing original constant module,
Galois trivialization, p-group induction and coprime image-unit retraction.
Actual scalar-multiplication kernels and cokernels supply positive-annihilator
induction. Only constant prime-field cohomology on the actual finite étale
tests is supplied; no geometric curve or duality hypothesis enters here.
The original R-valued coefficient and cohomology action are retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r w

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- This coefficient-only induction retains the actual kernel and cokernel.
Only prime divisors of the original positive annihilator are tested. -/
private theorem property_of_positive_annihilator
    {X : Scheme.{u}} (R : Type r) [CommRing R] [IsNoetherianRing R]
    (P : ModuleSheaf R X → Prop)
    (hzero : ∀ F : ModuleSheaf R X, IsZero F → P F)
    (hstep : ∀ S : ShortComplex (ModuleSheaf R X), S.ShortExact →
      P S.X₁ → P S.X₃ → P S.X₂)
    (n : ℕ) (hn : 0 < n)
    (hprime : ∀ (p : ℕ), p.Prime → p ∣ n →
      ∀ (F : ModuleSheaf R X), IsFiniteTypeLocallyConstant F → p • 𝟙 F = 0 → P F)
    (F : ModuleSheaf R X) (hF : IsFiniteTypeLocallyConstant F) (hkill : n • 𝟙 F = 0) :
    P F := by
  suffices ∀ m : ℕ, 0 < m → m ∣ n → ∀ F : ModuleSheaf R X,
      IsFiniteTypeLocallyConstant F → m • 𝟙 F = 0 → P F from
    this n hn (dvd_refl n) F hF hkill
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm hmn F hF hk
    by_cases h1 : m = 1
    · apply hzero F
      apply (IsZero.iff_id_eq_zero F).mpr
      simpa only [h1, one_nsmul] using hk
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd h1
    let a : F ⟶ F := (m / p) • 𝟙 F
    let i := kernel.ι a
    let S := ShortComplex.cokernelSequence i
    have hS : S.ShortExact := {
      exact := ShortComplex.cokernelSequence_exact i
      mono_f := by change Mono (kernel.ι a); infer_instance }
    have hK : IsFiniteTypeLocallyConstant (kernel a) :=
      isFiniteTypeLocallyConstant_kernel a hF hF
    have hQ : IsFiniteTypeLocallyConstant (cokernel i) :=
      isFiniteTypeLocallyConstant_cokernel i hK hF
    have hmK : (m / p) • 𝟙 (kernel a) = 0 := by
      apply (cancel_mono i).mp
      rw [Preadditive.nsmul_comp, Category.id_comp, zero_comp]
      simpa only [a, Preadditive.comp_nsmul, Category.comp_id] using kernel.condition a
    have hmp : (m / p) * p = m := Nat.div_mul_cancel hpm
    have hpa : (p • 𝟙 F) ≫ a = 0 := by
      simpa only [a, Preadditive.nsmul_comp, Category.id_comp, ← mul_nsmul, hmp] using hk
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
    have hdiv : m / p ∣ n := (show m / p ∣ m from ⟨p, hmp.symm⟩).trans hmn
    exact hstep S hS
      (ih (m / p) (Nat.div_lt_self hm hp.one_lt)
        (Nat.div_pos (Nat.le_of_dvd hm hpm) hp.pos) hdiv (kernel a) hK hmK)
      (hprime p hp (hpm.trans hmn) (cokernel i) hQ hpQ)

/-- An actual constant trivialization detects the original scalar annihilator. -/
private theorem value_annihilator_of_trivialization
    {X Y : Scheme.{u}} (R : Type r) [CommRing R] [Finite R]
    (f : Y ⟶ X) [Etale f] [ConnectedSpace Y] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (F : ModuleSheaf R X) (M : ModuleCat.{u + 1} R) [Module.Finite R M]
    (p : ℕ) (hp : p • 𝟙 F = 0)
    (t : (moduleInverseImage R f).obj F ≅
      (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    ∀ m : M, p • m = 0 := by
  let Q := moduleInverseImage R f
  let C := constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)
  let : (moduleEtaleRestriction R f).Additive := { map_add := by intro A B a b; rfl }
  let : Q.Additive := Functor.additive_of_iso (moduleInverseImageEtaleIso R f).symm
  have hpull : p • 𝟙 (Q.obj F) = 0 := by
    have hmap : Q.map (p • 𝟙 F) = 0 := (congrArg Q.map hp).trans (Q.map_zero F F)
    have hscalar : Q.map (p • 𝟙 F) = p • 𝟙 (Q.obj F) :=
      Q.map_nsmul.trans (congrArg (fun a => p • a) (Q.map_id F))
    exact hscalar.symm.trans hmap
  have hc : p • 𝟙 (C.obj M) = 0 := by
    apply (cancel_epi t.hom).mp
    rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero]
    have h := (congrArg (fun a : Q.obj F ⟶ Q.obj F => a ≫ t.hom) hpull).trans zero_comp
    simpa only [Preadditive.nsmul_comp, Category.id_comp] using h
  let : Finite M := Module.finite_of_finite R
  let : IsIso ((moduleConstantAdjunction R Y).unit.app M) :=
    moduleConstantUnit_isIso_of_isAddTorsion R Y M _root_.isAddTorsion_of_finite
  have hCinj : Function.Injective (C.map : (M ⟶ M) → _) :=
    ((moduleConstantAdjunction R Y).bijective_map_of_isIso_unit_app M M).injective
  have hm : p • 𝟙 M = 0 := by
    apply hCinj
    exact (C.map_nsmul.trans (congrArg (fun a => p • a) (C.map_id M))).trans
      (hc.trans (C.map_zero M M).symm)
  intro m
  simpa using congrArg (fun a : M ⟶ M => a m) hm

/-- A finite prime-killed constant module reduces to its original prime-field
constant coefficient, without changing the target cohomology scalar action. -/
theorem constantCohomology_subsingleton_of_prime_field
    (X : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    (R : Type r) [CommRing R] [Finite R] (p : ℕ) [Fact p.Prime] (q : ℕ)
    (hzero : Subsingleton (Sheaf.H.{w} (primeFieldSheaf X p) q))
    (M : ModuleCat.{u + 1} R) [Module.Finite R M] (hM : ∀ m : M, p • m = 0) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.smallEtaleTopology R q).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)) := by
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
    ModuleCat.Sheaf.constantCohomology X.smallEtaleTopology (ZMod p) q
  let : Subsingleton (H.obj (ModuleCat.liftedUnit.{0, u + 1} (ZMod p))) := hzero
  have hsurj := ModuleCat.functorTensorComparison_surjective_of_basis.{0, u + 1, w, 0}
    H (M := V) b
  let ht : Unique (H.obj (ModuleCat.liftedUnit.{0, u + 1} (ZMod p)) ⊗[ZMod p] V) :=
    TensorProduct.uniqueLeft (R := ZMod p)
      (M := H.obj (ModuleCat.liftedUnit.{0, u + 1} (ZMod p))) (N := V)
  have hv : Subsingleton (H.obj V) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨a, ha⟩ := hsurj x
    obtain ⟨c, hc⟩ := hsurj y
    have hac : a = c := (ht.uniq a).trans (ht.uniq c).symm
    subst c
    exact ha.symm.trans hc
  let : Subsingleton
      ((ModuleCat.Sheaf.constantCohomology X.smallEtaleTopology R q).obj M) := by
    change Subsingleton (H.obj V)
    exact hv
  exact ((ModuleCat.Sheaf.constantUnderlyingCohomologyIso
    X.smallEtaleTopology R q).app M).toLinearEquiv.injective.subsingleton


/-- The original p-group property induction applies to the original
cohomology functor once its actual prime-field constant value vanishes. -/
theorem moduleSheaf_cohomology_subsingleton_of_pGroup_trivialization
    (X : Scheme.{u}) [ConnectedSpace X] [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    (R : Type r) [CommRing R] [Finite R] (p : ℕ) [Fact p.Prime] (q : ℕ)
    (hconstant : Subsingleton (Sheaf.H.{w} (primeFieldSheaf X p) q))
    (Y : Scheme.FiniteEtale X) [PreGaloisCategory.IsGalois Y] [Surjective Y.obj.hom]
    [ConnectedSpace Y.obj.left] [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]
    (hY : IsPGroup p (Aut Y))
    (F : ModuleSheaf R X) (M : ModuleCat.{u + 1} R) [Module.Finite R M]
    (hM : ∀ m : M, p • m = 0)
    (t : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.smallEtaleTopology R q).obj F) := by
  apply property_of_pGroup_trivialization Y p hY
    (fun A => Subsingleton ((ModuleCat.Sheaf.cohomology X.smallEtaleTopology R q).obj A))
    ?_ ?_ ?_ F M hM t
  · intro N _ hN
    exact constantCohomology_subsingleton_of_prime_field X R p q hconstant N hN
  · intro A B e hA
    let := hA
    let E := ((ModuleCat.Sheaf.cohomology X.smallEtaleTopology R q).mapIso e).symm.toLinearEquiv
    exact E.injective.subsingleton
  · intro S hS h₁ h₃
    let : Subsingleton (Sheaf.H ((S.map (moduleUnderlying R X)).X₁) q) := h₁
    let : Subsingleton (Sheaf.H ((S.map (moduleUnderlying R X)).X₃) q) := h₃
    exact Sheaf.H.subsingleton_middle_of_shortExact
      (hS.map_of_exact (moduleUnderlying R X)) q

/-- The original Sylow quotient and original coprime trace retraction reduce
a genuine finite Galois trivialization to its prime constant tests. -/
theorem moduleSheaf_cohomology_subsingleton_of_galois_prime_trivialization
    (X : Scheme.{u}) [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    (R : Type r) [CommRing R] [Finite R] (p : ℕ) [Fact p.Prime] (q : ℕ)
    (hconstant : ∀ Y : Scheme.FiniteEtale X,
      let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Y.obj.left) := hasExtStandard Y.obj.left
      Subsingleton (Sheaf.H.{u + 2} (primeFieldSheaf Y.obj.left p) q))
    (Y : Scheme.FiniteEtale X) [PreGaloisCategory.IsGalois Y] [Surjective Y.obj.hom]
    [ConnectedSpace Y.obj.left] [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]
    (F : ModuleSheaf R X) (M : ModuleCat.{u + 1} R) [Module.Finite R M]
    (hM : ∀ m : M, p • m = 0)
    (t : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.smallEtaleTopology R q).obj F) := by
  let P : Sylow p (Aut Y) := Classical.choice inferInstance
  let Z := Scheme.FiniteEtale.galoisSubgroupQuotient Y P.toSubgroup
  let V := Scheme.FiniteEtale.galoisSubgroupRelative Y P.toSubgroup
  let : ConnectedSpace Z.obj.left := inferInstance
  let : CompactSpace Z.obj.left := QuasiCompact.compactSpace_of_compactSpace Z.obj.hom
  let : QuasiSeparatedSpace Z.obj.left := quasiSeparatedSpace_of_quasiSeparated Z.obj.hom
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Z.obj.left) := hasExtStandard Z.obj.left
  let : PreGaloisCategory.IsGalois V :=
    Scheme.FiniteEtale.galoisSubgroupRelative_isGalois Y P.toSubgroup
  let : Surjective V.obj.hom := Scheme.FiniteEtale.galoisSubgroupRelative_surjective Y P.toSubgroup
  let : ConnectedSpace V.obj.left := inferInstanceAs (ConnectedSpace Y.obj.left)
  let : CompactSpace V.obj.left := inferInstanceAs (CompactSpace Y.obj.left)
  let : QuasiSeparatedSpace V.obj.left := inferInstanceAs (QuasiSeparatedSpace Y.obj.left)
  let E := (moduleInverseImage R Z.obj.hom).obj F
  have htriangle : V.obj.hom ≫ Z.obj.hom = Y.obj.hom :=
    Scheme.FiniteEtale.galoisSubgroupQuotientπ_structure Y P.toSubgroup
  let t' : (moduleInverseImage R V.obj.hom).obj E ≅
      (constantSheaf V.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M :=
    ((moduleInverseImageComp R Z.obj.hom V.obj.hom).app F).symm ≪≫
      eqToIso (congrArg (fun f => (moduleInverseImage R f).obj F) htriangle) ≪≫ t
  have hzero : Subsingleton ((ModuleCat.Sheaf.cohomology
      Z.obj.left.smallEtaleTopology R q).obj E) :=
    moduleSheaf_cohomology_subsingleton_of_pGroup_trivialization Z.obj.left R p q
      (hconstant Z) V (Scheme.FiniteEtale.galoisSylowRelative_isPGroup Y P) E M hM t'
  let H := ModuleCat.Sheaf.cohomology X.smallEtaleTopology R q
  let : Subsingleton (Sheaf.H.{u + 2} ((moduleUnderlying R Z.obj.left).obj E) q) := hzero
  let : Subsingleton (H.obj ((moduleDirectImage R Z.obj.hom).obj E)) :=
    (Finite.finiteModuleCohomologyDirectImageLinearEquiv R Z.obj.hom E q).injective.subsingleton
  have hp : p • 𝟙 F = 0 :=
    moduleSheaf_nsmul_id_eq_zero_of_trivialization R Y.obj.hom F M p hM t
  obtain ⟨a, ha⟩ := exists_finiteEtale_moduleSheafRetraction_map R Z
    P.toSubgroup.index (Scheme.FiniteEtale.galoisSubgroupQuotient_finrank Y P.toSubgroup)
    F p (Scheme.FiniteEtale.galoisSylow_index_coprime Y P) hp H
  have hs : Function.Surjective a := by
    intro x
    exact ⟨H.map ((moduleImageAdjunction R Z.obj.hom).unit.app F) x,
      congrArg (fun b => b x) ha⟩
  exact hs.subsingleton

private theorem prime_high_of_constant_tests
    (X : Scheme.{u}) [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    (R : Type r) [CommRing R] [Finite R]
    [(forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).Full]
    (p : ℕ) [Fact p.Prime] (q : ℕ)
    (hconstant : ∀ Y : Scheme.FiniteEtale X,
      let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Y.obj.left) := hasExtStandard Y.obj.left
      Subsingleton (Sheaf.H.{u + 2} (primeFieldSheaf Y.obj.left p) q))
    (F : ModuleSheaf R X) (hF : IsFiniteTypeLocallyConstant F) (hp : p • 𝟙 F = 0) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.smallEtaleTopology R q).obj F) := by
  let T := Classical.choice (nonempty_galoisCoverConstantTrivialization F hF)
  let Y := T.cover
  let : PreGaloisCategory.IsGalois Y := T.galois_cover
  let : ConnectedSpace Y.obj.left := T.connected_cover
  let : Surjective Y.obj.hom := T.surjective_cover
  let : CompactSpace Y.obj.left := QuasiCompact.compactSpace_of_compactSpace Y.obj.hom
  let : QuasiSeparatedSpace Y.obj.left := quasiSeparatedSpace_of_quasiSeparated Y.obj.hom
  let : Module.Finite R T.value := T.finite_value
  have hM : ∀ m : T.value, p • m = 0 :=
    value_annihilator_of_trivialization R Y.obj.hom F T.value p hp T.iso
  exact moduleSheaf_cohomology_subsingleton_of_galois_prime_trivialization
    X R p q hconstant Y F T.value hM T.iso

/-- Vanishing on the actual prime constants of finite étale tests implies
vanishing for the original finite local system with its positive annihilator.
The constant tests use the selected standard abelian Ext construction only;
the original source cohomology world is independent. -/
theorem moduleSheaf_cohomology_subsingleton_of_constant_prime_tests
    (X : Scheme.{u}) [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    (R : Type r) [CommRing R] [Finite R]
    [(forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).Full]
    (n : ℕ) (hn : 0 < n) (q : ℕ)
    (hconstant : ∀ (p : ℕ), p.Prime → p ∣ n → ∀ Y : Scheme.FiniteEtale X,
      let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Y.obj.left) := hasExtStandard Y.obj.left
      Subsingleton (Sheaf.H.{u + 2} (primeFieldSheaf Y.obj.left p) q))
    (F : ModuleSheaf R X) (hF : IsFiniteTypeLocallyConstant F) (hkill : n • 𝟙 F = 0) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.smallEtaleTopology R q).obj F) := by
  let : IsNoetherianRing R := inferInstance
  apply property_of_positive_annihilator R
    (fun A => Subsingleton ((ModuleCat.Sheaf.cohomology X.smallEtaleTopology R q).obj A))
    ?_ ?_ n hn ?_ F hF hkill
  · intro A hA
    exact ModuleCat.subsingleton_of_isZero
      ((ModuleCat.Sheaf.cohomology X.smallEtaleTopology R q).map_isZero hA)
  · intro S hS h₁ h₃
    let : Subsingleton (Sheaf.H ((S.map (moduleUnderlying R X)).X₁) q) := h₁
    let : Subsingleton (Sheaf.H ((S.map (moduleUnderlying R X)).X₃) q) := h₃
    exact Sheaf.H.subsingleton_middle_of_shortExact
      (hS.map_of_exact (moduleUnderlying R X)) q
  · intro p hp hpn A hA hkillA
    let : Fact p.Prime := ⟨hp⟩
    exact prime_high_of_constant_tests X R p q (hconstant p hp hpn) A hA hkillA

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
