/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.PointRemoval
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.PointPurity.Finite
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.CoefficientExactness
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.CoefficientDevissage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ProperCompactFiniteness
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ConstantOnePerfectness
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.FiniteTracePairing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.FiniteTracePairing.Compatibility
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteEtalePresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteEtaleImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.InternalHom
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.LocallyConstantExt
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.FiniteCoefficientsVanishing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.LowerShriekComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.LowerShriekCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.Cohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.FinitePushforward
public import Aglib.AlgebraicGeometry.Curves.FiniteEtaleCompletion
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
/-!
# Finite support and compact vanishing for original curve duality
Finite point coefficients have the original perfect pairing, including empty
support. The original unit has no compact cohomology above degree two.
Finite locally constant coefficients reduce
to that unit case through the original exact extension by zero. Actual Sylow
quotients and finite completions give coprime descent on compact cohomology.
Positive-annihilator kernel/cokernel induction includes composite levels and
level one. The actual proper finite-trace square and compiled source-zero
criteria assemble proper constant H1 perfectness. The whole
smaller-open pairing is preserved under the existing adjunction comparisons.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
universe u v r w wU wX wA wV wP wY uC vC wC
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients Scheme.OverField
attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard moduleSheafExtZModModule
  ModuleCat.Sheaf.hasSheafify
  Abelian.hasFiniteBiproducts
section FinitePointPairing
variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]
/-- Isomorphisms of actual coefficients preserve both adjoints of the original
trace pairing. No finite or free coefficient premise is used. -/
theorem moduleDualityMap_isPerfPair_iff_of_iso
    {F F' : ModuleSheaf U (ULift.{u + 1} (ZMod n))} (a : F ≅ F')
    (r : ℕ) (hr : r ≤ 2) :
    (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv F r hr).IsPerfPair ↔
    (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv F' r hr).IsPerfPair :=
  (Functor.isPerfPair_extPairingLinearMap_compr₂_iso_iff
    (moduleLowerShriek j (ULift.{u + 1} (ZMod n)))
    (moduleUnit X.left (ULift.{u + 1} (ZMod n))) n a r (2 - r) 2 (by lia)
    (moduleCompactSupportTraceLinearMap X hX D hfin hclosed j hD n hn hunit hinv)).symm
/-- The original finite-bicone pairing is perfect componentwise. Keeping
its actual bicone variable fixes the canonical Ext parents before the selected
point-family biproduct is substituted. -/
private theorem moduleDualityMap_bicone_isPerfPair {I : Type v} [Finite I]
    {F : I → ModuleSheaf U (ULift.{u + 1} (ZMod n))} {b : Bicone F} (hb : b.IsBilimit)
    (r : ℕ) (hr : r ≤ 2)
    (hF : ∀ i, (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv
      (F i) r hr).IsPerfPair) :
    (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv b.pt r hr).IsPerfPair := by
  unfold moduleDualityMap moduleTracePairingLinearMap at hF ⊢
  exact Functor.isPerfPair_extPairingLinearMap_compr₂_biproduct.{
      u + 2, u + 1, u + 2, u + 1, wU, wX, v}
    (moduleLowerShriek j (ULift.{u + 1} (ZMod n)))
    (moduleUnit X.left (ULift.{u + 1} (ZMod n))) n hb (moduleRootsOfUnity U n)
    r (2 - r) 2 (by lia)
    (moduleCompactSupportTraceLinearMap X hX D hfin hclosed j hD n hn hunit hinv) hF
/-- A finite support has the original perfect pairing in every allowed degree,
using the already proved whole finite-SUM source comparison, including empty support. -/
theorem moduleDualityMap_finitePoint_isPerfPair
    (T : Set U) (hTfin : T.Finite) (hTclosed : ∀ x ∈ T, IsClosed ({x} : Set U))
    (r : ℕ) (hr : r ≤ 2) :
    (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv
      (moduleFinitePointSource U T n) r hr).IsPerfPair := by
  let : Finite T := hTfin.to_subtype
  let M : T → ModuleSheaf U (ULift.{u + 1} (ZMod n)) := fun x : T =>
    (moduleDirectImage (U.fromSpecResidueField x.val) (ULift.{u + 1} (ZMod n))).obj
      (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n)))
  let a : moduleFinitePointSource U T n ≅ ⨁ M :=
    moduleFinitePointSourceIso U T n hTclosed
  have hM : ∀ x : T, (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv
      (M x) r hr).IsPerfPair := fun x =>
    moduleDualityMap_point_isPerfPair.{u, wU, wX, wA} X hX D hfin hclosed j hD n hn hunit hinv
      ⟨x.val, hTclosed x.val x.property⟩ r hr
  have hsum : (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv
      (⨁ M) r hr).IsPerfPair :=
    moduleDualityMap_bicone_isPerfPair X hX D hfin hclosed j hD n hn hunit hinv
      (biproduct.isBilimit M) r hr hM
  exact (moduleDualityMap_isPerfPair_iff_of_iso X hX D hfin hclosed j hD n hn hunit hinv
    a r hr).mpr hsum
end FinitePointPairing
section CompactConstantVanishing
variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
include hX in
/-- The original finite point-support coefficient has no positive compact
cohomology, by its SAME whole source isomorphism and native Ext decomposition. -/
theorem moduleCompactFinitePointUnitExt_pos_subsingleton
    (T : Set U) (hTfin : T.Finite) (hTclosed : ∀ x ∈ T, IsClosed ({x} : Set U))
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
        (moduleFinitePointSource U T n)) q) := by
  let : Finite T := hTfin.to_subtype
  let : Fintype T := Fintype.ofFinite T
  let Λ := ULift.{u + 1} (ZMod n)
  let L := moduleLowerShriek j Λ
  let A := moduleUnit X.left Λ
  let M := fun x : T => (moduleDirectImage (U.fromSpecResidueField x.val) Λ).obj
    (moduleUnit (Spec (U.residueField x.val)) Λ)
  let (x : T) : Subsingleton (Ext.{wX} A (L.obj (M x)) q) :=
    moduleCompactPointUnitExt_pos_subsingleton X hX j n
      ⟨x.val, hTclosed x.val x.property⟩ q hq
  let E₁ : Ext.{wX} A (L.obj (moduleFinitePointSource U T n)) q ≃+
      Ext.{wX} A (L.obj (⨁ M)) q :=
    ((extFunctorObj A q).mapIso
      (L.mapIso (moduleFinitePointSourceIso U T n hTclosed))).addCommGroupIsoToAddEquiv
  let E₂ : Ext.{wX} A (L.obj (⨁ M)) q ≃+ ∀ x : T, Ext.{wX} A (L.obj (M x)) q :=
    Ext.addEquivBiproduct A (Functor.mapFiniteBiconeIsBilimit L (biproduct.isBilimit M)) q
  exact (E₁.trans E₂).injective.subsingleton
include hX D hfin hclosed hD hn hunit in
/-- Compact support of the original unit vanishes above degree two on the
original finite-complement open. This uses proper finite-LCC vanishing only
on the original proper UNIT, and positive cohomology vanishing of its finite
point boundary; it never treats the extension by zero as locally constant. -/
theorem moduleUnitCompactExt_high_subsingleton (q : ℕ) (hq : 2 < q) :
    Subsingleton (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit U (ULift.{u + 1} (ZMod n)))) q) := by
  cases q with
  | zero => omega
  | succ r =>
    let : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} X.left) := hasExtStandard X.left
    let Λ := ULift.{u + 1} (ZMod n)
    let A := moduleUnit X.left Λ
    let iz := Curves.FiniteClosedSupport.inclusion X.left D
    let : IsClosedImmersion iz :=
      Curves.FiniteClosedSupport.inclusion_isClosedImmersion X.left D hfin hclosed
    have hcomp : Set.range j = (Set.range iz)ᶜ := by
      rw [Curves.FiniteClosedSupport.range_inclusion]
      exact hD
    let S := moduleLocalizationShortComplex j Λ iz hcomp A
    have hS : S.ShortExact := moduleLocalization_shortExact j Λ iz hcomp A
    let : Subsingleton (Ext.{wX} A S.X₂ (r + 1)) :=
      Curves.moduleUnitExt_subsingleton_of_finiteLocallyConstant X hX n hn hunit
        (r + 1) hq A (moduleUnit_isFiniteTypeLocallyConstant X.left Λ)
    let E₃ : Ext.{wX} A S.X₃ r ≃+
        Ext.{wX} A (moduleFinitePointSource X.left D n) r :=
      ((extFunctorObj A r).mapIso
        ((moduleDirectImage iz Λ).mapIso (moduleUnitInverseImageIso iz n)))
        |>.addCommGroupIsoToAddEquiv
    let : Subsingleton (Ext.{wX} A (moduleFinitePointSource X.left D n) r) := by
      let E : Ext.{wX} A
          ((moduleLowerShriek (𝟙 X.left) Λ).obj (moduleFinitePointSource X.left D n)) r ≃+
            Ext.{wX} A (moduleFinitePointSource X.left D n) r :=
        ((extFunctorObj A r).mapIso
          ((moduleLowerShriekIdIso Λ X.left).app (moduleFinitePointSource X.left D n)))
            |>.addCommGroupIsoToAddEquiv
      let : Subsingleton (Ext.{wX} A
          ((moduleLowerShriek (𝟙 X.left) Λ).obj (moduleFinitePointSource X.left D n)) r) :=
        moduleCompactFinitePointUnitExt_pos_subsingleton X hX (𝟙 X.left) n D hfin hclosed r
          (by omega)
      exact E.symm.injective.subsingleton
    let : Subsingleton (Ext.{wX} A S.X₃ r) := E₃.injective.subsingleton
    let : Subsingleton (Ext.{wX} A S.X₁ (r + 1)) := by
      apply subsingleton_of_forall_eq 0
      intro c
      obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₁ A hS c
        (Subsingleton.elim _ _) (n₀ := r) rfl
      exact hb.symm.trans (by rw [Subsingleton.elim b 0, Ext.zero_comp])
    let E₁ : Ext.{wX} A S.X₁ (r + 1) ≃+
        Ext.{wX} A ((moduleLowerShriek j Λ).obj (moduleUnit U Λ)) (r + 1) :=
      ((extFunctorObj A (r + 1)).mapIso
        ((moduleLowerShriek j Λ).mapIso (moduleUnitInverseImageIso j n))).addCommGroupIsoToAddEquiv
    exact E₁.symm.injective.subsingleton
end CompactConstantVanishing

/-- An additive functor kills every finite module over a field once it kills
its original lifted regular module. The finite basis is internal and no
scalar action is introduced on the target abelian groups. -/
private theorem finiteField_additiveFunctor_subsingleton
    (R : Type) [Field R] (H : ModuleCat.{v} R ⥤ AddCommGrpCat.{w}) [H.Additive]
    [Subsingleton (H.obj (ModuleCat.liftedUnit.{0, v} R))]
    (M : ModuleCat.{v} R) [Finite M] : Subsingleton (H.obj M) := by
  let : Module.Finite R M := Module.Finite.of_finite
  let : Module.Free R M := Module.Free.of_divisionRing R M
  let d := Module.finrank R M
  let b : Module.Basis (Fin d) R M := Module.finBasis R M
  let P := fun _ : Fin d => ModuleCat.liftedUnit.{0, v} R
  let e : M ≃ₗ[R] (Fin d → ULift.{v} R) :=
    b.equivFun.trans (LinearEquiv.piCongrRight fun _ => ULift.moduleEquiv.symm)
  let a : M ≅ ⨁ P := e.toModuleIso ≪≫ (ModuleCat.biproductIsoPi P).symm
  have hp (i : Fin d) : H.map (biproduct.π P i) = 0 := by
    ext x
    exact Subsingleton.elim _ _
  have hid : (𝟙 (H.obj (⨁ P))) = 0 := by
    have h := congrArg H.map (IsBilimit.total (biproduct.isBilimit P))
    rw [H.map_sum, H.map_id] at h
    simp only [H.map_comp, hp, zero_comp, Finset.sum_const_zero] at h
    exact h.symm
  let : Subsingleton (H.obj (⨁ P)) := by
    apply subsingleton_of_forall_eq 0
    intro x
    exact congrArg (fun f : H.obj (⨁ P) ⟶ H.obj (⨁ P) => f x) hid
  exact (H.mapIso a).addCommGroupIsoToAddEquiv.injective.subsingleton

section CompactPrimeConstant

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]

include hX D hfin hclosed hD in
/-- Prime-annihilated finite constant coefficients have zero original compact
cohomology above degree two. The auxiliary prime-field action is only on the
SAME finite module value; no scalar extension or action on compact cohomology
is introduced. -/
private theorem constantModule_compact_H_high_subsingleton_of_prime_nsmul
    (R : Type r) [CommRing R] [Finite R]
    (p : ℕ) [Fact p.Prime] (hunit : IsUnit (p : k)) (q : ℕ) (hq : 2 < q)
    (M : ModuleCat.{u + 1} R) [Module.Finite R M] (hM : ∀ m : M, p • m = 0) :
    Subsingleton (CompactSupport.H.{wA} j
      ((Constructible.Modules.moduleUnderlying R U).obj
        ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)) q) := by
  let : Finite M := Module.finite_of_finite R
  let mFp : Module (ZMod p) M := AddCommGroup.zmodModule hM
  let : Module (ZMod p) M := mFp
  let V : ModuleCat.{u + 1} (ZMod p) := ModuleCat.of (ZMod p) M
  let H : ModuleCat.{u + 1} (ZMod p) ⥤ AddCommGrpCat.{wA} :=
    constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ZMod p)) ⋙
      Constructible.Modules.moduleUnderlying (ZMod p) U ⋙ CompactSupport.functor j q
  let Λ := ULift.{u + 1} (ZMod p)
  let : HasExt.{u + 2} (ModuleSheaf X.left Λ) :=
    SheafOfModules.hasExt (constantRing X.left Λ)
  let C := moduleUnit U Λ
  let Q := SheafOfModules.toSheaf (constantRing U Λ)
  let : Subsingleton (Ext.{u + 2} (moduleUnit X.left Λ)
      ((moduleLowerShriek j Λ).obj C) q) :=
    moduleUnitCompactExt_high_subsingleton X hX D hfin hclosed j hD p
      (Fact.out : p.Prime).pos hunit q hq
  let E₀ : Ext.{u + 2} (moduleUnit X.left Λ) ((moduleLowerShriek j Λ).obj C) q ≃+
      CompactSupport.H.{wA} j (Q.obj C) q :=
    moduleLowerShriekCohomologyAddEquiv j Λ C q
  let : Subsingleton (CompactSupport.H.{wA} j (Q.obj C) q) :=
    E₀.symm.injective.subsingleton
  let a : (Constructible.Modules.moduleUnderlying (ZMod p) U).obj
      ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ZMod p))).obj
        (ModuleCat.liftedUnit.{0, u + 1} (ZMod p))) ≅ Q.obj C :=
    (Constructible.Modules.moduleConstantUnderlyingIso (ZMod p) U).app
        (ModuleCat.liftedUnit.{0, u + 1} (ZMod p)) ≪≫ moduleUnitUnderlyingIso U Λ
  let E₁ : H.obj (ModuleCat.liftedUnit.{0, u + 1} (ZMod p)) ≃+
      CompactSupport.H.{wA} j (Q.obj C) q :=
    ((CompactSupport.functor j q).mapIso a).addCommGroupIsoToAddEquiv
  let : Subsingleton (H.obj (ModuleCat.liftedUnit.{0, u + 1} (ZMod p))) :=
    E₁.injective.subsingleton
  let : Subsingleton (H.obj V) := finiteField_additiveFunctor_subsingleton (ZMod p) H V
  let b := (Constructible.Modules.moduleConstantUnderlyingIso R U).app M ≪≫
    ((Constructible.Modules.moduleConstantUnderlyingIso (ZMod p) U).app V).symm
  let E₂ : CompactSupport.H.{wA} j
      ((Constructible.Modules.moduleUnderlying R U).obj
        ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)) q ≃+
          H.obj V := ((CompactSupport.functor j q).mapIso b).addCommGroupIsoToAddEquiv
  exact E₂.injective.subsingleton

end CompactPrimeConstant

section CompactPGroup

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]

include hX D hfin hclosed hD in
/-- P-group filtration of the SAME actual trivialization gives compact high
vanishing. Exactness is the original module forgetting followed by original
extension by zero; no duality or coefficient extension occurs. -/
private theorem moduleSheaf_compact_H_high_subsingleton_of_pGroup_trivialization
    [ConnectedSpace U] (R : Type r) [CommRing R] [Finite R]
    (p : ℕ) [Fact p.Prime] (hunit : IsUnit (p : k))
    (Y : Scheme.FiniteEtale U) [PreGaloisCategory.IsGalois Y]
    [Surjective Y.obj.hom] [ConnectedSpace Y.obj.left]
    [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]
    (hY : IsPGroup p (Aut Y)) (q : ℕ) (hq : 2 < q)
    (F : Constructible.Modules.ModuleSheaf R U) (M : ModuleCat.{u + 1} R)
    [Module.Finite R M] (hM : ∀ m : M, p • m = 0)
    (t : (Constructible.Modules.moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    Subsingleton (CompactSupport.H.{wA} j
      ((Constructible.Modules.moduleUnderlying R U).obj F) q) := by
  apply Constructible.Modules.property_of_pGroup_trivialization Y p hY
    (fun A => Subsingleton (CompactSupport.H.{wA} j
      ((Constructible.Modules.moduleUnderlying R U).obj A) q)) ?_ ?_ ?_ F M hM t
  · intro N _ hN
    exact constantModule_compact_H_high_subsingleton_of_prime_nsmul
      X hX D hfin hclosed j hD R p hunit q hq N hN
  · intro A B e hA
    let := hA
    let E : CompactSupport.H.{wA} j
        ((Constructible.Modules.moduleUnderlying R U).obj A) q ≃+
      CompactSupport.H.{wA} j ((Constructible.Modules.moduleUnderlying R U).obj B) q :=
      ((CompactSupport.functor j q).mapIso
        ((Constructible.Modules.moduleUnderlying R U).mapIso e)).addCommGroupIsoToAddEquiv
    exact E.symm.injective.subsingleton
  · intro S hS h₁ h₃
    let Q := Constructible.Modules.moduleUnderlying R U
    let L := etaleLowerShriek j
    let : Subsingleton (Sheaf.H.{wA} (((S.map Q).map L).X₁) q) := h₁
    let : Subsingleton (Sheaf.H.{wA} (((S.map Q).map L).X₃) q) := h₃
    exact Sheaf.H.subsingleton_middle_of_shortExact
      ((hS.map_of_exact Q).map_of_exact L) q

end CompactPGroup

/-- A finite closed subset of a Jacobson space consists of closed points.
This supplies the literal preimage boundary returned by native cover completion. -/
private theorem finite_closed_mem_isClosed_singleton
    {T : Type u} [TopologicalSpace T] [JacobsonSpace T]
    (E : Set T) (hfin : E.Finite) (hE : IsClosed E) :
    ∀ x ∈ E, IsClosed ({x} : Set T) := by
  let S := E ∩ closedPoints T
  have hSfin : S.Finite := hfin.subset Set.inter_subset_left
  let : Finite S := hSfin.to_subtype
  have hS : IsClosed S := by
    have heq : (⋃ y : S, ({y.val} : Set T)) = S := by ext z; simp
    rw [← heq]
    exact isClosed_iUnion_of_finite (fun y : S => y.property.2)
  intro x hx
  by_contra hn
  have hne : (E ∩ Sᶜ).Nonempty := ⟨x, hx, fun hs => hn hs.2⟩
  have hlc : IsLocallyClosed (E ∩ Sᶜ) :=
    hE.isLocallyClosed.inter hS.isOpen_compl.isLocallyClosed
  obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints hne hlc
  exact hy.2 ⟨hy.1, hc⟩

section CompactCoprime

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (R : Type r) [CommRing R]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X)]

/-- Coprime annihilator descent for ORIGINAL compact cohomology. The actual
module image-unit retraction is mapped by original forgetting, j! and H;
its source is identified by the original finite/open Cartesian comparison. -/
private theorem moduleSheaf_compact_H_subsingleton_of_finiteEtale_coprime
    (Y : Scheme.FiniteEtale U) {Ybar : Scheme.{u}}
    (fbar : Ybar ⟶ X) [IsFinite fbar]
    (jY : Y.obj.left ⟶ Ybar) [IsOpenImmersion jY]
    (hsq : IsPullback jY Y.obj.hom fbar j)
    [HasExt.{wY} (AbelianSheaf.{u, u + 1} Ybar)]
    (d : ℕ) (hd : ∀ x : U, Y.obj.hom.finrank x = d)
    (F : Constructible.Modules.ModuleSheaf R U)
    (p : ℕ) (hcop : d.Coprime p) (hp : p • 𝟙 F = 0) (q : ℕ)
    (hzero : Subsingleton (CompactSupport.H.{wY} jY
      ((Constructible.Modules.moduleUnderlying R Y.obj.left).obj
        ((Constructible.Modules.moduleInverseImage R Y.obj.hom).obj F)) q)) :
    Subsingleton (CompactSupport.H.{wA} j
      ((Constructible.Modules.moduleUnderlying R U).obj F) q) := by
  let M := (Constructible.Modules.moduleInverseImage R Y.obj.hom).obj F
  let H : Constructible.Modules.ModuleSheaf R U ⥤ AddCommGrpCat.{wA} :=
    Constructible.Modules.moduleUnderlying R U ⋙ CompactSupport.functor j q
  let E₁ : H.obj ((Constructible.Modules.moduleDirectImage R Y.obj.hom).obj M) ≃+
      CompactSupport.H.{wA} j ((directImage Y.obj.hom).obj
        ((Constructible.Modules.moduleUnderlying R Y.obj.left).obj M)) q :=
    ((CompactSupport.functor j q).mapIso
      ((Constructible.Modules.moduleDirectImageUnderlyingIso R Y.obj.hom).app M))
        |>.addCommGroupIsoToAddEquiv
  let E₂ := CompactSupport.finiteDirectImageAddEquiv fbar Y.obj.hom j jY hsq
    ((Constructible.Modules.moduleUnderlying R Y.obj.left).obj M) q
  let : Subsingleton (H.obj ((Constructible.Modules.moduleDirectImage R Y.obj.hom).obj M)) :=
    (E₁.trans E₂).injective.subsingleton
  obtain ⟨tr, htr⟩ := exists_finiteEtale_moduleSheafRetraction_map R Y d hd F p hcop hp H
  have hsurj : Function.Surjective tr := by
    intro x
    refine ⟨H.map ((Constructible.Modules.moduleImageAdjunction R Y.obj.hom).unit.app F) x, ?_⟩
    exact congrArg (fun a => a x) htr
  exact hsurj.subsingleton

end CompactCoprime

section CompactSylow

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]

include hX D hfin hclosed hD in
private theorem moduleSheaf_compact_H_high_subsingleton_of_galois_prime_trivialization
    [ConnectedSpace U] (R : Type r) [CommRing R] [Finite R]
    (p : ℕ) [Fact p.Prime] (hunit : IsUnit (p : k))
    (Y : Scheme.FiniteEtale U) [PreGaloisCategory.IsGalois Y]
    [Surjective Y.obj.hom] [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]
    (q : ℕ) (hq : 2 < q)
    (F : Constructible.Modules.ModuleSheaf R U) (M : ModuleCat.{u + 1} R)
    [Module.Finite R M] (hM : ∀ m : M, p • m = 0)
    (t : (Constructible.Modules.moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    Subsingleton (CompactSupport.H.{wA} j
      ((Constructible.Modules.moduleUnderlying R U).obj F) q) := by
  let P : Sylow p (Aut Y) := Classical.choice inferInstance
  let Z₀ := Scheme.FiniteEtale.galoisSubgroupQuotient Y P.toSubgroup
  let V := Scheme.FiniteEtale.galoisSubgroupRelative Y P.toSubgroup
  let : Surjective Z₀.obj.hom := inferInstance
  let : ConnectedSpace Z₀.obj.left := inferInstance
  have hDc : IsClosed D := by
    let : Finite D := hfin.to_subtype
    have heq : (⋃ x : D, ({x.val} : Set X.left)) = D := by ext z; simp
    rw [← heq]
    exact isClosed_iUnion_of_finite (fun x : D => hclosed x.val x.property)
  obtain ⟨Z, fbar, jZ, hZ, hfbar, _, hjZ, hsq, hEfin, hEc, hE⟩ :=
    Curve.exists_finiteEtaleCompletion_with_boundary X hX j Z₀ D hfin hDc hD
  let : IsFinite fbar.left := hfbar
  let : IsOpenImmersion jZ := hjZ
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Z.left) := hasExtStandard Z.left
  let := Curve.curveProperties_locallyOfFiniteType hZ
  let : JacobsonSpace Z.left := LocallyOfFiniteType.jacobsonSpace Z.hom
  let E := fbar.left ⁻¹' D
  have hEclosed : ∀ z ∈ E, IsClosed ({z} : Set Z.left) :=
    finite_closed_mem_isClosed_singleton E hEfin hEc
  let : PreGaloisCategory.IsGalois V :=
    Scheme.FiniteEtale.galoisSubgroupRelative_isGalois Y P.toSubgroup
  let : Surjective V.obj.hom :=
    Scheme.FiniteEtale.galoisSubgroupRelative_surjective Y P.toSubgroup
  let : CompactSpace V.obj.left := inferInstanceAs (CompactSpace Y.obj.left)
  let : QuasiSeparatedSpace V.obj.left := inferInstanceAs (QuasiSeparatedSpace Y.obj.left)
  let FZ := (Constructible.Modules.moduleInverseImage R Z₀.obj.hom).obj F
  have htriangle : V.obj.hom ≫ Z₀.obj.hom = Y.obj.hom :=
    Scheme.FiniteEtale.galoisSubgroupQuotientπ_structure Y P.toSubgroup
  let t' : (Constructible.Modules.moduleInverseImage R V.obj.hom).obj FZ ≅
      (constantSheaf V.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M :=
    ((Constructible.Modules.moduleInverseImageComp R Z₀.obj.hom V.obj.hom).app F).symm ≪≫
      eqToIso (congrArg (fun f =>
        (Constructible.Modules.moduleInverseImage R f).obj F) htriangle) ≪≫ t
  have hzero : Subsingleton (CompactSupport.H.{u + 2} jZ
      ((Constructible.Modules.moduleUnderlying R Z₀.obj.left).obj FZ) q) :=
    moduleSheaf_compact_H_high_subsingleton_of_pGroup_trivialization
      Z hZ E hEfin hEclosed jZ hE R p hunit V
      (Scheme.FiniteEtale.galoisSylowRelative_isPGroup Y P) q hq FZ M hM t'
  exact moduleSheaf_compact_H_subsingleton_of_finiteEtale_coprime j R Z₀
    fbar.left jZ hsq P.toSubgroup.index
    (Scheme.FiniteEtale.galoisSubgroupQuotient_finrank Y P.toSubgroup) F p
    (Scheme.FiniteEtale.galoisSylow_index_coprime Y P)
    (moduleSheaf_nsmul_id_eq_zero_of_trivialization
      R Y.obj.hom F M p hM t) q hzero

end CompactSylow

private theorem compact_nsmul_id_naturality {C : Type*} [Category* C] [Preadditive C]
    (p : ℕ) {A B : C} (f : A ⟶ B) :
    f ≫ (p • 𝟙 B) = (p • 𝟙 A) ≫ f := by
  simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id, Category.id_comp]

section CompactGlobal
open Constructible.Modules
variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]

omit hX D hfin hclosed j hD [IsAlgClosed k]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)] in
private theorem compact_constant_value_nsmul_eq_zero_of_trivialization
    (R : Type r) [CommRing R] [Finite R]
    {S : Scheme.{u}} (f : S ⟶ U) [Etale f]
    [ConnectedSpace S] [CompactSpace S] [QuasiSeparatedSpace S]
    (F : ModuleSheaf R U) (M : ModuleCat.{u + 1} R) [Module.Finite R M]
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
    exact (compact_nsmul_id_naturality p t.hom).trans
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

include hX D hfin hclosed hD in
private theorem compact_moduleSheaf_H_high_subsingleton_of_prime_nsmul
    [ConnectedSpace U] (R : Type r) [CommRing R] [Finite R]
    [(forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).Full]
    (p : ℕ) [Fact p.Prime] (hunit : IsUnit (p : k)) (q : ℕ) (hq : 2 < q)
    (F : ModuleSheaf R U) (hF : IsFiniteTypeLocallyConstant F)
    (hp : p • 𝟙 F = 0) :
    Subsingleton (CompactSupport.H.{wA} j ((moduleUnderlying R U).obj F) q) := by
  let : IsNoetherian X.left := Curve.curveProperties_isNoetherian hX
  let : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  let : TopologicalSpace.NoetherianSpace U :=
    j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  let : CompactSpace U := TopologicalSpace.NoetherianSpace.compactSpace U
  let : IsNoetherian U := ⟨⟩
  let T := Classical.choice (nonempty_galoisCoverConstantTrivialization F hF)
  let Y := T.cover
  let : PreGaloisCategory.IsGalois Y := T.galois_cover
  let : ConnectedSpace Y.obj.left := T.connected_cover
  let : Surjective Y.obj.hom := T.surjective_cover
  let : CompactSpace Y.obj.left := QuasiCompact.compactSpace_of_compactSpace Y.obj.hom
  let : QuasiSeparatedSpace Y.obj.left := quasiSeparatedSpace_of_quasiSeparated Y.obj.hom
  let : Module.Finite R T.value := T.finite_value
  have hM : ∀ m : T.value, p • m = 0 :=
    compact_constant_value_nsmul_eq_zero_of_trivialization R Y.obj.hom F T.value p hp T.iso
  exact moduleSheaf_compact_H_high_subsingleton_of_galois_prime_trivialization
    X hX D hfin hclosed j hD R p hunit Y q hq F T.value hM T.iso

include hX D hfin hclosed hD in
/-- Positive invertible annihilators give genuine compact high vanishing on
the original open curve, through actual coefficient kernels and cokernels. -/
private theorem compact_moduleSheaf_H_high_subsingleton_of_pos_nsmul
    [ConnectedSpace U] (R : Type r) [CommRing R] [Finite R]
    [(forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).Full]
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (q : ℕ) (hq : 2 < q)
    (F : ModuleSheaf R U) (hF : IsFiniteTypeLocallyConstant F)
    (hkill : n • 𝟙 F = 0) :
    Subsingleton (CompactSupport.H.{wA} j ((moduleUnderlying R U).obj F) q) := by
  let : IsNoetherianRing R := inferInstance
  induction n using Nat.strong_induction_on generalizing F with
  | h n ih =>
    by_cases h1 : n = 1
    · subst n
      let H := moduleUnderlying R U ⋙ CompactSupport.functor j q
      have hzero : 𝟙 F = 0 := by simpa only [one_nsmul] using hkill
      have hid : 𝟙 (H.obj F) = 0 := (H.map_id F).symm.trans
        ((congrArg H.map hzero).trans (H.map_zero F F))
      apply subsingleton_of_forall_eq 0
      intro x
      exact congrArg (fun f : H.obj F ⟶ H.obj F => f x) hid
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
      have hleft : Subsingleton (CompactSupport.H.{wA} j
          ((moduleUnderlying R U).obj (kernel a)) q) :=
        ih m hlt hm hum (kernel a) hK hmK
      have hright : Subsingleton (CompactSupport.H.{wA} j
          ((moduleUnderlying R U).obj (cokernel i)) q) :=
        compact_moduleSheaf_H_high_subsingleton_of_prime_nsmul
          X hX D hfin hclosed j hD R p hup q hq (cokernel i) hQ hpQ
      let : Subsingleton (Sheaf.H.{wA}
          (((S.map (moduleUnderlying R U)).map (etaleLowerShriek j)).X₁) q) := by
        change Subsingleton (CompactSupport.H.{wA} j
          ((moduleUnderlying R U).obj (kernel a)) q)
        exact hleft
      let : Subsingleton (Sheaf.H.{wA}
          (((S.map (moduleUnderlying R U)).map (etaleLowerShriek j)).X₃) q) := by
        change Subsingleton (CompactSupport.H.{wA} j
          ((moduleUnderlying R U).obj (cokernel i)) q)
        exact hright
      exact Sheaf.H.subsingleton_middle_of_shortExact
        ((hS.map_of_exact (moduleUnderlying R U)).map_of_exact (etaleLowerShriek j)) q

end CompactGlobal

section CompactNative
variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)

omit [IsAlgClosed k] [IsOpenImmersion j] in
include hX D hfin hclosed hD in
private theorem finite_complement_open_nonempty : Nonempty U := by
  classical
  by_contra hempty
  let : IsEmpty U := not_nonempty_iff.mp hempty
  have hDu : D = Set.univ := by
    apply compl_injective
    rw [Set.compl_univ, ← hD]
    exact Set.range_eq_empty j
  let : Finite X.left := Set.finite_univ_iff.mp (hDu ▸ hfin)
  let : T1Space X.left := ⟨fun x => hclosed x (by rw [hDu]; trivial)⟩
  have hdim := topologicalKrullDim_zero_of_discreteTopology X.left
  rw [Curve.curveProperties_dimension smoothFieldDimension hX] at hdim
  exact (by norm_num : ¬ (1 : WithBot ℕ∞) ≤ 0) hdim

include hX D hfin hclosed hD in
/-- Finite locally constant coefficients on the given finite-complement open
have no original compact unit-Ext above degree two. The module and abelian
Ext worlds remain independent. Composite positive levels and level one are
included. No local constancy of the extension by zero is assumed. -/
theorem moduleCompactExt_high_subsingleton_of_finiteLocallyConstant
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    [HasExt.{wX} (Coefficients.ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]
    (F : Coefficients.ModuleSheaf U (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((Coefficients.moduleSheafEquivalence U (ULift.{u + 1} (ZMod n))).inverse.obj F))
    (q : ℕ) (hq : 2 < q) :
    Subsingleton (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj F) q) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : Nonempty U := finite_complement_open_nonempty X hX D hfin hclosed j hD
  let : IsIntegral X.left :=
    Curve.curveProperties_isIntegral smoothFieldNormality normalComponentsOpen hX
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : ConnectedSpace U := inferInstance
  let Λ := ULift.{u + 1} (ZMod n)
  let M := (Coefficients.moduleSheafEquivalence U Λ).inverse.obj F
  let : (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).Full :=
    ModuleCat.uLiftZMod_forget₂_full n
  have hkill : n • 𝟙 M = 0 := by
    apply ObjectProperty.hom_ext
    ext V m
    change n • m = 0
    rw [← Nat.cast_smul_eq_nsmul (R := Λ)]
    have hnzero : (n : Λ) = 0 := by
      apply ULift.ext
      change (n : ZMod n) = 0
      exact ZMod.natCast_self n
    rw [hnzero, zero_smul]
  let : Subsingleton (CompactSupport.H.{wA} j
      ((Constructible.Modules.moduleUnderlying Λ U).obj M) q) :=
    compact_moduleSheaf_H_high_subsingleton_of_pos_nsmul X hX D hfin hclosed j hD
      Λ n hn hunit q hq M hF hkill
  let Q := SheafOfModules.toSheaf (constantRing U Λ)
  let E₀ : Ext.{wX} (moduleUnit X.left Λ) ((moduleLowerShriek j Λ).obj F) q ≃+
      CompactSupport.H.{wA} j (Q.obj F) q :=
    moduleLowerShriekCohomologyAddEquiv j Λ F q
  let E₁ : CompactSupport.H.{wA} j (Q.obj F) q ≃+
      CompactSupport.H.{wA} j ((Constructible.Modules.moduleUnderlying Λ U).obj M) q :=
    ((CompactSupport.functor j q).mapIso
      ((Coefficients.moduleSheafInverseUnderlyingIso U Λ).app F).symm)
        |>.addCommGroupIsoToAddEquiv
  exact (E₀.trans E₁).injective.subsingleton

end CompactNative

private theorem originalAddEquiv_toZModLinearEquiv_apply
    (n : ℕ) {M : Type uC} {N : Type vC} [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod n) M] [Module (ZMod n) N] (e : M ≃+ N) (x : M) :
    (AddEquiv.toZModLinearEquiv n e) x = e x := rfl

section ProperFinitePerfectness
open GroupCohomology.Kummer.CoefficientBaseChange
universe wSY wAY
variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{wP} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]

/-- The proved whole finite-pushforward pairing law transports the SAME
degree-two proper pairing. Both maps are the already defined original EX/EY. -/
private theorem proper_finiteLowerShriek_two_isPerfPair
    (Y : FScheme k) (hY : Curve.Properties Y) (f : Y ⟶ X)
    [IsFinite f.left] [IsDominant f.left] [Etale f.left]
    (d : ℕ) (hd : ∀ x : X.left, f.left.finrank x = d)
    [HasExt.{wY} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wSY} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wAY} (AbelianSheaf.{u, u + 1} Y.left)]
    (P : ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))
    (hP : (moduleDualityMap.{u, wSY, wY, wAY} Y hY ∅ Set.finite_empty (by simp)
      (𝟙 Y.left) (by simp) n hn hunit (levelInvertible f.left n hinv)
        P 2 (by decide)).IsPerfPair) :
    (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv
        ((moduleLowerShriek f.left (ULift.{u + 1} (ZMod n))).obj P) 2 (by decide)).IsPerfPair := by
  let L := AddEquiv.toZModLinearEquiv n
    (moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY} f.left n d hd P 2)
  let R := AddEquiv.toZModLinearEquiv n
    (moduleFiniteLowerShriekRootsExtAddEquiv.{u, wP, wSY} f.left n hn hinv P 0)
  let B := moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
    (𝟙 X.left) (by simp) n hn hunit hinv
      ((moduleLowerShriek f.left (ULift.{u + 1} (ZMod n))).obj P) 2 (by decide)
  let C := moduleDualityMap.{u, wSY, wY, wAY} Y hY ∅ Set.finite_empty (by simp)
    (𝟙 Y.left) (by simp) n hn hunit (levelInvertible f.left n hinv) P 2 (by decide)
  have hs : C.compl₁₂ L R = B := by
    ext c e
    simp only [LinearMap.compl₁₂_apply, L, R, LinearEquiv.coe_coe,
      originalAddEquiv_toZModLinearEquiv_apply]
    exact (moduleTracePairingLinearMap_finiteLowerShriek_two_zero.{
      u, wX, wY, wA, wAY, wP, wSY} X Y hX hY f n d hd hn hunit hinv P c e).symm
  have hC : C.IsPerfPair := hP
  let := hC
  change B.IsPerfPair
  rw [← hs]
  exact LinearMap.IsPerfPair.compl₁₂ C L R

omit hX hn hunit hinv [IsAlgClosed k]
  [HasExt.{wP} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)] in
private theorem finiteLowerShriek_isFiniteTypeLocallyConstant
    {V : Scheme.{u}} (f : V ⟶ X.left) [IsFinite f] [Etale f]
    (d : ℕ) (hd : ∀ x : X.left, f.finrank x = d)
    (P : ModuleSheaf V (ULift.{u + 1} (ZMod n)))
    (hP : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence V (ULift.{u + 1} (ZMod n))).inverse.obj P)) :
    Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X.left (ULift.{u + 1} (ZMod n))).inverse.obj
        ((moduleLowerShriek f (ULift.{u + 1} (ZMod n))).obj P)) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let E := (moduleSheafEquivalence X.left Λ).inverse
  let e := E.mapIso ((moduleFiniteEtaleLowerShriekDirectImageIso f n d hd).app P) ≪≫
    (moduleDirectImageComparison f Λ).app P
  exact (Constructible.Modules.isFiniteTypeLocallyConstant_iff_of_iso e).mpr
    (Constructible.Modules.isFiniteTypeLocallyConstant_finiteEtaleDirectImage f hP)

include hX hn hunit in
private theorem proper_galois_freeLowerShriek_two_isPerfPair
    (Y : Scheme.FiniteEtale X.left) [ConnectedSpace Y.obj.left] [Surjective Y.obj.hom]
    (m : ℕ) :
    (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv
        ((moduleLowerShriek Y.obj.hom (ULift.{u + 1} (ZMod n))).obj
          (⨁ fun _ : Fin m => moduleUnit Y.obj.left (ULift.{u + 1} (ZMod n))))
        2 (by decide)).IsPerfPair := by
  let : ConnectedSpace X.left := Curve.curveProperties_connectedSpace hX
  let Z : FScheme k := Over.mk (Y.obj.hom ≫ X.hom)
  let hZ : Curve.Properties Z := Curves.curveProperties_of_connected_finiteEtale X hX Y
  let f : Z ⟶ X := Over.homMk Y.obj.hom rfl
  let : IsFinite f.left := inferInstanceAs (IsFinite Y.obj.hom)
  let : Etale f.left := inferInstanceAs (Etale Y.obj.hom)
  let : IsDominant f.left := ⟨Y.obj.hom.surjective.denseRange⟩
  let x : X.left := Classical.ofNonempty
  let d := Y.obj.hom.finrank x
  have hd : ∀ z : X.left, f.left.finrank z = d := fun z =>
    Y.obj.hom.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace z x
  let : HasExt.{u + 2} (ModuleSheaf Z.left (ULift.{u + 1} (ZMod n))) :=
    SheafOfModules.hasExt (constantRing Z.left (ULift.{u + 1} (ZMod n)))
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Z.left) := hasExtStandard Z.left
  exact proper_finiteLowerShriek_two_isPerfPair.{u, wX, wA, wP, u + 2, u + 2, u + 2}
    X hX n hn hunit hinv Z hZ f d hd
    (⨁ fun _ : Fin m => moduleUnit Z.left (ULift.{u + 1} (ZMod n)))
    (moduleDualityMap_unit_biproduct_two_isPerfPair.{u, u + 2, u + 2, u + 2}
      Z hZ ∅ Set.finite_empty (by simp)
      (𝟙 Z.left) (by simp) n hn hunit (levelInvertible f.left n hinv) m)

/-- The native degree-zero transpose is the original degree-two pairing's
right adjoint, fixed at a variable coefficient before any kernel presentation. -/
private theorem proper_zero_transpose_eq_flip
    (F : ModuleSheaf X.left (ULift.{u + 1} (ZMod n))) :
    moduleDualityTransposeMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv F 0 (by decide) =
    (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv F 2 (by decide)).flip := rfl

private theorem proper_zero_transpose_bijective_of_two_isPerfPair
    (F : ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))
    (hF : (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv F 2 (by decide)).IsPerfPair) :
    Function.Bijective (moduleDualityTransposeMap.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
      n hn hunit hinv F 0 (by decide)) := by
  rw [proper_zero_transpose_eq_flip.{u, wX, wA, wP} X hX n hn hunit hinv F]
  exact hF.bijective_right

private theorem proper_one_transpose_eq_flip
    (F : ModuleSheaf X.left (ULift.{u + 1} (ZMod n))) :
    moduleDualityTransposeMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv F 1 (by decide) =
    (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv F 1 (by decide)).flip := rfl

private theorem proper_one_isPerfPair_of_transpose_injective
    (F : ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))
    [Finite (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X.left) (ULift.{u + 1} (ZMod n))).obj F) 1)]
    (hi : Function.Injective (moduleDualityTransposeMap.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
      n hn hunit hinv F 1 (by decide)))
    (hc : Nat.card (Ext.{wP} F (moduleRootsOfUnity X.left n) 1) =
      Nat.card (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
        ((moduleLowerShriek (𝟙 X.left) (ULift.{u + 1} (ZMod n))).obj F) 1)) :
    (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv F 1 (by decide)).IsPerfPair := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [proper_one_transpose_eq_flip.{u, wX, wA, wP} X hX n hn hunit hinv F] at hi
  let B := moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
    (𝟙 X.left) (by simp) n hn hunit hinv F 1 (by decide)
  exact (ZMod.isPerfPair_of_injective_of_natCard_eq n B.flip hi hc).flip

include hX hn hunit in
private theorem proper_dualityTranspose_zero_injective
    (F : ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X.left (ULift.{u + 1} (ZMod n))).inverse.obj F)) :
    Function.Injective (moduleDualityTransposeMap.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
      n hn hunit hinv F 0 (by decide)) := by
  let : ConnectedSpace X.left := Curve.curveProperties_connectedSpace hX
  obtain ⟨Y, _, hconn, hsurj, m, a, ha⟩ :=
    exists_galois_unit_biproduct_lowerShriek_epi n hn F hF
  let : ConnectedSpace Y.obj.left := hconn
  let : Surjective Y.obj.hom := hsurj
  let S := ShortComplex.kernelSequence a
  have hS : S.ShortExact := { exact := ShortComplex.kernelSequence_exact a, epi_g := ha }
  have hB : (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv
      ((moduleLowerShriek Y.obj.hom (ULift.{u + 1} (ZMod n))).obj
        (⨁ fun _ : Fin m => moduleUnit Y.obj.left (ULift.{u + 1} (ZMod n))))
      2 (by decide)).IsPerfPair :=
    proper_galois_freeLowerShriek_two_isPerfPair.{u, wX, wA, wP} X hX n hn hunit hinv Y m
  apply moduleDualityTransposeMap_zero_injective_of_shortExact.{u, wP, wX, wA}
    X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp) n hn hunit hinv hS
  dsimp only [S, ShortComplex.kernelSequence]
  exact (proper_zero_transpose_bijective_of_two_isPerfPair.{u, wX, wA, wP}
    X hX n hn hunit hinv _ hB).injective

include hX hn hunit in
/-- Proper source degree zero is bijective for every original finite local
system, by the actual free epimorphism and the already compiled two-pass
criteria. No open-curve chase is used. -/
theorem moduleDualityTransposeMap_proper_zero_bijective
    (F : ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X.left (ULift.{u + 1} (ZMod n))).inverse.obj F)) :
    Function.Bijective (moduleDualityTransposeMap.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
      n hn hunit hinv F 0 (by decide)) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : ConnectedSpace X.left := Curve.curveProperties_connectedSpace hX
  refine ⟨proper_dualityTranspose_zero_injective.{u, wX, wA, wP}
    X hX n hn hunit hinv F hF, ?_⟩
  obtain ⟨Y, _, hconn, hsurj, m, a, ha⟩ :=
    exists_galois_unit_biproduct_lowerShriek_epi n hn F hF
  let : ConnectedSpace Y.obj.left := hconn
  let : Surjective Y.obj.hom := hsurj
  let Λ := ULift.{u + 1} (ZMod n)
  let P : ModuleSheaf Y.obj.left Λ := ⨁ fun _ : Fin m => moduleUnit Y.obj.left Λ
  let x : X.left := Classical.ofNonempty
  let d := Y.obj.hom.finrank x
  have hd : ∀ z : X.left, Y.obj.hom.finrank z = d := fun z =>
    Y.obj.hom.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace z x
  have hBLC := finiteLowerShriek_isFiniteTypeLocallyConstant X n Y.obj.hom d hd P
    (moduleUnitBiproduct_isFiniteTypeLocallyConstant Y.obj.left Λ m)
  have hKLC := moduleKernel_isFiniteTypeLocallyConstant X.left Λ a hBLC hF
  let S := ShortComplex.kernelSequence a
  have hS : S.ShortExact := { exact := ShortComplex.kernelSequence_exact a, epi_g := ha }
  let : Subsingleton (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X.left) (ULift.{u + 1} (ZMod n))).obj S.X₁) 3) := by
    change Subsingleton (Ext.{wX} (moduleUnit X.left Λ)
      ((moduleLowerShriek (𝟙 X.left) Λ).obj (kernel a)) 3)
    exact moduleUnitCompactIdExt_subsingleton_of_finiteLocallyConstant.{u, wX, wA}
      X hX n hn hunit (kernel a) hKLC 3 (by decide)
  have hB : (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv
      ((moduleLowerShriek Y.obj.hom (ULift.{u + 1} (ZMod n))).obj
        (⨁ fun _ : Fin m => moduleUnit Y.obj.left (ULift.{u + 1} (ZMod n))))
      2 (by decide)).IsPerfPair :=
    proper_galois_freeLowerShriek_two_isPerfPair.{u, wX, wA, wP} X hX n hn hunit hinv Y m
  have hK : Function.Injective (moduleDualityTransposeMap.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
      n hn hunit hinv (kernel a) 0 (by decide)) :=
    proper_dualityTranspose_zero_injective.{u, wX, wA, wP}
      X hX n hn hunit hinv (kernel a) hKLC
  apply moduleDualityTransposeMap_zero_surjective_of_shortExact.{u, wP, wX, wA}
    X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp) n hn hunit hinv hS
  · dsimp only [S, ShortComplex.kernelSequence]
    exact (proper_zero_transpose_bijective_of_two_isPerfPair.{u, wX, wA, wP}
      X hX n hn hunit hinv _ hB).surjective
  · dsimp only [S, ShortComplex.kernelSequence]
    exact hK

include hX hn hunit in
/-- The original constant degree-one pairing on the proper curve is perfect.
Intrinsic killing supplies the actual normalized counit; proper source-zero
duality and the original unsigned boundary chase give injectivity. The proved
finite equal-cardinality theorem then gives both original adjoints. -/
theorem moduleDualityMap_unit_proper_one_isPerfPair :
    (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv
      (moduleUnit X.left (ULift.{u + 1} (ZMod n))) 1 (by decide)).IsPerfPair := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : ConnectedSpace X.left := Curve.curveProperties_connectedSpace hX
  let Λ := ULift.{u + 1} (ZMod n)
  let Ψ := moduleDualityTransposeMap.{u, wP, wX, wA}
    X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
    n hn hunit hinv (moduleUnit X.left Λ) 1 (by decide)
  have hz : ∀ e, Ψ e = 0 → e = 0 := by
    intro e he
    obtain ⟨Y, _, _, _, hg, hkill⟩ :=
      exists_galois_finiteEtale_unitCounit_one_killed n k hn hunit X.hom e
    let g := moduleUnitLowerShriekCounit Y.obj.hom n
    let S := ShortComplex.kernelSequence g
    have hS : S.ShortExact := { exact := ShortComplex.kernelSequence_exact g, epi_g := hg }
    let x : X.left := Classical.ofNonempty
    let d := Y.obj.hom.finrank x
    have hd : ∀ z : X.left, Y.obj.hom.finrank z = d := fun z =>
      Y.obj.hom.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace z x
    have hBLC := finiteLowerShriek_isFiniteTypeLocallyConstant X n Y.obj.hom d hd
      (moduleUnit Y.obj.left Λ) (moduleUnit_isFiniteTypeLocallyConstant Y.obj.left Λ)
    have hKLC := moduleKernel_isFiniteTypeLocallyConstant X.left Λ g hBLC
      (moduleUnit_isFiniteTypeLocallyConstant X.left Λ)
    have hBzero : Function.Bijective (moduleDualityTransposeMap.{u, wP, wX, wA}
        X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
        n hn hunit hinv S.X₂ 0 (by decide)) :=
      moduleDualityTransposeMap_proper_zero_bijective.{u, wX, wA, wP}
        X hX n hn hunit hinv S.X₂ hBLC
    have hKzero : Function.Injective (moduleDualityTransposeMap.{u, wP, wX, wA}
        X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
        n hn hunit hinv S.X₁ 0 (by decide)) :=
      proper_dualityTranspose_zero_injective.{u, wX, wA, wP}
        X hX n hn hunit hinv S.X₁ hKLC
    exact moduleDualityTransposeMap_one_eq_zero_of_precomp_eq_zero.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp) n hn hunit hinv hS
      hBzero.surjective hKzero e hkill he
  have hinj : Function.Injective Ψ := by
    intro e e' he
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub, he, sub_self]
  obtain ⟨_, hfinC, hcard⟩ :=
    moduleUnit_one_finite_and_natCard_eq.{u, wP, wX, wA} X hX n hn hunit
  let := hfinC
  exact proper_one_isPerfPair_of_transpose_injective.{u, wX, wA, wP}
    X hX n hn hunit hinv (moduleUnit X.left Λ) hinj hcard

end ProperFinitePerfectness

private theorem originalAddEquiv_toAddHom_apply
    {M : Type uC} {N : Type vC} [AddCommGroup M] [AddCommGroup N]
    (e : M ≃+ N) (x : M) : e.toAddMonoidHom x = e x := rfl

private theorem originalExt_postcomp_apply
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{wC} C]
    {A B D : C} (f : B ⟶ D) (q : ℕ) (c : Ext.{wC} A B q) :
    ((Ext.mk₀ f).postcomp A (add_zero q)) c = c.comp (Ext.mk₀ f) (add_zero q) := rfl
section Shrinking
open GroupCohomology.Kummer.CoefficientBaseChange
variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  {V : Scheme.{u}} (i : V ⟶ U) [IsOpenImmersion i]
  (E : Set X.left) (hEfin : E.Finite) (hEclosed : ∀ x ∈ E, IsClosed ({x} : Set X.left))
  (hE : Set.range (i ≫ j) = Eᶜ)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{wV} (ModuleSheaf V (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]
omit [HasExt.{wV} (ModuleSheaf V (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))] in
/-- The original whole trace rectangle, evaluated at a variable ORIGINAL Ext
class before the Yoneda input is substituted. -/
private theorem moduleCompactSupportTrace_restriction_apply
    (c : Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (i ≫ j) (ULift.{u + 1} (ZMod n))).obj
        ((moduleInverseImage i (ULift.{u + 1} (ZMod n))).obj (moduleRootsOfUnity U n))) 2) :
    moduleCompactSupportTraceAddEquiv X hX E hEfin hEclosed (i ≫ j) hE n hn hunit hinv
      (c.comp (Ext.mk₀ ((moduleLowerShriek (i ≫ j) (ULift.{u + 1} (ZMod n))).map
        (moduleRootsOfUnityInverseImageIso i n hn (levelInvertible j n hinv)).hom))
          (add_zero 2)) =
    moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv
      (c.comp (Ext.mk₀ ((moduleLowerShriekCompIso (ULift.{u + 1} (ZMod n)) j i).hom.app
          ((moduleInverseImage i (ULift.{u + 1} (ZMod n))).obj (moduleRootsOfUnity U n)) ≫
        (moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map
          ((moduleLowerShriekAdjunction i (ULift.{u + 1} (ZMod n))).counit.app
            (moduleRootsOfUnity U n)))) (add_zero 2)) := by
  have h := DFunLike.congr_fun
    (moduleCompactSupportTrace_restriction X hX D hfin hclosed j hD n hn hunit hinv
      i E hEfin hEclosed hE) c
  simpa only [AddMonoidHom.comp_apply, originalExt_postcomp_apply,
    originalAddEquiv_toAddHom_apply] using h
/-- The original smaller-open pairing is the original larger-open pairing on
lower shriek, under the existing composition and Ext-adjunction comparisons. -/
theorem moduleTracePairingLinearMap_lowerShriek
    (F : ModuleSheaf V (ULift.{u + 1} (ZMod n))) (r s : ℕ) (h : r + s = 2)
    (c : Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
        ((moduleLowerShriek i (ULift.{u + 1} (ZMod n))).obj F)) r)
    (e : Ext.{wU} ((moduleLowerShriek i (ULift.{u + 1} (ZMod n))).obj F)
      (moduleRootsOfUnity U n) s) :
    moduleTracePairingLinearMap X hX D hfin hclosed j hD n hn hunit hinv
      ((moduleLowerShriek i (ULift.{u + 1} (ZMod n))).obj F) r s h c e =
    moduleTracePairingLinearMap X hX E hEfin hEclosed (i ≫ j) hE n hn hunit hinv F r s h
      (moduleLowerShriekCompAddEquiv i j (ULift.{u + 1} (ZMod n)) F r c)
      ((moduleLowerShriekExtEquiv i (ULift.{u + 1} (ZMod n)) F
        (moduleRootsOfUnity U n) s e).comp
          (Ext.mk₀ (moduleRootsOfUnityInverseImageIso i n hn (levelInvertible j n hinv)).hom)
            (add_zero s)) := by
  have htrace := moduleCompactSupportTrace_restriction_apply.{u, wX, wA}
    X hX D hfin hclosed j hD i E hEfin hEclosed hE n hn hunit hinv
    (moduleLowerShriekPairing.{wV, wX, u} (i ≫ j) (ULift.{u + 1} (ZMod n))
      (moduleLowerShriekCompAddEquiv i j (ULift.{u + 1} (ZMod n)) F r c)
      (moduleLowerShriekExtEquiv i (ULift.{u + 1} (ZMod n)) F (moduleRootsOfUnity U n) s e) h)
  rw [moduleTracePairingLinearMap_apply_apply, moduleTracePairingLinearMap_apply_apply,
    moduleLowerShriekPairing_eq_comp_counit, moduleLowerShriekPairing_comp_mk₀]
  exact htrace.symm

/-- Shrinking preserves perfectness of the SAME original pairing. The
comparison maps are the existing lower-shriek composition and Ext adjunction. -/
theorem moduleDualityMap_lowerShriek_isPerfPair_iff
    (F : ModuleSheaf V (ULift.{u + 1} (ZMod n))) (r : ℕ) (hr : r ≤ 2) :
    (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv
      ((moduleLowerShriek i (ULift.{u + 1} (ZMod n))).obj F) r hr).IsPerfPair ↔
    (moduleDualityMap X hX E hEfin hEclosed (i ≫ j) hE n hn hunit hinv F r hr).IsPerfPair := by
  let L := AddEquiv.toZModLinearEquiv n
    (moduleLowerShriekCompAddEquiv i j (ULift.{u + 1} (ZMod n)) F r)
  let R := (AddEquiv.toZModLinearEquiv n
    (moduleLowerShriekExtEquiv i (ULift.{u + 1} (ZMod n)) F
      (moduleRootsOfUnity U n) (2 - r))).trans
        (Ext.postcompZModLinearEquiv n
          (moduleRootsOfUnityInverseImageIso i n hn
            (levelInvertible j n hinv)) F (2 - r))
  let B := moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv
    ((moduleLowerShriek i (ULift.{u + 1} (ZMod n))).obj F) r hr
  let C := moduleDualityMap X hX E hEfin hEclosed (i ≫ j) hE n hn hunit hinv F r hr
  have hs : C.compl₁₂ L R = B := by
    ext c e
    exact (moduleTracePairingLinearMap_lowerShriek X hX D hfin hclosed j hD i
      E hEfin hEclosed hE n hn hunit hinv F r (2 - r) (by lia) c e).symm
  change B.IsPerfPair ↔ C.IsPerfPair
  constructor
  · intro hB
    let := hB
    exact LinearMap.IsPerfPair.congr B L.symm R.symm C hs
  · intro hC
    let := hC
    rw [← hs]
    exact LinearMap.IsPerfPair.compl₁₂ C L R
end Shrinking

section ProperSourceHighVanishing

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  [HasExt.{wP} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]

include hX hn hunit in
set_option backward.isDefEq.respectTransparency false in
/-- Proper higher source Ext vanishes for every original finite local system.
The actual internal Hom is finite locally constant by its finite-presentation
charts; the original Ext/cohomology comparison and proper high vanishing then
give the result. The source and abelian Ext worlds are independent. -/
theorem moduleSourceExt_high_subsingleton_of_finiteLocallyConstant
    (F : ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X.left (ULift.{u + 1} (ZMod n))).inverse.obj F))
    (q : ℕ) (hq : 2 < q) :
    Subsingleton (Ext.{wP} F (moduleRootsOfUnity X.left n) q) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let Λ := ULift.{u + 1} (ZMod n)
  let : (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).Full :=
    ModuleCat.uLiftZMod_forget₂_full n
  let E := moduleSheafEquivalence X.left Λ
  have hRoots : Constructible.Modules.IsFiniteTypeLocallyConstant
      (E.inverse.obj (moduleRootsOfUnity X.left n)) :=
    (Constructible.Modules.isFiniteTypeLocallyConstant_iff_of_iso
      (E.inverse.mapIso (moduleUnitRootsIso k n hn hunit X.hom))).mp
        (moduleUnit_isFiniteTypeLocallyConstant X.left Λ)
  let H := SheafOfModules.InternalHom.sheaf
    (ModuleCat.Sheaf.ConstantRing.commutativeSheaf X.left.smallEtaleTopology Λ)
      F (moduleRootsOfUnity X.left n)
  have hH : Constructible.Modules.IsFiniteTypeLocallyConstant (E.inverse.obj H) :=
    Constructible.Modules.isFiniteTypeLocallyConstant_nativeInternalHom
      Λ F (moduleRootsOfUnity X.left n) hF hRoots
  let : Subsingleton (Ext.{wP} (moduleUnit X.left Λ) H q) :=
    Curves.moduleUnitExt_subsingleton_of_finiteLocallyConstant X hX n hn hunit q hq H hH
  let Q := SheafOfModules.toSheaf (constantRing X.left Λ)
  let E₀ : Ext.{wP} (moduleUnit X.left Λ) H q ≃+ Sheaf.H.{wA} (Q.obj H) q :=
    etaleModuleExtCohomologyAddEquivLargeScalars X.left (constantRing X.left Λ) H q
  let : Subsingleton (Sheaf.H.{wA} (Q.obj H) q) := E₀.symm.injective.subsingleton
  let E₁ : Ext.{wP} F (moduleRootsOfUnity X.left n) q ≃+ Sheaf.H.{wA} (Q.obj H) q :=
    locallyConstantExtCohomologyAddEquiv.{u, wP, wA} k n hn hunit X.hom F hF q
  exact E₁.injective.subsingleton

end ProperSourceHighVanishing

section ProperCoverAllDegrees

universe wSY wAY

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{wP} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]

open GroupCohomology.Kummer.CoefficientBaseChange

private theorem proper_finiteLowerShriek_isPerfPair
    (Y : FScheme k) (hY : Curve.Properties Y) (f : Y ⟶ X)
    [IsFinite f.left] [IsDominant f.left] [Etale f.left]
    (d : ℕ) (hd : ∀ x : X.left, f.left.finrank x = d)
    [HasExt.{wY} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wSY} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wAY} (AbelianSheaf.{u, u + 1} Y.left)]
    (P : ModuleSheaf Y.left (ULift.{u + 1} (ZMod n))) (r : ℕ) (hr : r ≤ 2)
    (hP : (moduleDualityMap.{u, wSY, wY, wAY} Y hY ∅ Set.finite_empty (by simp)
      (𝟙 Y.left) (by simp) n hn hunit (levelInvertible f.left n hinv) P r hr).IsPerfPair) :
    (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv
        ((moduleLowerShriek f.left (ULift.{u + 1} (ZMod n))).obj P) r hr).IsPerfPair := by
  let L := AddEquiv.toZModLinearEquiv n
    (moduleFiniteLowerShriekCompactExtAddEquiv.{u, wX, wY} f.left n d hd P r)
  let R := AddEquiv.toZModLinearEquiv n
    (moduleFiniteLowerShriekRootsExtAddEquiv.{u, wP, wSY} f.left n hn hinv P (2 - r))
  let B := moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
    (𝟙 X.left) (by simp) n hn hunit hinv
      ((moduleLowerShriek f.left (ULift.{u + 1} (ZMod n))).obj P) r hr
  let C := moduleDualityMap.{u, wSY, wY, wAY} Y hY ∅ Set.finite_empty (by simp)
    (𝟙 Y.left) (by simp) n hn hunit (levelInvertible f.left n hinv) P r hr
  have hs : C.compl₁₂ L R = B := by
    ext c e
    simp only [LinearMap.compl₁₂_apply, L, R, LinearEquiv.coe_coe,
      originalAddEquiv_toZModLinearEquiv_apply]
    exact (moduleTracePairingLinearMap_finiteLowerShriek.{u, wX, wY, wA, wAY, wP, wSY}
      X Y hX hY f n d hd hn hunit hinv P r (2 - r) (by lia) c e).symm
  let : C.IsPerfPair := hP
  change B.IsPerfPair
  rw [← hs]
  exact LinearMap.IsPerfPair.compl₁₂ C L R

/-- The original proper unit pairing is perfect in every allowed degree. -/
theorem moduleDualityMap_unit_proper_isPerfPair (r : ℕ) (hr : r ≤ 2) :
    (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv
      (moduleUnit X.left (ULift.{u + 1} (ZMod n))) r hr).IsPerfPair := by
  interval_cases r
  · exact moduleDualityMap_unit_zero_isPerfPair.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp) n hn hunit hinv
  · exact moduleDualityMap_unit_proper_one_isPerfPair.{u, wX, wA, wP}
      X hX n hn hunit hinv
  · exact moduleDualityMap_unit_two_isPerfPair.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp) n hn hunit hinv

private theorem proper_unit_biproduct_isPerfPair (m r : ℕ) (hr : r ≤ 2) :
    (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv
      (⨁ fun _ : Fin m => moduleUnit X.left (ULift.{u + 1} (ZMod n))) r hr).IsPerfPair := by
  exact moduleDualityMap_bicone_isPerfPair.{u, 0, wP, wX, wA}
    X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp) n hn hunit hinv
    (biproduct.isBilimit (fun _ : Fin m => moduleUnit X.left (ULift.{u + 1} (ZMod n))))
    r hr (fun _ => moduleDualityMap_unit_proper_isPerfPair.{u, wX, wA, wP}
      X hX n hn hunit hinv r hr)

/-- Actual finite étale direct images of original unit powers have the
original proper perfect pairing in every complementary degree. -/
theorem moduleDualityMap_galois_unit_biproduct_directImage_isPerfPair
    (Y : Scheme.FiniteEtale X.left) [ConnectedSpace Y.obj.left] [Surjective Y.obj.hom]
    (m r : ℕ) (hr : r ≤ 2) :
    (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv
      ((moduleDirectImage Y.obj.hom (ULift.{u + 1} (ZMod n))).obj
        (⨁ fun _ : Fin m => moduleUnit Y.obj.left (ULift.{u + 1} (ZMod n)))) r hr).IsPerfPair := by
  let : ConnectedSpace X.left := Curve.curveProperties_connectedSpace hX
  let Z : FScheme k := Over.mk (Y.obj.hom ≫ X.hom)
  let hZ : Curve.Properties Z := Curves.curveProperties_of_connected_finiteEtale X hX Y
  let f : Z ⟶ X := Over.homMk Y.obj.hom rfl
  let : IsFinite f.left := inferInstanceAs (IsFinite Y.obj.hom)
  let : Etale f.left := inferInstanceAs (Etale Y.obj.hom)
  let : IsDominant f.left := ⟨Y.obj.hom.surjective.denseRange⟩
  let x : X.left := Classical.ofNonempty
  let d := Y.obj.hom.finrank x
  have hd : ∀ z : X.left, f.left.finrank z = d := fun z =>
    Y.obj.hom.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace z x
  let : HasExt.{u + 2} (ModuleSheaf Z.left (ULift.{u + 1} (ZMod n))) :=
    SheafOfModules.hasExt (constantRing Z.left (ULift.{u + 1} (ZMod n)))
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Z.left) := hasExtStandard Z.left
  let P := ⨁ fun _ : Fin m => moduleUnit Z.left (ULift.{u + 1} (ZMod n))
  have hP : (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv
      ((moduleLowerShriek Y.obj.hom (ULift.{u + 1} (ZMod n))).obj P) r hr).IsPerfPair :=
    proper_finiteLowerShriek_isPerfPair.{u, wX, wA, wP, u + 2, u + 2, u + 2}
      X hX n hn hunit hinv Z hZ f d hd P r hr
      (proper_unit_biproduct_isPerfPair.{u, u + 2, u + 2, u + 2}
        Z hZ n hn hunit (levelInvertible f.left n hinv) m r hr)
  exact (moduleDualityMap_isPerfPair_iff_of_iso.{u, wP, wX, wA}
    X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp) n hn hunit hinv
    ((moduleFiniteEtaleLowerShriekDirectImageIso Y.obj.hom n d hd).app P) r hr).mp hP

end ProperCoverAllDegrees

section ProperTopTranspose

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{wP} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]

private theorem proper_two_transpose_eq_flip
    (F : ModuleSheaf X.left (ULift.{u + 1} (ZMod n))) :
    moduleDualityTransposeMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv F 2 le_rfl =
    (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv F 0 (by decide)).flip := rfl

private theorem proper_two_transpose_bijective_of_zero_isPerfPair
    (F : ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))
    (hF : (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv F 0 (by decide)).IsPerfPair) :
    Function.Bijective (moduleDualityTransposeMap.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
      n hn hunit hinv F 2 le_rfl) := by
  rw [proper_two_transpose_eq_flip.{u, wX, wA, wP} X hX n hn hunit hinv F]
  exact hF.bijective_right

private theorem proper_dualityTranspose_two_surjective
    (F : ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X.left (ULift.{u + 1} (ZMod n))).inverse.obj F)) :
    Function.Surjective (moduleDualityTransposeMap.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
      n hn hunit hinv F 2 le_rfl) := by
  let : ConnectedSpace X.left := Curve.curveProperties_connectedSpace hX
  obtain ⟨Y, _, hc, hs, m, a, ha⟩ := exists_galois_unit_biproduct_directImage_mono n hn F hF
  let : ConnectedSpace Y.obj.left := hc
  let : Surjective Y.obj.hom := hs
  let S := ShortComplex.cokernelSequence a
  have hS : S.ShortExact := { exact := ShortComplex.cokernelSequence_exact a, mono_f := ha }
  have hB : (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv S.X₂ 0 (by decide)).IsPerfPair :=
    moduleDualityMap_galois_unit_biproduct_directImage_isPerfPair.{u, wX, wA, wP}
      X hX n hn hunit hinv Y m 0 (by decide)
  apply moduleDualityTransposeMap_two_surjective_of_shortExact.{u, wP, wX, wA}
    X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp) n hn hunit hinv hS
  exact (proper_two_transpose_bijective_of_zero_isPerfPair.{u, wX, wA, wP}
    X hX n hn hunit hinv S.X₂ hB).surjective

/-- The original source-degree-two proper adjoint is bijective for every
finite local system. First extend compact-zero functionals uniformly through
actual cofree embeddings, then use genuine E3 vanishing and the same exact
dual row for injectivity. No copresentation object or finite-group premise is used. -/
theorem moduleDualityTransposeMap_proper_two_bijective
    (F : ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X.left (ULift.{u + 1} (ZMod n))).inverse.obj F)) :
    Function.Bijective (moduleDualityTransposeMap.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
      n hn hunit hinv F 2 le_rfl) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : ConnectedSpace X.left := Curve.curveProperties_connectedSpace hX
  refine ⟨?_, proper_dualityTranspose_two_surjective.{u, wX, wA, wP}
    X hX n hn hunit hinv F hF⟩
  obtain ⟨Y, _, hc, hs, m, a, ha⟩ := exists_galois_unit_biproduct_directImage_mono n hn F hF
  let : ConnectedSpace Y.obj.left := hc
  let : Surjective Y.obj.hom := hs
  let Λ := ULift.{u + 1} (ZMod n)
  let B := (moduleDirectImage Y.obj.hom Λ).obj
    (⨁ fun _ : Fin m => moduleUnit Y.obj.left Λ)
  have hBLC := moduleDirectImage_isFiniteTypeLocallyConstant Λ Y.obj.hom
    (⨁ fun _ : Fin m => moduleUnit Y.obj.left Λ)
    (moduleUnitBiproduct_isFiniteTypeLocallyConstant Y.obj.left Λ m)
  have hKLC := moduleCokernel_isFiniteTypeLocallyConstant Λ a hF hBLC
  let S := ShortComplex.cokernelSequence a
  have hS : S.ShortExact := { exact := ShortComplex.cokernelSequence_exact a, mono_f := ha }
  let : Subsingleton (Ext.{wP} S.X₃ (moduleRootsOfUnity X.left n) 3) := by
    change Subsingleton (Ext.{wP} (cokernel a) (moduleRootsOfUnity X.left n) 3)
    exact moduleSourceExt_high_subsingleton_of_finiteLocallyConstant.{u, wA, wP}
      X hX n hn hunit (cokernel a) hKLC 3 (by decide)
  have hB : (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv B 0 (by decide)).IsPerfPair :=
    moduleDualityMap_galois_unit_biproduct_directImage_isPerfPair.{u, wX, wA, wP}
      X hX n hn hunit hinv Y m 0 (by decide)
  have hK : Function.Surjective (moduleDualityTransposeMap.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
      n hn hunit hinv S.X₃ 2 le_rfl) :=
    proper_dualityTranspose_two_surjective.{u, wX, wA, wP}
      X hX n hn hunit hinv S.X₃ hKLC
  apply moduleDualityTransposeMap_two_injective_of_shortExact.{u, wP, wX, wA}
    X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp) n hn hunit hinv hS
  · dsimp only [S, ShortComplex.cokernelSequence]
    exact (proper_two_transpose_bijective_of_zero_isPerfPair.{u, wX, wA, wP}
      X hX n hn hunit hinv B hB).injective
  · exact hK

end ProperTopTranspose

section ProperMiddleTranspose

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{wP} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]

private theorem proper_one_transpose_bijective_of_one_isPerfPair
    (F : ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))
    (hF : (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv F 1 (by decide)).IsPerfPair) :
    Function.Bijective (moduleDualityTransposeMap.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
      n hn hunit hinv F 1 (by decide)) := by
  rw [proper_one_transpose_eq_flip.{u, wX, wA, wP} X hX n hn hunit hinv F]
  exact hF.bijective_right

private theorem proper_dualityTranspose_one_surjective
    (F : ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X.left (ULift.{u + 1} (ZMod n))).inverse.obj F)) :
    Function.Surjective (moduleDualityTransposeMap.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
      n hn hunit hinv F 1 (by decide)) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : ConnectedSpace X.left := Curve.curveProperties_connectedSpace hX
  obtain ⟨Y, _, hc, hs, m, a, ha⟩ := exists_galois_unit_biproduct_directImage_mono n hn F hF
  let : ConnectedSpace Y.obj.left := hc
  let : Surjective Y.obj.hom := hs
  let Λ := ULift.{u + 1} (ZMod n)
  let B := (moduleDirectImage Y.obj.hom (ULift.{u + 1} (ZMod n))).obj
    (⨁ fun _ : Fin m => moduleUnit Y.obj.left (ULift.{u + 1} (ZMod n)))
  have hBLC := moduleDirectImage_isFiniteTypeLocallyConstant Λ Y.obj.hom
    (⨁ fun _ : Fin m => moduleUnit Y.obj.left Λ)
    (moduleUnitBiproduct_isFiniteTypeLocallyConstant Y.obj.left Λ m)
  have hKLC := moduleCokernel_isFiniteTypeLocallyConstant Λ a hF hBLC
  have hB : (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv B 1 (by decide)).IsPerfPair :=
    moduleDualityMap_galois_unit_biproduct_directImage_isPerfPair.{u, wX, wA, wP}
      X hX n hn hunit hinv Y m 1 (by decide)
  have hB₁ : Function.Bijective (moduleDualityTransposeMap.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
      n hn hunit hinv B 1 (by decide)) :=
    proper_one_transpose_bijective_of_one_isPerfPair.{u, wX, wA, wP}
      X hX n hn hunit hinv B hB
  have hB₂ : Function.Bijective (moduleDualityTransposeMap.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
      n hn hunit hinv B 2 le_rfl) :=
    moduleDualityTransposeMap_proper_two_bijective.{u, wX, wA, wP}
      X hX n hn hunit hinv B hBLC
  have hK₂ : Function.Bijective (moduleDualityTransposeMap.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
      n hn hunit hinv (cokernel a) 2 le_rfl) :=
    moduleDualityTransposeMap_proper_two_bijective.{u, wX, wA, wP}
      X hX n hn hunit hinv (cokernel a) hKLC
  let S := ShortComplex.cokernelSequence a
  have hS : S.ShortExact := { exact := ShortComplex.cokernelSequence_exact a, mono_f := ha }
  apply moduleDualityTransposeMap_one_surjective_of_shortExact.{u, wP, wX, wA}
    X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp) n hn hunit hinv hS
  · dsimp only [S, ShortComplex.cokernelSequence]
    exact hB₁.surjective
  · dsimp only [S, ShortComplex.cokernelSequence]
    exact hK₂.surjective
  · dsimp only [S, ShortComplex.cokernelSequence]
    exact hB₂.injective

/-- The original middle proper adjoint is bijective on every finite local
system. Surjectivity is proved uniformly first; only then is it used for the
actual cokernel in the original unsigned-boundary injectivity row. -/
theorem moduleDualityTransposeMap_proper_one_bijective
    (F : ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X.left (ULift.{u + 1} (ZMod n))).inverse.obj F)) :
    Function.Bijective (moduleDualityTransposeMap.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
      n hn hunit hinv F 1 (by decide)) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : ConnectedSpace X.left := Curve.curveProperties_connectedSpace hX
  refine ⟨?_, proper_dualityTranspose_one_surjective.{u, wX, wA, wP}
    X hX n hn hunit hinv F hF⟩
  obtain ⟨Y, _, hc, hs, m, a, ha⟩ := exists_galois_unit_biproduct_directImage_mono n hn F hF
  let : ConnectedSpace Y.obj.left := hc
  let : Surjective Y.obj.hom := hs
  let Λ := ULift.{u + 1} (ZMod n)
  let B := (moduleDirectImage Y.obj.hom (ULift.{u + 1} (ZMod n))).obj
    (⨁ fun _ : Fin m => moduleUnit Y.obj.left (ULift.{u + 1} (ZMod n)))
  have hBLC := moduleDirectImage_isFiniteTypeLocallyConstant Λ Y.obj.hom
    (⨁ fun _ : Fin m => moduleUnit Y.obj.left Λ)
    (moduleUnitBiproduct_isFiniteTypeLocallyConstant Y.obj.left Λ m)
  have hKLC := moduleCokernel_isFiniteTypeLocallyConstant Λ a hF hBLC
  have hB : (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv B 1 (by decide)).IsPerfPair :=
    moduleDualityMap_galois_unit_biproduct_directImage_isPerfPair.{u, wX, wA, wP}
      X hX n hn hunit hinv Y m 1 (by decide)
  have hB₁ : Function.Bijective (moduleDualityTransposeMap.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
      n hn hunit hinv B 1 (by decide)) :=
    proper_one_transpose_bijective_of_one_isPerfPair.{u, wX, wA, wP}
      X hX n hn hunit hinv B hB
  have hK₁ : Function.Surjective (moduleDualityTransposeMap.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
      n hn hunit hinv (cokernel a) 1 (by decide)) :=
    proper_dualityTranspose_one_surjective.{u, wX, wA, wP}
      X hX n hn hunit hinv (cokernel a) hKLC
  have hK₂ : Function.Bijective (moduleDualityTransposeMap.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
      n hn hunit hinv (cokernel a) 2 le_rfl) :=
    moduleDualityTransposeMap_proper_two_bijective.{u, wX, wA, wP}
      X hX n hn hunit hinv (cokernel a) hKLC
  let S := ShortComplex.cokernelSequence a
  have hS : S.ShortExact := { exact := ShortComplex.cokernelSequence_exact a, mono_f := ha }
  apply moduleDualityTransposeMap_one_injective_of_shortExact.{u, wP, wX, wA}
    X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp) n hn hunit hinv hS
  · dsimp only [S, ShortComplex.cokernelSequence]
    exact hB₁.injective
  · dsimp only [S, ShortComplex.cokernelSequence]
    exact hK₁
  · dsimp only [S, ShortComplex.cokernelSequence]
    exact hK₂.injective

end ProperMiddleTranspose

section ProperFinalPerfectness

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{wP} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]

/-- Both adjoints of the original proper trace pairing are bijective for
every finite local system, at every positive invertible level. -/
theorem moduleDualityMap_proper_isPerfPair
    (F : ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X.left (ULift.{u + 1} (ZMod n))).inverse.obj F))
    (r : ℕ) (hr : r ≤ 2) :
    (moduleDualityMap.{u, wP, wX, wA} X hX ∅ Set.finite_empty (by simp)
      (𝟙 X.left) (by simp) n hn hunit hinv F r hr).IsPerfPair := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : Finite (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X.left) (ULift.{u + 1} (ZMod n))).obj F) r) :=
    moduleUnitCompactIdExt_finite_of_finiteLocallyConstant.{u, wX, wA} X hX n hn hunit F hF r
  interval_cases r
  · have h := moduleDualityTransposeMap_proper_two_bijective.{u, wX, wA, wP}
      X hX n hn hunit hinv F hF
    rw [proper_two_transpose_eq_flip.{u, wX, wA, wP} X hX n hn hunit hinv F] at h
    exact (ZMod.isPerfPair_iff_flip_bijective n _).mpr h
  · have h := moduleDualityTransposeMap_proper_one_bijective.{u, wX, wA, wP}
      X hX n hn hunit hinv F hF
    rw [proper_one_transpose_eq_flip.{u, wX, wA, wP} X hX n hn hunit hinv F] at h
    exact (ZMod.isPerfPair_iff_flip_bijective n _).mpr h
  · have h := moduleDualityTransposeMap_proper_zero_bijective.{u, wX, wA, wP}
      X hX n hn hunit hinv F hF
    rw [proper_zero_transpose_eq_flip.{u, wX, wA, wP} X hX n hn hunit hinv F] at h
    exact (ZMod.isPerfPair_iff_flip_bijective n _).mpr h

end ProperFinalPerfectness

end AlgebraicGeometry.Scheme.EtaleCohomology
