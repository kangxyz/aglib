/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.TracePairing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteEtalePresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ConstantPerfectness
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.LowerShriekExt
public import Aglib.AlgebraicGeometry.EtaleCohomology.Coefficients.ModuleCohomologyPullback
public import Aglib.Algebra.Module.ZMod.Dual
public import Aglib.Algebra.Homology.DerivedCategory.Ext.PairingBiproduct
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Original coefficient and boundary squares for curve duality

The actual transposed trace pairing intertwines the original coefficient maps
and the unsigned source extension-class boundary with the native dual compact
maps. The surjective étale lower-shriek counit and its whole Ext pullback square
are supplied independently of finite étale ambidexterity or trace compatibility.
Actual finite Galois trivializations and finite module presentations also give
epimorphisms from lower shrieks of finite biproducts of the original units.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w w' w''

open Coefficients Scheme.OverField

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard moduleSheafExtZModModule

attribute [local instance] moduleSheaf_hasFiniteBiproducts



section SurjectiveEtale

variable {V U : Scheme.{u}} (f : V ⟶ U) [Etale f]
  (Λ : Type (u + 1)) [CommRing Λ]

variable [HasExt.{w} (ModuleSheaf V Λ)] [HasExt.{w'} (ModuleSheaf U Λ)]

/-- Precomposition by the original lower-shriek counit is exactly inverse image
under the original Ext adjunction, as an equality of entire homomorphisms. -/
theorem moduleLowerShriekExtEquiv_counit_precomp (M N : ModuleSheaf U Λ) (q : ℕ) :
    (moduleLowerShriekExtEquiv f Λ ((moduleInverseImage f Λ).obj M) N q).toAddMonoidHom.comp
        ((Ext.mk₀ ((moduleLowerShriekAdjunction f Λ).counit.app M)).precomp N
          (zero_add q)) =
      (moduleInverseImage f Λ).mapExtAddHom M N q := by
  ext e
  change moduleLowerShriekExtEquiv f Λ _ N q
      ((Ext.mk₀ ((moduleLowerShriekAdjunction f Λ).counit.app M)).comp e (zero_add q)) = _
  rw [moduleLowerShriekExtEquiv_comp_right, moduleLowerShriekExtEquiv_mk₀]
  have h : (moduleLowerShriekAdjunction f Λ).homEquiv _ _
      ((moduleLowerShriekAdjunction f Λ).counit.app M) = 𝟙 _ := by
    simp [Adjunction.homEquiv_unit]
  rw [h, Ext.mk₀_id_comp]
  rfl

end SurjectiveEtale

section UnitCounit

variable {V U : Scheme.{u}} (f : V ⟶ U) [Etale f] (n : ℕ)

variable [HasExt.{w} (ModuleSheaf V (ULift.{u + 1} (ZMod n)))]
  [HasExt.{w'} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]

/-- Under the original Ext adjunction, precomposition by the actual normalized
unit counit is precisely the original native module-unit pullback, as a whole map. -/
theorem moduleUnitLowerShriekCounit_ext_square
    (M : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (q : ℕ) :
    (moduleLowerShriekExtEquiv f (ULift.{u + 1} (ZMod n))
        (moduleUnit V (ULift.{u + 1} (ZMod n))) M q).toAddMonoidHom.comp
        ((Ext.mk₀ (moduleUnitLowerShriekCounit f n)).precomp M (zero_add q)) =
      moduleUnitExtPullback f n M q := by
  ext e
  have hmk : Ext.mk₀ (moduleUnitLowerShriekCounit f n) =
      (moduleLowerShriekExt f (ULift.{u + 1} (ZMod n)) _ _ 0
        (Ext.mk₀ (moduleUnitInverseImageIso f n).inv)).comp
        (Ext.mk₀ ((moduleLowerShriekAdjunction f (ULift.{u + 1} (ZMod n))).counit.app
          (moduleUnit U (ULift.{u + 1} (ZMod n))))) (add_zero 0) := by
    rw [moduleLowerShriekExt_mk₀, Ext.mk₀_comp_mk₀]
    rfl
  change moduleLowerShriekExtEquiv f _ _ M q
    ((Ext.mk₀ (moduleUnitLowerShriekCounit f n)).comp e (zero_add q)) = _
  rw [hmk, Ext.comp_assoc_of_second_deg_zero, moduleLowerShriekExtEquiv_comp_left]
  have hc := DFunLike.congr_fun (moduleLowerShriekExtEquiv_counit_precomp f
    (ULift.{u + 1} (ZMod n)) (moduleUnit U (ULift.{u + 1} (ZMod n))) M q) e
  change moduleLowerShriekExtEquiv f _ _ M q
    ((Ext.mk₀ ((moduleLowerShriekAdjunction f (ULift.{u + 1} (ZMod n))).counit.app
      (moduleUnit U (ULift.{u + 1} (ZMod n))))).comp e (zero_add q)) = _ at hc
  rw [hc]
  rfl

end UnitCounit



section CurvePairing

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{w} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{w'} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{w''} (AbelianSheaf.{u, u + 1} X.left)]

/-- The whole native transpose map sends original source precomposition to
the dual of original compact-support coefficient postcomposition. -/
theorem moduleDualityTransposeMap_naturality
    {F F' : ModuleSheaf U (ULift.{u + 1} (ZMod n))} (f : F ⟶ F')
    (s : ℕ) (hs : s ≤ 2) :
    (moduleDualityTransposeMap X hX D hfin hclosed j hD n hn hunit hinv F s hs).comp
        (AddMonoidHom.toZModLinearMap n
          ((Ext.mk₀ f).precomp (moduleRootsOfUnity U n) (zero_add s))) =
      (AddMonoidHom.toZModLinearMap n
        ((Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map f)).postcomp
          (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (add_zero (2 - s)))).dualMap.comp
        (moduleDualityTransposeMap X hX D hfin hclosed j hD n hn hunit hinv F' s hs) := by
  have h := moduleTracePairingLinearMap_naturality X hX D hfin hclosed j hD
    n hn hunit hinv f (2 - s) s (by lia)
  ext e c
  exact (LinearMap.congr_fun (LinearMap.congr_fun h c) e).symm

/-- The whole native transpose map identifies the unsigned source extension
boundary with the dual of the original compact-support extension boundary.
Mathlib's signed `Ext.δ` is not substituted for this map. -/
theorem moduleDualityTransposeMap_extClass
    {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    (s : ℕ) (hs : s + 1 ≤ 2) :
    (moduleDualityTransposeMap X hX D hfin hclosed j hD n hn hunit hinv
        S.X₃ (s + 1) hs).comp
        (AddMonoidHom.toZModLinearMap n
          (hS.extClass.precomp (moduleRootsOfUnity U n) (add_comm 1 s))) =
      (AddMonoidHom.toZModLinearMap n
        ((shortExact_moduleLowerShriek j (ULift.{u + 1} (ZMod n)) hS).extClass.postcomp
          (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
          (show (2 - (s + 1)) + 1 = 2 - s by lia))).dualMap.comp
        (moduleDualityTransposeMap X hX D hfin hclosed j hD n hn hunit hinv
          S.X₁ s (by lia)) := by
  have h := moduleTracePairingLinearMap_extClass X hX D hfin hclosed j hD
    n hn hunit hinv hS (2 - (s + 1)) (2 - s) s (s + 1)
    (by lia) (add_comm 1 s) (by lia) (by lia)
  ext e c
  exact (LinearMap.congr_fun (LinearMap.congr_fun h c) e).symm

/-- The original degree-two pairing is perfect for every finite biproduct of
native unit coefficients, by the proved original finite-SUM pairing law. -/
theorem moduleDualityMap_unit_biproduct_two_isPerfPair (m : ℕ) :
    (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv
      (⨁ fun _ : Fin m => moduleUnit U (ULift.{u + 1} (ZMod n))) 2 le_rfl).IsPerfPair := by
  let L := moduleLowerShriek j (ULift.{u + 1} (ZMod n))
  let A := moduleUnit X.left (ULift.{u + 1} (ZMod n))
  let F : Fin m → ModuleSheaf U (ULift.{u + 1} (ZMod n)) :=
    fun _ => moduleUnit U (ULift.{u + 1} (ZMod n))
  let τ := moduleCompactSupportTraceLinearMap X hX D hfin hclosed j hD n hn hunit hinv
  exact Functor.isPerfPair_extPairingLinearMap_compr₂_biproduct L A n
    (biproduct.isBilimit F) (moduleRootsOfUnity U n) 2 0 2 rfl τ
    (fun _ => moduleDualityMap_unit_two_isPerfPair X hX D hfin hclosed j hD n hn hunit hinv)

/-- The original constant free-module coefficient inherits perfectness through
its actual native unit-power comparison, without a new pairing. -/
theorem moduleDualityMap_constantFree_two_isPerfPair (m : ℕ) :
    (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv
      ((moduleSheafEquivalence U (ULift.{u + 1} (ZMod n))).functor.obj
        ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))).obj
          (ModuleCat.of (ULift.{u + 1} (ZMod n)) (Fin m → ULift.{u + 1} (ZMod n)))))
      2 le_rfl).IsPerfPair := by
  let L := moduleLowerShriek j (ULift.{u + 1} (ZMod n))
  let A := moduleUnit X.left (ULift.{u + 1} (ZMod n))
  let τ := moduleCompactSupportTraceLinearMap X hX D hfin hclosed j hD n hn hunit hinv
  exact (Functor.isPerfPair_extPairingLinearMap_compr₂_iso_iff L A n
    (moduleFiniteFreeConstantIso U (ULift.{u + 1} (ZMod n)) m) 2 0 2 rfl τ).mpr
      (moduleDualityMap_unit_biproduct_two_isPerfPair X hX D hfin hclosed j hD
        n hn hunit hinv m)

/-- Injectivity in source degree zero descends along an actual coefficient
epimorphism, by the original coefficient square and native Ext exactness. -/
theorem moduleDualityTransposeMap_zero_injective_of_shortExact
    {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    (hB : Function.Injective (moduleDualityTransposeMap X hX D hfin hclosed j hD
      n hn hunit hinv S.X₂ 0 (by decide))) :
    Function.Injective (moduleDualityTransposeMap X hX D hfin hclosed j hD
      n hn hunit hinv S.X₃ 0 (by decide)) := by
  let : Epi S.g := hS.epi_g
  intro a b hab
  apply Ext.precomp_mk₀_injective_of_epi (moduleRootsOfUnity U n) S.g
  apply hB
  have hsq := moduleDualityTransposeMap_naturality X hX D hfin hclosed j hD
    n hn hunit hinv S.g 0 (by decide)
  have ha := LinearMap.congr_fun hsq a
  have hb := LinearMap.congr_fun hsq b
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at ha hb
  exact ha.trans ((congrArg _ hab).trans hb.symm)

/-- Surjectivity in source degree zero follows from the same actual coefficient
sequence once degree three compact support of its kernel vanishes and the two
preceding degree-zero transpose maps have the stated properties. -/
theorem moduleDualityTransposeMap_zero_surjective_of_shortExact
    {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    [Subsingleton (Ext.{w'} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj S.X₁) 3)]
    (hB : Function.Surjective (moduleDualityTransposeMap X hX D hfin hclosed j hD
      n hn hunit hinv S.X₂ 0 (by decide)))
    (hK : Function.Injective (moduleDualityTransposeMap X hX D hfin hclosed j hD
      n hn hunit hinv S.X₁ 0 (by decide))) :
    Function.Surjective (moduleDualityTransposeMap X hX D hfin hclosed j hD
      n hn hunit hinv S.X₃ 0 (by decide)) := by
  let i := AddMonoidHom.toZModLinearMap n
    ((Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map S.f)).postcomp
      (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (add_zero 2))
  let g := AddMonoidHom.toZModLinearMap n
    ((Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map S.g)).postcomp
      (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (add_zero 2))
  have hig : Function.Exact i g := by
    have h := Ext.covariant_sequence_exact₂'
      (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      (shortExact_moduleLowerShriek j (ULift.{u + 1} (ZMod n)) hS) 2
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact h
  let : Subsingleton (Ext.{w'} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      (S.map (moduleLowerShriek j (ULift.{u + 1} (ZMod n)))).X₁ 3) := by
    change Subsingleton (Ext.{w'} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj S.X₁) 3)
    infer_instance
  have hg : Function.Surjective g := by
    intro c
    exact Ext.covariant_sequence_exact₃
      (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      (shortExact_moduleLowerShriek j (ULift.{u + 1} (ZMod n)) hS) c
      (show 2 + 1 = 3 from rfl) (Subsingleton.elim _ _)
  intro l
  obtain ⟨b, hb⟩ := hB (g.dualMap l)
  have hf : (Ext.mk₀ S.f).comp b (zero_add 0) = 0 := by
    apply hK
    rw [map_zero]
    have hv := LinearMap.congr_fun
      (moduleDualityTransposeMap_naturality X hX D hfin hclosed j hD n hn hunit hinv
        S.f 0 (by decide)) b
    change moduleDualityTransposeMap X hX D hfin hclosed j hD n hn hunit hinv
      S.X₁ 0 (by decide) ((Ext.mk₀ S.f).comp b (zero_add 0)) =
        i.dualMap (moduleDualityTransposeMap X hX D hfin hclosed j hD n hn hunit hinv
          S.X₂ 0 (by decide) b) at hv
    rw [hv, hb]
    ext c
    change l (g (i c)) = 0
    rw [hig.apply_apply_eq_zero, map_zero]
  obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₂ hS (moduleRootsOfUnity U n) b hf
  refine ⟨a, ?_⟩
  apply LinearMap.dualMap_injective_of_surjective hg
  have hv := LinearMap.congr_fun
    (moduleDualityTransposeMap_naturality X hX D hfin hclosed j hD n hn hunit hinv
      S.g 0 (by decide)) a
  change moduleDualityTransposeMap X hX D hfin hclosed j hD n hn hunit hinv
    S.X₂ 0 (by decide) ((Ext.mk₀ S.g).comp a (zero_add 0)) =
      g.dualMap (moduleDualityTransposeMap X hX D hfin hclosed j hD n hn hunit hinv
        S.X₃ 0 (by decide) a) at hv
  rw [ha, hb] at hv
  exact hv.symm

end CurvePairing

end AlgebraicGeometry.Scheme.EtaleCohomology
