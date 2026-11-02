/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.LowerShriekCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.OnePointRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.Complement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ModuleShortExact
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.LowerShriekExt
public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.OpenLocalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.Trace
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Point-support purity in the original constant-ring module category

The point-unit map is the original inverse-image adjunction unit followed by
the selected native unit comparison. Precomposition with this actual map,
then the original module-unit/roots comparison, gives the support-forgetting
map to ordinary roots cohomology. On a smooth proper curve, the original
module unit localization sequence, the one-point H0/H1 restriction isomorphisms
and ordinary open-curve vanishing show that supported Ext vanishes except in
degree two. The point-unit map identifies degree two with ordinary H2; the
original Kummer boundary of O(x), followed by the original trace, fixes its
normalization.

For a closed point in a given open subcurve, closed-support excision keeps
the canonical Spec κ(x) and its original composite map to the proper curve.
The module Ext universe remains arbitrary; only the auxiliary Ext on the
proper completion uses the existing standard size. Positive invertible
composite levels and level one are included. No strict-local cohomology model,
external Gysin generator or SGA sign comparison is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients

universe u wM wA wMU wAU

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

section PointMaps

variable {Z X : Scheme.{u}} (i : Z ⟶ X) (n : ℕ)

/-- The original point-unit arrow on actual constant-ring module objects.
Its construction is valid for any morphism, before the closed-point specialization. -/
def modulePointUnitMap :
    moduleUnit X (ULift.{u + 1} (ZMod n)) ⟶
      (moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit Z (ULift.{u + 1} (ZMod n))) :=
  (moduleInverseImageAdjunction i (ULift.{u + 1} (ZMod n))).unit.app
      (moduleUnit X (ULift.{u + 1} (ZMod n))) ≫
    (moduleDirectImage i (ULift.{u + 1} (ZMod n))).map (moduleUnitInverseImageIso i n).hom

variable [HasExt.{wM} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X)]

/-- The actual support-forgetting map, defined by original point-unit
precomposition rather than assumed as a Gysin or purity comparison. -/
def modulePointExtToCohomology (q : ℕ) :
    Ext.{wM} ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit Z (ULift.{u + 1} (ZMod n)))) (moduleRootsOfUnity X n) q →+
      Sheaf.H.{wA} (mu X n) q :=
  (moduleRootsUnitExtCohomologyAddEquiv X n q).toAddMonoidHom.comp
    ((Ext.mk₀ (modulePointUnitMap i n)).precomp (moduleRootsOfUnity X n) (zero_add q))

/-- Evaluation retains the original point-unit precomposition and the
original module-unit/roots forward map. -/
theorem modulePointExtToCohomology_apply (q : ℕ)
    (e : Ext.{wM} ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
      (moduleUnit Z (ULift.{u + 1} (ZMod n)))) (moduleRootsOfUnity X n) q) :
    modulePointExtToCohomology i n q e =
      moduleRootsUnitExtCohomologyAddEquiv X n q
        ((Ext.mk₀ (modulePointUnitMap i n)).comp e (zero_add q)) := rfl

omit [HasExt.{wM} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X)] in
/-- The closed arrow of the ORIGINAL unit localization sequence becomes
the selected point-unit map through the original unit inverse-image iso. -/
theorem modulePointUnitMap_eq_localization_g
    {V : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    (hcomp : Set.range j = (Set.range i)ᶜ) :
    (moduleLocalizationShortComplex j (ULift.{u + 1} (ZMod n)) i hcomp
        (moduleUnit X (ULift.{u + 1} (ZMod n)))).g ≫
      (moduleDirectImage i (ULift.{u + 1} (ZMod n))).map (moduleUnitInverseImageIso i n).hom =
    modulePointUnitMap i n := rfl

omit [HasExt.{wA} (AbelianSheaf.{u, u + 1} X)] in
private theorem modulePointLocalization_subsingleton_zero_one
    (S : ShortComplex (ModuleSheaf X (ULift.{u + 1} (ZMod n)))) (hS : S.ShortExact)
    (Y : ModuleSheaf X (ULift.{u + 1} (ZMod n)))
    (h0 : Function.Bijective ((Ext.mk₀ S.f).precomp Y (zero_add 0)))
    (h1 : Function.Bijective ((Ext.mk₀ S.f).precomp Y (zero_add 1))) :
    Subsingleton (Ext.{wM} S.X₃ Y 0) ∧ Subsingleton (Ext.{wM} S.X₃ Y 1) := by
  have hfg (q : ℕ) (a : Ext.{wM} S.X₃ Y q) :
      (Ext.mk₀ S.f).comp ((Ext.mk₀ S.g).comp a (zero_add q)) (zero_add q) = 0 := by
    simp only [Ext.mk₀_comp_mk₀_assoc, S.zero, Ext.mk₀_zero, Ext.zero_comp]
  have : Epi S.g := hS.epi_g
  constructor
  · apply subsingleton_of_forall_eq 0
    intro a
    have hp : (Ext.mk₀ S.g).comp a (zero_add 0) = 0 :=
      h0.injective ((hfg 0 a).trans (map_zero ((Ext.mk₀ S.f).precomp Y (zero_add 0))).symm)
    exact (Ext.precomp_mk₀_injective_of_epi Y S.g)
      (hp.trans (map_zero ((Ext.mk₀ S.g).precomp Y (zero_add 0))).symm)
  · apply subsingleton_of_forall_eq 0
    intro a
    have hp : (Ext.mk₀ S.g).comp a (zero_add 1) = 0 :=
      h1.injective ((hfg 1 a).trans (map_zero ((Ext.mk₀ S.f).precomp Y (zero_add 1))).symm)
    obtain ⟨b, hb⟩ := Ext.contravariant_sequence_exact₃ hS Y a hp (n₀ := 0) (by decide)
    obtain ⟨c, hc⟩ := h0.surjective b
    have hz : hS.extClass.comp b (by decide : 1 + 0 = 1) = 0 := by
      change (Ext.mk₀ S.f).comp c (zero_add 0) = b at hc
      rw [← hc]
      exact hS.extClass_comp_assoc c
    exact hb.symm.trans hz

omit [HasExt.{wA} (AbelianSheaf.{u, u + 1} X)] in
private theorem modulePointLocalization_precomp_g_two_bijective
    (S : ShortComplex (ModuleSheaf X (ULift.{u + 1} (ZMod n)))) (hS : S.ShortExact)
    (Y : ModuleSheaf X (ULift.{u + 1} (ZMod n)))
    (h1 : Function.Surjective ((Ext.mk₀ S.f).precomp Y (zero_add 1)))
    [Subsingleton (Ext.{wM} S.X₁ Y 2)] :
    Function.Bijective ((Ext.mk₀ S.g).precomp Y (zero_add 2)) := by
  constructor
  · rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
    intro a ha
    obtain ⟨b, hb⟩ := Ext.contravariant_sequence_exact₃ hS Y a ha (n₀ := 1) (by decide)
    obtain ⟨c, hc⟩ := h1 b
    have hz : hS.extClass.comp b (by decide : 1 + 1 = 2) = 0 := by
      change (Ext.mk₀ S.f).comp c (zero_add 1) = b at hc
      rw [← hc]
      exact hS.extClass_comp_assoc c
    exact hb.symm.trans hz
  · intro a
    exact Ext.contravariant_sequence_exact₂ hS Y a (Subsingleton.elim _ _)

omit [HasExt.{wA} (AbelianSheaf.{u, u + 1} X)] in
private def modulePointOpenExtCohomologyAddEquiv
    {V : Scheme.{u}} (j : V ⟶ X) [Etale j] (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤)))
    [HasExt.{wMU} (ModuleSheaf V (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wAU} (AbelianSheaf.{u, u + 1} V)] (q : ℕ) :
    Ext.{wM} ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
        ((moduleInverseImage j (ULift.{u + 1} (ZMod n))).obj
          (moduleUnit X (ULift.{u + 1} (ZMod n))))) (moduleRootsOfUnity X n) q ≃+
      Sheaf.H.{wAU} (mu V n) q :=
  moduleLowerShriekRootsExtCohomologyAddEquiv (n := n) j hn hinv q

omit [HasExt.{wA} (AbelianSheaf.{u, u + 1} X)] in
private theorem modulePointOpenExtCohomologyAddEquiv_apply
    {V : Scheme.{u}} (j : V ⟶ X) [Etale j] (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤)))
    [HasExt.{wMU} (ModuleSheaf V (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wAU} (AbelianSheaf.{u, u + 1} V)] (q : ℕ)
    (e : Ext.{wM} ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
      ((moduleInverseImage j (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit X (ULift.{u + 1} (ZMod n))))) (moduleRootsOfUnity X n) q) :
    modulePointOpenExtCohomologyAddEquiv (n := n) j hn hinv q e =
      moduleRootsUnitExtCohomologyAddEquiv V n q
        (((Ext.mk₀ (moduleUnitInverseImageIso j n).inv).comp
          (moduleLowerShriekExtEquiv j (ULift.{u + 1} (ZMod n))
            ((moduleInverseImage j (ULift.{u + 1} (ZMod n))).obj
              (moduleUnit X (ULift.{u + 1} (ZMod n))))
            (moduleRootsOfUnity X n) q e) (zero_add q)).comp
          (Ext.mk₀ (moduleRootsOfUnityInverseImageIso j n hn hinv).hom) (add_zero q)) :=
  moduleLowerShriekRootsExtCohomologyAddEquiv_apply (n := n) j hn hinv q e

private theorem modulePointOpenExtCohomologyAddEquiv_counit
    {V : Scheme.{u}} (j : V ⟶ X) [Etale j] (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤)))
    [HasExt.{wMU} (ModuleSheaf V (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wAU} (AbelianSheaf.{u, u + 1} V)] (q : ℕ) :
    (modulePointOpenExtCohomologyAddEquiv (n := n) j hn hinv q).toAddMonoidHom.comp
      ((Ext.mk₀
        ((moduleLowerShriekAdjunction j (ULift.{u + 1} (ZMod n))).counit.app
          (moduleUnit X (ULift.{u + 1} (ZMod n))))).precomp
            (moduleRootsOfUnity X n) (zero_add q)) =
    (Kummer.rootsCohomologyPullback j n hn hinv q).comp
      (moduleRootsUnitExtCohomologyAddEquiv X n q).toAddMonoidHom :=
  moduleLowerShriekRootsExtCohomologyAddEquiv_counit (n := n) j hn hinv q

end PointMaps

private theorem modulePointOpenRestriction_bijective
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.OverField.FScheme k}
    (hC : Scheme.OverField.Curve.Properties C) (x : Scheme.ClosedPoint C.left)
    (V : C.left.Opens) (hV : (V : Set C.left) = {x.val}ᶜ)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(C.left, ⊤)))
    [HasExt.{wM} (ModuleSheaf C.left (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wA} (AbelianSheaf.{u, u + 1} C.left)]
    [HasExt.{wMU} (ModuleSheaf V.toScheme (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wAU} (AbelianSheaf.{u, u + 1} V.toScheme)] (q : ℕ) (hq : q ≤ 1) :
    Function.Bijective ((Ext.mk₀
      ((moduleLowerShriekAdjunction V.ι (ULift.{u + 1} (ZMod n))).counit.app
        (moduleUnit C.left (ULift.{u + 1} (ZMod n))))).precomp
          (moduleRootsOfUnity C.left n) (zero_add q)) := by
  let J := modulePointOpenExtCohomologyAddEquiv (n := n) V.ι hn hinv q
  let R := (Ext.mk₀
    ((moduleLowerShriekAdjunction V.ι (ULift.{u + 1} (ZMod n))).counit.app
      (moduleUnit C.left (ULift.{u + 1} (ZMod n))))).precomp
        (moduleRootsOfUnity C.left n) (zero_add q)
  let E := moduleRootsUnitExtCohomologyAddEquiv C.left n q
  let p := Kummer.rootsCohomologyPullback V.ι n hn hinv q
  have hwhole : J.toAddMonoidHom.comp R = p.comp E.toAddMonoidHom :=
    modulePointOpenExtCohomologyAddEquiv_counit (n := n) V.ι hn hinv q
  have hp : Function.Bijective p :=
    Curves.rootsCohomologyPullback_bijective_of_onePoint_of_le_one
      hC x V hV n hn hunit hinv q hq
  have hfunc : J ∘ R = p ∘ E := funext fun e => DFunLike.congr_fun hwhole e
  have hcomp : Function.Bijective (J ∘ R) := by
    rw [hfunc]
    exact hp.comp E.bijective
  exact hcomp.of_comp_left J.injective

private theorem modulePointExt_properties_of_range_singleton
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.OverField.FScheme k}
    (hC : Scheme.OverField.Curve.Properties C) (x : Scheme.ClosedPoint C.left)
    {Z : Scheme.{u}} (i : Z ⟶ C.left) [IsClosedImmersion i]
    (hi : Set.range i = {x.val}) (n : ℕ) (hn : 0 < n)
    (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(C.left, ⊤)))
    [HasExt.{wM} (ModuleSheaf C.left (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wA} (AbelianSheaf.{u, u + 1} C.left)] :
    Subsingleton (Ext.{wM}
        ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
          (moduleUnit Z (ULift.{u + 1} (ZMod n)))) (moduleRootsOfUnity C.left n) 0) ∧
      Subsingleton (Ext.{wM}
        ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
          (moduleUnit Z (ULift.{u + 1} (ZMod n)))) (moduleRootsOfUnity C.left n) 1) ∧
      Function.Bijective (modulePointExtToCohomology i n 2) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let V : C.left.Opens := ⟨{x.val}ᶜ, x.property.isOpen_compl⟩
  have hV : (V : Set C.left) = {x.val}ᶜ := rfl
  let : HasExt.{u + 2} (ModuleSheaf V.toScheme Λ) := SheafOfModules.hasExt (constantRing V Λ)
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} V.toScheme) := hasExtStandard V.toScheme
  have hcomp : Set.range V.ι = (Set.range i)ᶜ := by
    rw [Scheme.Opens.range_ι, hi]
    exact hV
  let S := moduleLocalizationShortComplex V.ι Λ i hcomp (moduleUnit C.left Λ)
  have hS : S.ShortExact := moduleLocalization_shortExact V.ι Λ i hcomp (moduleUnit C.left Λ)
  let Y := moduleRootsOfUnity C.left n
  have h0 : Function.Bijective ((Ext.mk₀ S.f).precomp Y (zero_add 0)) :=
    modulePointOpenRestriction_bijective hC x V hV n hn hunit hinv 0 (by decide)
  have h1 : Function.Bijective ((Ext.mk₀ S.f).precomp Y (zero_add 1)) :=
    modulePointOpenRestriction_bijective hC x V hV n hn hunit hinv 1 (by decide)
  have hv := modulePointLocalization_subsingleton_zero_one (n := n) S hS Y h0 h1
  have hx : ∃ z : C.left, IsClosed ({z} : Set C.left) ∧ z ∉ Set.range V.ι :=
    ⟨x.val, x.property, by rw [Scheme.Opens.range_ι, hV]; simp⟩
  have : Subsingleton (Sheaf.H.{u + 2} (mu V.toScheme n) 2) :=
    Curves.roots_subsingleton_H_two_of_isOpenImmersion hC V.ι hx n hunit
  have : Subsingleton (Ext.{wM} S.X₁ Y 2) :=
    (modulePointOpenExtCohomologyAddEquiv (n := n) V.ι hn hinv 2).injective.subsingleton
  have hg : Function.Bijective ((Ext.mk₀ S.g).precomp Y (zero_add 2)) :=
    modulePointLocalization_precomp_g_two_bijective (n := n) S hS Y h1.surjective
  let e₃ : S.X₃ ≅ (moduleDirectImage i Λ).obj (moduleUnit Z Λ) :=
    (moduleDirectImage i Λ).mapIso (moduleUnitInverseImageIso i n)
  let E (q : ℕ) : Ext.{wM} ((moduleDirectImage i Λ).obj (moduleUnit Z Λ)) Y q ≃+
      Ext.{wM} S.X₃ Y q :=
    (((CategoryTheory.Abelian.extFunctor q).mapIso e₃.op).app Y).addCommGroupIsoToAddEquiv
  have hβ : modulePointUnitMap i n = S.g ≫ e₃.hom :=
    (modulePointUnitMap_eq_localization_g i n V.ι hcomp).symm
  have hpre : Function.Bijective ((Ext.mk₀ (modulePointUnitMap i n)).precomp Y (zero_add 2)) := by
    have hwhole : (Ext.mk₀ (modulePointUnitMap i n)).precomp Y (zero_add 2) =
        ((Ext.mk₀ S.g).precomp Y (zero_add 2)).comp (E 2).toAddMonoidHom := by
      ext e
      change (Ext.mk₀ (modulePointUnitMap i n)).comp e (zero_add 2) =
        (Ext.mk₀ S.g).comp ((Ext.mk₀ e₃.hom).comp e (zero_add 2)) (zero_add 2)
      rw [hβ, Ext.mk₀_comp_mk₀_assoc]
      rfl
    rw [hwhole]
    exact hg.comp (E 2).bijective
  have hpoint0 : Subsingleton
      (Ext.{wM} ((moduleDirectImage i Λ).obj (moduleUnit Z Λ)) Y 0) := by
    let := hv.1
    exact (E 0).injective.subsingleton
  have hpoint1 : Subsingleton
      (Ext.{wM} ((moduleDirectImage i Λ).obj (moduleUnit Z Λ)) Y 1) := by
    let := hv.2
    exact (E 1).injective.subsingleton
  exact ⟨hpoint0, hpoint1,
    (moduleRootsUnitExtCohomologyAddEquiv C.left n 2).bijective.comp hpre⟩

section ProperPoint

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.OverField.FScheme k}
  (hC : Scheme.OverField.Curve.Properties C) (x : Scheme.ClosedPoint C.left)
  {Z : Scheme.{u}} (i : Z ⟶ C.left) [IsClosedImmersion i]
  (hi : Set.range i = {x.val}) (n : ℕ) (hn : 0 < n)
  (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(C.left, ⊤)))
  [HasExt.{wM} (ModuleSheaf C.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} C.left)]

include hC x hi hn hunit hinv

/-- Degree-zero Ext from the actual closed-point unit coefficient to roots
vanishes among the original module sheaves. -/
theorem modulePointExt_zero_subsingleton :
    Subsingleton (Ext.{wM} ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
      (moduleUnit Z (ULift.{u + 1} (ZMod n)))) (moduleRootsOfUnity C.left n) 0) :=
  (modulePointExt_properties_of_range_singleton hC x i hi n hn hunit hinv).1

/-- Degree-one Ext from the actual closed-point unit coefficient to roots
vanishes among the original module sheaves. -/
theorem modulePointExt_one_subsingleton :
    Subsingleton (Ext.{wM} ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
      (moduleUnit Z (ULift.{u + 1} (ZMod n)))) (moduleRootsOfUnity C.left n) 1) :=
  (modulePointExt_properties_of_range_singleton hC x i hi n hn hunit hinv).2.1

/-- The actual point-unit precomposition is a bijection in degree two on
the proper curve, before taking the original trace. -/
theorem modulePointExtToCohomology_two_bijective :
    Function.Bijective (modulePointExtToCohomology i n 2) :=
  (modulePointExt_properties_of_range_singleton hC x i hi n hn hunit hinv).2.2

/-- The original degree-two supported module Ext is identified with Z/n
by actual point-unit precomposition followed by the original proper trace. -/
def modulePointPurityAddEquiv :
    Ext.{wM} ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit Z (ULift.{u + 1} (ZMod n)))) (moduleRootsOfUnity C.left n) 2 ≃+ ZMod n :=
  (AddEquiv.ofBijective (modulePointExtToCohomology i n 2)
    (modulePointExtToCohomology_two_bijective hC x i hi n hn hunit hinv)).trans
      (Curves.traceAddEquiv hC n hn hunit hinv)

/-- The supported point class is the unique inverse image of the ORIGINAL
Kummer boundary of the ORIGINAL positive point line bundle. -/
def modulePointPurityClass :
    Ext.{wM} ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
      (moduleUnit Z (ULift.{u + 1} (ZMod n)))) (moduleRootsOfUnity C.left n) 2 :=
  (AddEquiv.ofBijective (modulePointExtToCohomology i n 2)
    (modulePointExtToCohomology_two_bijective hC x i hi n hn hunit hinv)).symm
      (Kummer.picardBoundary C.left n hn hinv
        (Scheme.OverField.Curve.Picard.OnePointRestriction.closedPointClass hC x))

/-- The whole point-unit image of the supported class is the actual
global Kummer point boundary, fixing the chosen normalization. -/
theorem modulePointPurityClass_image :
    modulePointExtToCohomology i n 2
        (modulePointPurityClass hC x i hi n hn hunit hinv) =
      Kummer.picardBoundary C.left n hn hinv
        (Scheme.OverField.Curve.Picard.OnePointRestriction.closedPointClass hC x) :=
  (AddEquiv.ofBijective (modulePointExtToCohomology i n 2)
    (modulePointExtToCohomology_two_bijective hC x i hi n hn hunit hinv)).apply_symm_apply _

/-- The actual supported point class has trace one, with the original
Kummer boundary convention and no external generator identification. -/
theorem modulePointPurityAddEquiv_pointClass :
    modulePointPurityAddEquiv hC x i hi n hn hunit hinv
      (modulePointPurityClass hC x i hi n hn hunit hinv) = 1 := by
  change Curves.traceAddEquiv hC n hn hunit hinv
    (modulePointExtToCohomology i n 2
      (modulePointPurityClass hC x i hi n hn hunit hinv)) = 1
  rw [modulePointPurityClass_image]
  exact Curves.traceAddEquiv_picardBoundary_closedPoint hC n hn hunit hinv x.val x.property

end ProperPoint

/-- Higher supported Ext vanishes by the ORIGINAL localization sequence,
ordinary open-curve vanishing in degree at least two, and ordinary proper
curve vanishing above degree two. No supported-point purity input is used. -/
theorem modulePointExt_high_subsingleton
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.OverField.FScheme k}
    (hC : Scheme.OverField.Curve.Properties C) (x : Scheme.ClosedPoint C.left)
    {Z : Scheme.{u}} (i : Z ⟶ C.left) [IsClosedImmersion i]
    (hi : Set.range i = {x.val}) (n : ℕ) (hn : 0 < n)
    (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(C.left, ⊤)))
    [HasExt.{wM} (ModuleSheaf C.left (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wA} (AbelianSheaf.{u, u + 1} C.left)] (q : ℕ) (hq : 2 < q) :
    Subsingleton (Ext.{wM} ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
      (moduleUnit Z (ULift.{u + 1} (ZMod n)))) (moduleRootsOfUnity C.left n) q) := by
  cases q with
  | zero => omega
  | succ r =>
    let Λ := ULift.{u + 1} (ZMod n)
    let V : C.left.Opens := ⟨{x.val}ᶜ, x.property.isOpen_compl⟩
    let : HasExt.{u + 2} (ModuleSheaf V.toScheme Λ) :=
      SheafOfModules.hasExt (constantRing V Λ)
    let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} V.toScheme) := hasExtStandard V.toScheme
    have hcomp : Set.range V.ι = (Set.range i)ᶜ := by
      rw [Scheme.Opens.range_ι, hi]
      rfl
    let S := moduleLocalizationShortComplex V.ι Λ i hcomp (moduleUnit C.left Λ)
    have hS : S.ShortExact :=
      moduleLocalization_shortExact V.ι Λ i hcomp (moduleUnit C.left Λ)
    let Y := moduleRootsOfUnity C.left n
    have hx : ∃ z : C.left, IsClosed ({z} : Set C.left) ∧ z ∉ Set.range V.ι :=
      ⟨x.val, x.property, by rw [Scheme.Opens.range_ι]; simp [V]⟩
    have : Subsingleton (Sheaf.H.{u + 2} (mu V.toScheme n) r) :=
      Curves.roots_subsingleton_H_of_isOpenImmersion hC V.ι hx n hunit r (by omega)
    have : Subsingleton (Ext.{wM} S.X₁ Y r) :=
      (modulePointOpenExtCohomologyAddEquiv (n := n) V.ι hn hinv r).injective.subsingleton
    have := Scheme.OverField.Curve.curveProperties_locallyOfFiniteType hC
    have := hC.proper
    have : CompactSpace C.left := QuasiCompact.compactSpace_of_compactSpace C.hom
    have : Subsingleton (Sheaf.H.{wA} (mu C.left n) (r + 1)) :=
      Curves.roots_subsingleton_H_of_curve k C.left C.hom hC.topologicalKrullDim_eq_one.le
        n hn hunit hinv (r + 1) hq
    have : Subsingleton (Ext.{wM} S.X₂ Y (r + 1)) :=
      (moduleRootsUnitExtCohomologyAddEquiv C.left n (r + 1)).injective.subsingleton
    have : Subsingleton (Ext.{wM} S.X₃ Y (r + 1)) := by
      apply subsingleton_of_forall_eq 0
      intro e
      obtain ⟨b, hb⟩ := Ext.contravariant_sequence_exact₃ hS Y e
        (Subsingleton.elim _ _) (n₀ := r) (by omega)
      exact hb.symm.trans (by rw [Subsingleton.elim b 0, Ext.comp_zero])
    let e₃ : S.X₃ ≅ (moduleDirectImage i Λ).obj (moduleUnit Z Λ) :=
      (moduleDirectImage i Λ).mapIso (moduleUnitInverseImageIso i n)
    let E : Ext.{wM} ((moduleDirectImage i Λ).obj (moduleUnit Z Λ)) Y (r + 1) ≃+
        Ext.{wM} S.X₃ Y (r + 1) :=
      (((CategoryTheory.Abelian.extFunctor (r + 1)).mapIso e₃.op).app Y)
        |>.addCommGroupIsoToAddEquiv
    exact E.injective.subsingleton

section PointExcision

variable {Z U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (i : Z ⟶ U) [IsClosedImmersion (i ≫ j)] (n : ℕ)

/-- The original closed-support lower-shriek/direct-image iso lifted to the
actual point-unit modules through full constant-Z/n forgetting. -/
def modulePointLowerShriekDirectImageIso :
    (moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
        ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
          (moduleUnit Z (ULift.{u + 1} (ZMod n)))) ≅
      (moduleDirectImage (i ≫ j) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit Z (ULift.{u + 1} (ZMod n))) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let M := moduleUnit Z Λ
  let Q := SheafOfModules.toSheaf (constantRing X Λ)
  let := moduleSheaf_uLiftZMod_toSheaf_full X n
  exact Q.preimageIso
    ((moduleLowerShriekUnderlyingIso j Λ).app ((moduleDirectImage i Λ).obj M) ≪≫
      (etaleLowerShriek j).mapIso ((moduleDirectImageUnderlyingIso i Λ).app M) ≪≫
        (etaleLowerShriekDirectImageIso j i).app
          ((SheafOfModules.toSheaf (constantRing Z Λ)).obj M) ≪≫
            ((moduleDirectImageUnderlyingIso (i ≫ j) Λ).app M).symm)

/-- Underlying the module iso is the EXISTING closed-support abelian iso,
with the original module lower-shriek and direct-image comparisons. -/
theorem modulePointLowerShriekDirectImageIso_underlying :
    (SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).map
        (modulePointLowerShriekDirectImageIso j i n).hom =
      (moduleLowerShriekUnderlyingIso j (ULift.{u + 1} (ZMod n))).hom.app
          ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
            (moduleUnit Z (ULift.{u + 1} (ZMod n)))) ≫
        (etaleLowerShriek j).map
          ((moduleDirectImageUnderlyingIso i (ULift.{u + 1} (ZMod n))).hom.app
            (moduleUnit Z (ULift.{u + 1} (ZMod n)))) ≫
          (etaleLowerShriekDirectImageIso j i).hom.app
            ((SheafOfModules.toSheaf (constantRing Z (ULift.{u + 1} (ZMod n)))).obj
              (moduleUnit Z (ULift.{u + 1} (ZMod n)))) ≫
            (moduleDirectImageUnderlyingIso (i ≫ j) (ULift.{u + 1} (ZMod n))).inv.app
              (moduleUnit Z (ULift.{u + 1} (ZMod n))) := by
  let := moduleSheaf_uLiftZMod_toSheaf_full X n
  rw [modulePointLowerShriekDirectImageIso, Functor.preimageIso_hom, Functor.map_preimage]
  rfl

variable (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
  [HasExt.{wM} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wMU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]

/-- Closed-support excision on the ORIGINAL point-unit Ext, through the
existing closed-support lower-shriek/direct-image iso and the open adjunction.
The Ext universes on the two schemes remain independent. -/
def modulePointExtExcisionAddEquiv (q : ℕ) :
    Ext.{wM} ((moduleDirectImage (i ≫ j) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit Z (ULift.{u + 1} (ZMod n)))) (moduleRootsOfUnity X n) q ≃+
      Ext.{wMU} ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit Z (ULift.{u + 1} (ZMod n)))) (moduleRootsOfUnity U n) q := by
  let Λ := ULift.{u + 1} (ZMod n)
  let M := (moduleDirectImage i Λ).obj (moduleUnit Z Λ)
  let e := modulePointLowerShriekDirectImageIso j i n
  let pre : Ext.{wM} ((moduleDirectImage (i ≫ j) Λ).obj (moduleUnit Z Λ))
        (moduleRootsOfUnity X n) q ≃+
      Ext.{wM} ((moduleLowerShriek j Λ).obj M) (moduleRootsOfUnity X n) q :=
    (((CategoryTheory.Abelian.extFunctor q).mapIso e.op).app
      (moduleRootsOfUnity X n)).addCommGroupIsoToAddEquiv
  let post : Ext.{wMU} M
        ((moduleInverseImage j Λ).obj (moduleRootsOfUnity X n)) q ≃+
      Ext.{wMU} M (moduleRootsOfUnity U n) q :=
    ((CategoryTheory.Abelian.extFunctorObj M q).mapIso
      (moduleRootsOfUnityInverseImageIso j n hn hinv)).addCommGroupIsoToAddEquiv
  exact pre.trans ((moduleLowerShriekExtEquiv j Λ M (moduleRootsOfUnity X n) q).trans post)

/-- Evaluation keeps the original closed-support iso, open Ext adjunction
and selected roots inverse-image map. -/
theorem modulePointExtExcisionAddEquiv_apply (q : ℕ)
    (e : Ext.{wM} ((moduleDirectImage (i ≫ j) (ULift.{u + 1} (ZMod n))).obj
      (moduleUnit Z (ULift.{u + 1} (ZMod n)))) (moduleRootsOfUnity X n) q) :
    modulePointExtExcisionAddEquiv j i n hn hinv q e =
      (moduleLowerShriekExtEquiv j (ULift.{u + 1} (ZMod n))
        ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
          (moduleUnit Z (ULift.{u + 1} (ZMod n)))) (moduleRootsOfUnity X n) q
        ((Ext.mk₀ (modulePointLowerShriekDirectImageIso j i n).hom).comp e (zero_add q))).comp
          (Ext.mk₀ (moduleRootsOfUnityInverseImageIso j n hn hinv).hom) (add_zero q) := rfl

end PointExcision

/-- The image in the proper curve of a closed point of an open subcurve is
closed. The rational-point argument is internal to this geometric proof. -/
theorem modulePoint_image_isClosed
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.OverField.FScheme k}
    (hC : Scheme.OverField.Curve.Properties C) {U : Scheme.{u}}
    (j : U ⟶ C.left) [IsOpenImmersion j] (x : Scheme.ClosedPoint U) :
    IsClosed ({j x.val} : Set C.left) := by
  have := Scheme.OverField.Curve.curveProperties_locallyOfFiniteType hC
  have : LocallyOfFiniteType (j ≫ C.hom) := inferInstance
  let p := pointOfClosedPoint (j ≫ C.hom) x.val x.property
  have hp : p ≫ (j ≫ C.hom) = 𝟙 _ := pointOfClosedPoint_comp (j ≫ C.hom) x.val x.property
  have hpC : (p ≫ j) ≫ C.hom = 𝟙 _ := by rw [Category.assoc]; exact hp
  have hc : IsClosed ({(p ≫ j) (IsLocalRing.closedPoint k)} : Set C.left) :=
    (pointEquivClosedPoint C.hom ⟨p ≫ j, hpC⟩).2
  have hvalue : (p ≫ j) (IsLocalRing.closedPoint k) = j x.val := by
    change j (p (IsLocalRing.closedPoint k)) = j x.val
    exact congrArg j (pointOfClosedPoint_apply (j ≫ C.hom) x.val x.property _)
  rw [hvalue] at hc
  exact hc

/-- The canonical residue-field point of the open subcurve remains a closed
immersion when composed with its given map to the proper curve. -/
theorem modulePoint_composite_isClosedImmersion
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.OverField.FScheme k}
    (hC : Scheme.OverField.Curve.Properties C) {U : Scheme.{u}}
    (j : U ⟶ C.left) [IsOpenImmersion j] (x : Scheme.ClosedPoint U) :
    IsClosedImmersion (U.fromSpecResidueField x.val ≫ j) := by
  have : IsClosedImmersion (U.fromSpecResidueField x.val) :=
    isClosed_singleton_iff_isClosedImmersion.mp x.property
  have : IsImmersion (U.fromSpecResidueField x.val ≫ j) := inferInstance
  have hrange : Set.range (U.fromSpecResidueField x.val ≫ j) = {j x.val} := by
    change Set.range (j ∘ U.fromSpecResidueField x.val) = {j x.val}
    rw [Set.range_comp, Scheme.range_fromSpecResidueField, Set.image_singleton]
  apply IsClosedImmersion.of_isPreimmersion
  rw [hrange]
  exact modulePoint_image_isClosed hC j x

/-- Field invertibility supplies the actual global-section invertibility
used by the original Kummer operators. -/
theorem modulePoint_globalLevelInvertible
    {k : Type u} [Field k] {C : Scheme.OverField.FScheme k}
    (n : ℕ) (hunit : IsUnit (n : k)) : IsUnit (n : Γ(C.left, ⊤)) := by
  have hk : IsUnit (n : Γ(Spec (.of k), ⊤)) := by
    simpa only [map_natCast] using hunit.map (Scheme.ΓSpecIso (.of k)).inv.hom
  exact GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible C.hom n hk

/-- The original composed residue-field point map has its literal singleton
range, without selecting a second residue-field point model. -/
theorem modulePoint_composite_range
    {U X : Scheme.{u}} (j : U ⟶ X) (x : Scheme.ClosedPoint U) :
    Set.range (U.fromSpecResidueField x.val ≫ j) = {j x.val} := by
  change Set.range (j ∘ U.fromSpecResidueField x.val) = {j x.val}
  rw [Set.range_comp, Scheme.range_fromSpecResidueField, Set.image_singleton]

section OpenPoint

-- Only the auxiliary proper-curve Ext and cohomology use the standard
-- existing size. The original supported Ext on U retains its arbitrary size.
local instance (T : Scheme.{u}) (n : ℕ) :
    HasExt.{u + 2} (ModuleSheaf T (ULift.{u + 1} (ZMod n))) :=
  SheafOfModules.hasExt (constantRing T (ULift.{u + 1} (ZMod n)))

attribute [local instance] hasExtStandard

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.OverField.FScheme k}
  (hC : Scheme.OverField.Curve.Properties C) {U : Scheme.{u}}
  (j : U ⟶ C.left) [IsOpenImmersion j] (x : Scheme.ClosedPoint U)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  [HasExt.{wMU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]

include hC j x hn hunit

/-- The original support-forgetting map for the canonical residue-field
point in U, transported to the given proper completion through CLOSED-support
excision. The same Spec κ(x) and composed point map are used throughout. -/
def moduleOpenPointExtToCohomology (q : ℕ) :
    Ext.{wMU}
        ((moduleDirectImage (U.fromSpecResidueField x.val)
          (ULift.{u + 1} (ZMod n))).obj
            (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n))))
        (moduleRootsOfUnity U n) q →+
      Sheaf.H.{u + 2} (mu C.left n) q := by
  let i := U.fromSpecResidueField x.val
  let : IsClosedImmersion (i ≫ j) := modulePoint_composite_isClosedImmersion hC j x
  let e : Ext.{u + 2} ((moduleDirectImage (i ≫ j) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n))))
        (moduleRootsOfUnity C.left n) q ≃+
      Ext.{wMU} ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n))))
        (moduleRootsOfUnity U n) q :=
    modulePointExtExcisionAddEquiv j i n hn (modulePoint_globalLevelInvertible n hunit) q
  exact (modulePointExtToCohomology (i ≫ j) n q).comp e.symm.toAddMonoidHom

/-- Original degree-zero supported module Ext vanishes for the canonical
residue-field point of any given open subcurve. -/
theorem moduleOpenPointExt_zero_subsingleton :
    Subsingleton (Ext.{wMU}
      ((moduleDirectImage (U.fromSpecResidueField x.val)
        (ULift.{u + 1} (ZMod n))).obj
          (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n))))
      (moduleRootsOfUnity U n) 0) := by
  let i := U.fromSpecResidueField x.val
  let : IsClosedImmersion (i ≫ j) := modulePoint_composite_isClosedImmersion hC j x
  let z : Scheme.ClosedPoint C.left := ⟨j x.val, modulePoint_image_isClosed hC j x⟩
  have : Subsingleton (Ext.{u + 2}
      ((moduleDirectImage (i ≫ j) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n))))
      (moduleRootsOfUnity C.left n) 0) :=
    modulePointExt_zero_subsingleton hC z (i ≫ j) (modulePoint_composite_range j x)
      n hn hunit (modulePoint_globalLevelInvertible n hunit)
  exact (modulePointExtExcisionAddEquiv j i n hn
    (modulePoint_globalLevelInvertible n hunit) 0).symm.injective.subsingleton

/-- Original degree-one supported module Ext vanishes for the canonical
residue-field point of any given open subcurve. -/
theorem moduleOpenPointExt_one_subsingleton :
    Subsingleton (Ext.{wMU}
      ((moduleDirectImage (U.fromSpecResidueField x.val)
        (ULift.{u + 1} (ZMod n))).obj
          (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n))))
      (moduleRootsOfUnity U n) 1) := by
  let i := U.fromSpecResidueField x.val
  let : IsClosedImmersion (i ≫ j) := modulePoint_composite_isClosedImmersion hC j x
  let z : Scheme.ClosedPoint C.left := ⟨j x.val, modulePoint_image_isClosed hC j x⟩
  have : Subsingleton (Ext.{u + 2}
      ((moduleDirectImage (i ≫ j) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n))))
      (moduleRootsOfUnity C.left n) 1) :=
    modulePointExt_one_subsingleton hC z (i ≫ j) (modulePoint_composite_range j x)
      n hn hunit (modulePoint_globalLevelInvertible n hunit)
  exact (modulePointExtExcisionAddEquiv j i n hn
    (modulePoint_globalLevelInvertible n hunit) 1).symm.injective.subsingleton

/-- The actual supported degree-two Ext maps bijectively to ordinary roots
cohomology of the specified proper completion. -/
theorem moduleOpenPointExtToCohomology_two_bijective :
    Function.Bijective (moduleOpenPointExtToCohomology hC j x n hn hunit 2) := by
  let i := U.fromSpecResidueField x.val
  let : IsClosedImmersion (i ≫ j) := modulePoint_composite_isClosedImmersion hC j x
  let z : Scheme.ClosedPoint C.left := ⟨j x.val, modulePoint_image_isClosed hC j x⟩
  exact (modulePointExtToCohomology_two_bijective hC z (i ≫ j)
    (modulePoint_composite_range j x) n hn hunit
      (modulePoint_globalLevelInvertible n hunit)).comp
        (modulePointExtExcisionAddEquiv j i n hn
          (modulePoint_globalLevelInvertible n hunit) 2).symm.bijective

/-- Point purity for the ORIGINAL module Ext on the given open subcurve,
normalized by the original proper-curve roots trace. -/
def moduleOpenPointPurityAddEquiv :
    Ext.{wMU}
      ((moduleDirectImage (U.fromSpecResidueField x.val)
        (ULift.{u + 1} (ZMod n))).obj
          (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n))))
      (moduleRootsOfUnity U n) 2 ≃+ ZMod n :=
  (AddEquiv.ofBijective (moduleOpenPointExtToCohomology hC j x n hn hunit 2)
    (moduleOpenPointExtToCohomology_two_bijective hC j x n hn hunit)).trans
      (Curves.traceAddEquiv hC n hn hunit (modulePoint_globalLevelInvertible n hunit))

/-- The supported point class is the unique class whose actual proper
support-forgetting image is the ORIGINAL Kummer boundary of O(j(x)). -/
def moduleOpenPointPurityClass :
    Ext.{wMU}
      ((moduleDirectImage (U.fromSpecResidueField x.val)
        (ULift.{u + 1} (ZMod n))).obj
          (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n))))
      (moduleRootsOfUnity U n) 2 :=
  (AddEquiv.ofBijective (moduleOpenPointExtToCohomology hC j x n hn hunit 2)
    (moduleOpenPointExtToCohomology_two_bijective hC j x n hn hunit)).symm
      (Kummer.picardBoundary C.left n hn (modulePoint_globalLevelInvertible n hunit)
        (Scheme.OverField.Curve.Picard.OnePointRestriction.closedPointClass hC
          ⟨j x.val, modulePoint_image_isClosed hC j x⟩))

/-- The original Kummer point boundary fixes the whole chosen point-class
normalization, before evaluation by trace. -/
theorem moduleOpenPointPurityClass_image :
    moduleOpenPointExtToCohomology hC j x n hn hunit 2
        (moduleOpenPointPurityClass hC j x n hn hunit) =
      Kummer.picardBoundary C.left n hn (modulePoint_globalLevelInvertible n hunit)
        (Scheme.OverField.Curve.Picard.OnePointRestriction.closedPointClass hC
          ⟨j x.val, modulePoint_image_isClosed hC j x⟩) :=
  (AddEquiv.ofBijective (moduleOpenPointExtToCohomology hC j x n hn hunit 2)
    (moduleOpenPointExtToCohomology_two_bijective hC j x n hn hunit)).apply_symm_apply _

/-- The canonical supported point class has original trace one. -/
theorem moduleOpenPointPurityAddEquiv_pointClass :
    moduleOpenPointPurityAddEquiv hC j x n hn hunit
      (moduleOpenPointPurityClass hC j x n hn hunit) = 1 := by
  change Curves.traceAddEquiv hC n hn hunit (modulePoint_globalLevelInvertible n hunit)
    (moduleOpenPointExtToCohomology hC j x n hn hunit 2
      (moduleOpenPointPurityClass hC j x n hn hunit)) = 1
  rw [moduleOpenPointPurityClass_image]
  exact Curves.traceAddEquiv_picardBoundary_closedPoint hC n hn hunit
    (modulePoint_globalLevelInvertible n hunit) (j x.val) (modulePoint_image_isClosed hC j x)

/-- All original supported module Ext above degree two vanishes. The
comparison uses only closed-support excision and ordinary curve vanishing. -/
theorem moduleOpenPointExt_high_subsingleton (q : ℕ) (hq : 2 < q) :
    Subsingleton (Ext.{wMU}
      ((moduleDirectImage (U.fromSpecResidueField x.val)
        (ULift.{u + 1} (ZMod n))).obj
          (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n))))
      (moduleRootsOfUnity U n) q) := by
  let i := U.fromSpecResidueField x.val
  let : IsClosedImmersion (i ≫ j) := modulePoint_composite_isClosedImmersion hC j x
  let z : Scheme.ClosedPoint C.left := ⟨j x.val, modulePoint_image_isClosed hC j x⟩
  have : Subsingleton (Ext.{u + 2}
      ((moduleDirectImage (i ≫ j) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n))))
      (moduleRootsOfUnity C.left n) q) :=
    modulePointExt_high_subsingleton hC z (i ≫ j) (modulePoint_composite_range j x)
      n hn hunit (modulePoint_globalLevelInvertible n hunit) q hq
  exact (modulePointExtExcisionAddEquiv j i n hn
    (modulePoint_globalLevelInvertible n hunit) q).symm.injective.subsingleton

end OpenPoint

end AlgebraicGeometry.Scheme.EtaleCohomology
