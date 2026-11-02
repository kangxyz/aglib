/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.PointPurity.Finite
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.LowerShriekCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.Rank
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Algebra.Exact.Basic

/-!
# Cardinality of original H1 on an open curve

The original unit localization sequence and the finite point-purity sum map
compute the cardinality of roots H1 on a given open complement of a finite
nonempty set of closed points of a smooth proper geometrically connected
curve over an algebraically closed field. Only positive levels invertible in
the field are used. Constants use the original constant-root isomorphism.
No splitting, coordinates or basis of the open cohomology group is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients

universe u wM wMU wA wAU

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- The actual direct-image unit iso gives the closed-source Ext comparison.
Its source and forward map are the original inverse-image unit source and
precomposition by the inverse of the selected native unit iso. -/
def moduleClosedUnitExtAddEquiv
    {Z X : Scheme.{u}} (i : Z ⟶ X) (n : ℕ)
    [HasExt.{wM} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
    (N : ModuleSheaf X (ULift.{u + 1} (ZMod n))) (q : ℕ) :
    Ext.{wM} ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
      ((moduleInverseImage i (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit X (ULift.{u + 1} (ZMod n))))) N q ≃+
      Ext.{wM} ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit Z (ULift.{u + 1} (ZMod n)))) N q :=
  (((extFunctor q).mapIso
    ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).mapIso
      (moduleUnitInverseImageIso i n)).symm.op).app N).addCommGroupIsoToAddEquiv

private theorem ext_precomp_sourceIso_square
    {A : Type*} [Category A] [Abelian A] [HasExt.{wM} A]
    {X Y Z : A} (g : X ⟶ Y) (a : Y ≅ Z) (p : X ⟶ Z)
    (hp : g ≫ a.hom = p) (N : A) :
    ((Ext.mk₀ p).precomp N (zero_add 2)).comp
      ((((extFunctor 2).mapIso a.symm.op).app N).addCommGroupIsoToAddEquiv).toAddMonoidHom =
        (Ext.mk₀ g).precomp N (zero_add 2) := by
  rw [← hp]
  refine AddMonoidHom.ext (fun (e : Ext.{wM} Y N 2) => ?_)
  change (Ext.mk₀ (g ≫ a.hom)).comp
    ((Ext.mk₀ a.inv).comp e (zero_add 2)) (zero_add 2) =
      (Ext.mk₀ g).comp e (zero_add 2)
  rw [Ext.mk₀_comp_mk₀_assoc, Category.assoc, a.hom_inv_id, Category.comp_id]

private theorem moduleClosedUnitExtAddEquiv_precomp
    {Z X : Scheme.{u}} (i : Z ⟶ X) (n : ℕ)
    [HasExt.{wM} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
    (N : ModuleSheaf X (ULift.{u + 1} (ZMod n))) :
    ((Ext.mk₀ (modulePointUnitMap i n)).precomp N (zero_add 2)).comp
      (moduleClosedUnitExtAddEquiv i n N 2).toAddMonoidHom =
    (Ext.mk₀ ((moduleInverseImageAdjunction i (ULift.{u + 1} (ZMod n))).unit.app
      (moduleUnit X (ULift.{u + 1} (ZMod n))))).precomp N (zero_add 2) := by
  exact ext_precomp_sourceIso_square
    ((moduleInverseImageAdjunction i (ULift.{u + 1} (ZMod n))).unit.app
      (moduleUnit X (ULift.{u + 1} (ZMod n))))
    ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).mapIso
      (moduleUnitInverseImageIso i n))
    (modulePointUnitMap i n) rfl N

private theorem addEquiv_conjugate_comp
    {A B T V : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup T] [AddCommGroup V]
    (E : A ≃+ B) (G : T ≃+ V) (d : A →+ T) :
    (G.toAddMonoidHom.comp (d.comp E.symm.toAddMonoidHom)).comp E.toAddMonoidHom =
      G.toAddMonoidHom.comp d := by
  ext a
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.symm_apply_apply]

namespace Curves

open Scheme.OverField Scheme.OverField.Curve FiniteClosedSupport

private theorem card_eq_mul_card_range_of_exact
    {A B T : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup T]
    (f : A →+ B) (g : B →+ T) (hf : Function.Injective f) (h : Function.Exact f g) :
    Nat.card B = Nat.card A * Nat.card g.range := by
  have hr : f.range = g.ker := by
    ext b
    change (∃ a, f a = b) ↔ g b = 0
    exact (h b).symm
  have ha : Nat.card f.range = Nat.card A :=
    (Nat.card_congr (Equiv.ofInjective f hf)).symm
  calc
    Nat.card B = Nat.card (B ⧸ g.ker) * Nat.card g.ker :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker
    _ = Nat.card g.range * Nat.card f.range := by
      rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv, ← hr]
    _ = Nat.card A * Nat.card g.range := by rw [ha, mul_comm]

private theorem card_sum_kernel (ι : Type*) [Fintype ι] [Nonempty ι]
    (n : ℕ) (hn : 0 < n) :
    Nat.card ((∑ x : ι, Pi.evalAddMonoidHom (fun _ : ι => ZMod n) x).ker) =
      n ^ (Nat.card ι - 1) := by
  classical
  let s : (ι → ZMod n) →+ ZMod n :=
    ∑ x : ι, Pi.evalAddMonoidHom (fun _ : ι => ZMod n) x
  have hs : Function.Surjective s := by
    intro a
    obtain ⟨d⟩ := ‹Nonempty ι›
    refine ⟨fun x => if x = d then a else 0, ?_⟩
    simp [s]
  have hc := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup s.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective s hs).toEquiv] at hc
  simp only [Nat.card_fun, Nat.card_zmod] at hc
  have hi : 0 < Nat.card ι := Nat.card_pos
  change Nat.card s.ker = _
  apply Nat.eq_of_mul_eq_mul_left hn
  calc
    n * Nat.card s.ker = n ^ Nat.card ι := hc.symm
    _ = n ^ ((Nat.card ι - 1) + 1) := congrArg (n ^ ·) (by omega)
    _ = n * n ^ (Nat.card ι - 1) := pow_succ' _ _

section OpenBoundary

variable {k : Type u} [Field k] [IsAlgClosed k] {C : FScheme k}
  (hC : Curve.Properties C) (D : Set C.left) [Finite D]
  (hclosed : ∀ x ∈ D, IsClosed ({x} : Set C.left))
  {U : Scheme.{u}} (j : U ⟶ C.left) [IsOpenImmersion j]
  (hD : Set.range j = Dᶜ) (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  [HasExt.{wM} (ModuleSheaf C.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wMU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} C.left)]
  [HasExt.{wAU} (AbelianSheaf.{u, u + 1} U)]

/-- The finite enumeration used for sums over the original support. -/
local instance openRankFintype : Fintype D := Fintype.ofFinite D

/-- The original unsigned localization boundary on roots H1, followed by
precomposition through the actual closed unit iso and the finite point-purity map. -/
def rootsOneLocalizationBoundary : Sheaf.H.{wAU} (mu U n) 1 →+ (D → ZMod n) := by
  let i := inclusion C.left D
  let : IsClosedImmersion i :=
    inclusion_isClosedImmersion C.left D (Set.toFinite D) hclosed
  let hcomp : Set.range j = (Set.range i)ᶜ := by
    simpa only [i, range_inclusion] using hD
  let S := moduleLocalizationShortComplex j (ULift.{u + 1} (ZMod n)) i hcomp
    (moduleUnit C.left (ULift.{u + 1} (ZMod n)))
  let hS : S.ShortExact := moduleLocalization_shortExact j (ULift.{u + 1} (ZMod n))
    i hcomp (moduleUnit C.left (ULift.{u + 1} (ZMod n)))
  let N := moduleRootsOfUnity C.left n
  let P := moduleClosedUnitExtAddEquiv i n N 2
  let G : Ext.{wM} S.X₃ N 2 ≃+ (D → ZMod n) :=
    P.trans (moduleFinitePointPurityAddEquiv hC D hclosed n hn hunit)
  exact G.toAddMonoidHom.comp ((hS.extClass.precomp N (by decide : 1 + 1 = 2)).comp
    (moduleLowerShriekRootsExtCohomologyAddEquiv (n := n) j hn
      (modulePoint_globalLevelInvertible n hunit) 1).symm.toAddMonoidHom)

include hC hclosed hD in
/-- Original roots restriction from the proper curve is injective for every
finite closed complement, including an empty complement. -/
theorem rootsOne_restriction_injective :
    Function.Injective (Kummer.rootsCohomologyPullback j n hn
      (modulePoint_globalLevelInvertible n hunit) 1) := by
  let i := inclusion C.left D
  let : IsClosedImmersion i :=
    inclusion_isClosedImmersion C.left D (Set.toFinite D) hclosed
  let hcomp : Set.range j = (Set.range i)ᶜ := by
    simpa only [i, range_inclusion] using hD
  let S := moduleLocalizationShortComplex j (ULift.{u + 1} (ZMod n)) i hcomp
    (moduleUnit C.left (ULift.{u + 1} (ZMod n)))
  let hS : S.ShortExact := moduleLocalization_shortExact j (ULift.{u + 1} (ZMod n))
    i hcomp (moduleUnit C.left (ULift.{u + 1} (ZMod n)))
  let N := moduleRootsOfUnity C.left n
  let P := moduleClosedUnitExtAddEquiv i n N 1
  let : Subsingleton (Ext.{wM} (moduleFinitePointSource C.left D n) N 1) :=
    moduleFinitePointExt_subsingleton hC D hclosed n hn hunit 1 (by decide)
  let : Subsingleton (Ext.{wM} S.X₃ N 1) := P.injective.subsingleton
  have hi : Function.Injective ((Ext.mk₀ S.f).precomp N (zero_add 1)) := by
    rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
    intro a ha
    obtain ⟨b, hb⟩ := Ext.contravariant_sequence_exact₂ hS N a ha
    rw [← hb, Subsingleton.elim b 0, Ext.comp_zero]
  let E : Ext.{wM} S.X₁ N 1 ≃+ Sheaf.H.{wAU} (mu U n) 1 :=
    moduleLowerShriekRootsExtCohomologyAddEquiv (n := n) j hn
      (modulePoint_globalLevelInvertible n hunit) 1
  let F : Ext.{wM} S.X₂ N 1 ≃+ Sheaf.H.{wA} (mu C.left n) 1 :=
    moduleRootsUnitExtCohomologyAddEquiv C.left n 1
  have hcomm := moduleLowerShriekRootsExtCohomologyAddEquiv_counit (n := n) j hn
    (modulePoint_globalLevelInvertible n hunit) 1
  intro a b hab
  obtain ⟨a, rfl⟩ := F.surjective a
  obtain ⟨b, rfl⟩ := F.surjective b
  have hh : ((Ext.mk₀ S.f).precomp N (zero_add 1)) a =
      ((Ext.mk₀ S.f).precomp N (zero_add 1)) b := by
    apply E.injective
    exact (DFunLike.congr_fun hcomm a).trans
      (hab.trans (DFunLike.congr_fun hcomm b).symm)
  exact congrArg F (hi hh)

/-- The ORIGINAL roots restriction and the actual localization boundary are exact. -/
theorem rootsOneLocalizationBoundary_exact :
    Function.Exact (Kummer.rootsCohomologyPullback j n hn
      (modulePoint_globalLevelInvertible n hunit) 1)
      (rootsOneLocalizationBoundary hC D hclosed j hD n hn hunit) := by
  let i := inclusion C.left D
  let : IsClosedImmersion i :=
    inclusion_isClosedImmersion C.left D (Set.toFinite D) hclosed
  let hcomp : Set.range j = (Set.range i)ᶜ := by
    simpa only [i, range_inclusion] using hD
  let S := moduleLocalizationShortComplex j (ULift.{u + 1} (ZMod n)) i hcomp
    (moduleUnit C.left (ULift.{u + 1} (ZMod n)))
  let hS : S.ShortExact := moduleLocalization_shortExact j (ULift.{u + 1} (ZMod n))
    i hcomp (moduleUnit C.left (ULift.{u + 1} (ZMod n)))
  let N := moduleRootsOfUnity C.left n
  let E : Ext.{wM} S.X₁ N 1 ≃+ Sheaf.H.{wAU} (mu U n) 1 :=
    moduleLowerShriekRootsExtCohomologyAddEquiv (n := n) j hn
      (modulePoint_globalLevelInvertible n hunit) 1
  let F : Ext.{wM} S.X₂ N 1 ≃+ Sheaf.H.{wA} (mu C.left n) 1 :=
    moduleRootsUnitExtCohomologyAddEquiv C.left n 1
  let P := moduleClosedUnitExtAddEquiv i n N 2
  let G : Ext.{wM} S.X₃ N 2 ≃+ (D → ZMod n) :=
    P.trans (moduleFinitePointPurityAddEquiv hC D hclosed n hn hunit)
  let f : Ext.{wM} S.X₂ N 1 →+ Ext.{wM} S.X₁ N 1 :=
    (Ext.mk₀ S.f).precomp N (zero_add 1)
  let d : Ext.{wM} S.X₁ N 1 →+ Ext.{wM} S.X₃ N 2 :=
    hS.extClass.precomp N (by decide : 1 + 1 = 2)
  have hraw : Function.Exact f d :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.contravariant_sequence_exact₁' hS N 1 2 (by decide))
  have hfirst := moduleLowerShriekRootsExtCohomologyAddEquiv_counit (n := n) j hn
    (modulePoint_globalLevelInvertible n hunit) 1
  have hboundary : (rootsOneLocalizationBoundary hC D hclosed j hD n hn hunit).comp
      E.toAddMonoidHom = G.toAddMonoidHom.comp d :=
    addEquiv_conjugate_comp E G d
  exact Function.Exact.of_ladder_addEquiv_of_exact F E G hfirst.symm hboundary hraw

/-- The boundary image is the kernel of SUM, through the proved original
finite support-forgetting map and original proper trace. -/
theorem rootsOneLocalizationBoundary_range :
    (rootsOneLocalizationBoundary hC D hclosed j hD n hn hunit).range =
      (∑ x : D, Pi.evalAddMonoidHom (fun _ : D => ZMod n) x).ker := by
  let i := inclusion C.left D
  let : IsClosedImmersion i :=
    inclusion_isClosedImmersion C.left D (Set.toFinite D) hclosed
  let hcomp : Set.range j = (Set.range i)ᶜ := by
    simpa only [i, range_inclusion] using hD
  let S := moduleLocalizationShortComplex j (ULift.{u + 1} (ZMod n)) i hcomp
    (moduleUnit C.left (ULift.{u + 1} (ZMod n)))
  let hS : S.ShortExact := moduleLocalization_shortExact j (ULift.{u + 1} (ZMod n))
    i hcomp (moduleUnit C.left (ULift.{u + 1} (ZMod n)))
  let N := moduleRootsOfUnity C.left n
  let E : Ext.{wM} S.X₁ N 1 ≃+ Sheaf.H.{wAU} (mu U n) 1 :=
    moduleLowerShriekRootsExtCohomologyAddEquiv (n := n) j hn
      (modulePoint_globalLevelInvertible n hunit) 1
  let P := moduleClosedUnitExtAddEquiv i n N 2
  let G : Ext.{wM} S.X₃ N 2 ≃+ (D → ZMod n) :=
    P.trans (moduleFinitePointPurityAddEquiv hC D hclosed n hn hunit)
  let F : Ext.{wM} S.X₂ N 2 ≃+ Sheaf.H.{wA} (mu C.left n) 2 :=
    moduleRootsUnitExtCohomologyAddEquiv C.left n 2
  let T := traceAddEquiv hC n hn hunit (modulePoint_globalLevelInvertible n hunit)
  let Q := F.trans T
  let d : Ext.{wM} S.X₁ N 1 →+ Ext.{wM} S.X₃ N 2 :=
    hS.extClass.precomp N (by decide : 1 + 1 = 2)
  let h : Ext.{wM} S.X₃ N 2 →+ Ext.{wM} S.X₂ N 2 :=
    (Ext.mk₀ S.g).precomp N (zero_add 2)
  let s : (D → ZMod n) →+ ZMod n :=
    ∑ x : D, Pi.evalAddMonoidHom (fun _ : D => ZMod n) x
  have hraw : Function.Exact d h :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.contravariant_sequence_exact₃' hS N 1 2 (by decide))
  have hboundary : (rootsOneLocalizationBoundary hC D hclosed j hD n hn hunit).comp
      E.toAddMonoidHom = G.toAddMonoidHom.comp d :=
    addEquiv_conjugate_comp E G d
  have Hsource := moduleClosedUnitExtAddEquiv_precomp i n N
  have Hforget := congrArg (fun r => F.toAddMonoidHom.comp r) Hsource
  have htrace : s.comp G.toAddMonoidHom = Q.toAddMonoidHom.comp h := by
    refine AddMonoidHom.ext (fun (e : Ext.{wM} S.X₃ N 2) => ?_)
    have HS := DFunLike.congr_fun Hforget e
    have HT := moduleFinitePointPurityAddEquiv_trace hC D hclosed n hn hunit (P e)
    have Hvalue := HT.symm.trans (congrArg T HS)
    change (∑ x : D, G e x) = Q (h e) at Hvalue
    change s (G e) = Q (h e)
    simpa only [s, AddMonoidHom.finsetSum_apply, Pi.evalAddMonoidHom_apply] using Hvalue
  have H := Function.Exact.of_ladder_addEquiv_of_exact E G Q hboundary htrace hraw
  ext a
  exact (H a).symm

end OpenBoundary

/-- Original roots H1 on a given finite nonempty open complement has
cardinality n^(2g + #D - 1). Auxiliary Ext worlds are chosen internally once. -/
theorem card_rootsOne_of_finite_nonempty_complement
    {k : Type u} [Field k] [IsAlgClosed k] {C : FScheme k}
    (hC : Curve.Properties C) (D : Set C.left) [Finite D]
    (hclosed : ∀ x ∈ D, IsClosed ({x} : Set C.left))
    {U : Scheme.{u}} (j : U ⟶ C.left) [IsOpenImmersion j]
    (hD : Set.range j = Dᶜ) (hne : D.Nonempty)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    [HasExt.{wAU} (AbelianSheaf.{u, u + 1} U)] :
    Nat.card (Sheaf.H.{wAU} (mu U n) 1) =
      n ^ (2 * coherentGenus k C + Nat.card D - 1) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let : HasExt.{u + 2} (ModuleSheaf C.left Λ) :=
    SheafOfModules.hasExt (constantRing C.left Λ)
  let : HasExt.{u + 2} (ModuleSheaf U Λ) := SheafOfModules.hasExt (constantRing U Λ)
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} C.left) := hasExtStandard C.left
  let : Fintype D := Fintype.ofFinite D
  let : Nonempty D := by obtain ⟨x, hx⟩ := hne; exact ⟨⟨x, hx⟩⟩
  let f := Kummer.rootsCohomologyPullback j n hn
    (modulePoint_globalLevelInvertible n hunit) 1
  let b := rootsOneLocalizationBoundary hC D hclosed j hD n hn hunit
  have hc := card_eq_mul_card_range_of_exact f b
    (rootsOne_restriction_injective hC D hclosed j hD n hn hunit)
    (rootsOneLocalizationBoundary_exact hC D hclosed j hD n hn hunit)
  change Nat.card (Sheaf.H.{wAU} (mu U n) 1) =
    Nat.card (Sheaf.H (mu C.left n) 1) * Nat.card
      (rootsOneLocalizationBoundary hC D hclosed j hD n hn hunit).range at hc
  rw [card_rootsOne hC n hn hunit,
    rootsOneLocalizationBoundary_range hC D hclosed j hD n hn hunit,
    card_sum_kernel D n hn] at hc
  calc
    _ = n ^ (2 * coherentGenus k C) * n ^ (Nat.card D - 1) := hc
    _ = _ := by
      rw [← pow_add]
      congr 1
      have : 0 < Nat.card D := Nat.card_pos
      omega

/-- Constant H1 has the same cardinality through the original chosen
constant-root coefficient isomorphism on the given open curve. -/
theorem card_constantOne_of_finite_nonempty_complement
    {k : Type u} [Field k] [IsAlgClosed k] {C : FScheme k}
    (hC : Curve.Properties C) (D : Set C.left) [Finite D]
    (hclosed : ∀ x ∈ D, IsClosed ({x} : Set C.left))
    {U : Scheme.{u}} (j : U ⟶ C.left) [IsOpenImmersion j]
    (hD : Set.range j = Dᶜ) (hne : D.Nonempty)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    [HasExt.{wAU} (AbelianSheaf.{u, u + 1} U)] :
    Nat.card (Sheaf.H.{wAU} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) U) 1) =
      n ^ (2 * coherentGenus k C + Nat.card D - 1) := by
  let e : ConstantFinite.coefficient (ULift.{u} (ZMod n)) U ≅ mu U n :=
    constantRootIso (X := (Over.mk (j ≫ C.hom) : FScheme k)) n hn hunit
  let E : Sheaf.H.{wAU} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) U) 1 ≃+
      Sheaf.H.{wAU} (mu U n) 1 :=
    ((Sheaf.functorH (Scheme.smallEtaleTopology U) 1).mapIso e).addCommGroupIsoToAddEquiv
  rw [Nat.card_congr E.toEquiv]
  exact card_rootsOne_of_finite_nonempty_complement hC D hclosed j hD hne n hn hunit

end Curves

end AlgebraicGeometry.Scheme.EtaleCohomology
