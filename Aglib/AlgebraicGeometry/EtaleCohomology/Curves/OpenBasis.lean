/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.OpenRank
public import Mathlib.LinearAlgebra.Basis.Prod

/-! # Bases of the original open-curve first cohomology

The unsigned localization boundary identifies the quotient by proper
restriction with the summation kernel on the original finite complement.
An enumeration gives coordinates on that kernel. Lifting its basis along
the boundary and adjoining the proper basis gives the open basis.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.OverField Scheme.OverField.Curve
open GroupCohomology.Kummer.Coefficients
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
open scoped BigOperators

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

private def sumCoordinates (n : ℕ) (ι : Type*) [Fintype ι] : (ι → ZMod n) →+ ZMod n :=
  ∑ i : ι, Pi.evalAddMonoidHom (fun _ : ι => ZMod n) i

private theorem mem_sumCoordinates_ker (n : ℕ) {ι : Type*} [Fintype ι]
    (x : ι → ZMod n) :
    x ∈ (sumCoordinates n ι).ker ↔ ∑ i, x i = 0 := by
  change sumCoordinates n ι x = 0 ↔ _
  simp only [sumCoordinates, AddMonoidHom.finsetSum_apply, Pi.evalAddMonoidHom_apply]

/-- Forget the first coordinate in the summation kernel. The inverse
sets the first coordinate to minus the sum of the remaining ones. -/
private def sumKernelEquiv (n : ℕ) (ι : Type*) [Fintype ι] [Nonempty ι] :
    (sumCoordinates n ι |>.toZModLinearMap n).ker ≃ₗ[ZMod n]
      (Fin (Nat.card ι - 1) → ZMod n) := by
  classical
  let m := Nat.card ι - 1
  have hpos : 0 < Nat.card ι := Nat.card_pos
  have hm : Fintype.card ι = m + 1 := by
    rw [← Nat.card_eq_fintype_card]
    dsimp [m]
    omega
  let e : ι ≃ Fin (m + 1) := Fintype.equivFinOfCardEq hm
  let K := (sumCoordinates n ι |>.toZModLinearMap n).ker
  let r : K →ₗ[ZMod n] (Fin m → ZMod n) :=
    LinearMap.pi fun i => (LinearMap.proj (e.symm i.succ)).comp K.subtype
  refine LinearEquiv.ofBijective r ⟨(injective_iff_map_eq_zero r).2 ?_, ?_⟩
  · intro x hx
    have htail (i : Fin m) : x.val (e.symm i.succ) = 0 := congrFun hx i
    have hs : ∑ i, x.val i = 0 := (mem_sumCoordinates_ker n x.val).mp x.property
    have h0 : x.val (e.symm 0) = 0 := by
      have h := (Equiv.sum_comp e.symm x.val).trans hs
      simpa only [Fin.sum_univ_succ, htail, Finset.sum_const_zero, add_zero] using h
    apply Subtype.ext
    funext i
    obtain ⟨j, rfl⟩ := e.symm.surjective i
    exact Fin.cases h0 htail j
  · intro v
    let a : Fin (m + 1) → ZMod n := Fin.cons (-∑ i, v i) v
    have ha : ∑ i : ι, a (e i) = 0 := by
      rw [Equiv.sum_comp e a, Fin.sum_univ_succ]
      simp only [a, Fin.cons_zero, Fin.cons_succ, neg_add_cancel]
    have hmem : (fun i => a (e i)) ∈ K :=
      (mem_sumCoordinates_ker n _).mpr ha
    refine ⟨⟨fun i => a (e i), hmem⟩, ?_⟩
    funext i
    change a (e (e.symm i.succ)) = v i
    simp only [Equiv.apply_symm_apply, a, Fin.cons_succ]

/-- Lifting the supplied quotient basis gives a section of the same
surjection and a product decomposition with the same injection. -/
private def splitWithBasis {R A B Q ι : Type*} [CommRing R]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup Q]
    [Module R A] [Module R B] [Module R Q]
    (f : A →ₗ[R] B) (g : B →ₗ[R] Q) (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (b : Module.Basis ι R Q) :
    (A × Q) ≃ₗ[R] B := by
  classical
  let v : ι → B := fun i => Classical.choose (hg (b i))
  let s : Q →ₗ[R] B := b.constr R v
  have hs : g.comp s = LinearMap.id := by
    apply b.ext
    intro i
    change g (b.constr R v (b i)) = b i
    rw [Module.Basis.constr_basis]
    exact Classical.choose_spec (hg (b i))
  exact ((hfg.splitSurjectiveEquiv hf) ⟨s, hs⟩).val.symm

private def basisFromBoundary (n r : ℕ) {A B ι : Type*} [Fintype ι] [Nonempty ι]
    [AddCommGroup A] [AddCommGroup B] [Module (ZMod n) A] [Module (ZMod n) B]
    (f : A →+ B) (b : B →+ (ι → ZMod n)) (hf : Function.Injective f)
    (hfb : Function.Exact f b) (hr : b.range = (sumCoordinates n ι).ker)
    (bA : Module.Basis (Fin r) (ZMod n) A) :
    Module.Basis (Fin (r + (Nat.card ι - 1))) (ZMod n) B := by
  let K := (sumCoordinates n ι |>.toZModLinearMap n).ker
  have hb (x : B) : b x ∈ K := by
    change b x ∈ (sumCoordinates n ι).ker
    rw [← hr]
    exact ⟨x, rfl⟩
  let g : B →ₗ[ZMod n] K := (b.toZModLinearMap n).codRestrict K hb
  have hg : Function.Surjective g := by
    intro x
    have hx : x.val ∈ b.range := by
      rw [hr]
      exact x.property
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, Subtype.ext ha⟩
  let fL := f.toZModLinearMap n
  have hfg : Function.Exact fL g := by
    intro x
    have hx : g x = 0 ↔ b x = 0 :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    exact hx.trans (hfb x)
  let bk := (Pi.basisFun (ZMod n) (Fin (Nat.card ι - 1))).map (sumKernelEquiv n ι).symm
  let e := splitWithBasis fL g hf hfg hg bk
  exact ((bA.prod bk).map e).reindex finSumFinEquiv

variable {k : Type u} [Field k] [IsAlgClosed k] {C : FScheme k}
  (hC : Curve.Properties C) (D : Set C.left) [Finite D]
  (hclosed : ∀ x ∈ D, IsClosed ({x} : Set C.left))
  {U : Scheme.{u}} (j : U ⟶ C.left) [IsOpenImmersion j]
  (hD : Set.range j = Dᶜ) (hne : D.Nonempty)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  [hU : HasExt.{w} (AbelianSheaf.{u, u + 1} U)]

include hC hclosed hD hne hn hunit in
/-- A basis of the original roots H1 on the given open complement, for
its native annihilation action. The construction includes level one. -/
@[no_expose]
def rootsOneOpenBasis :
    letI : Module (ZMod n) (Sheaf.H.{w} (mu U n) 1) :=
      AddCommGroup.zmodModule (nsmul_h1_eq_zero_of_killedBy (mu_killedBy U n))
    Module.Basis (Fin (2 * coherentGenus k C + Nat.card D - 1)) (ZMod n)
      (Sheaf.H.{w} (mu U n) 1) := by
  let : Module (ZMod n) (Sheaf.H.{w} (mu U n) 1) :=
    AddCommGroup.zmodModule (nsmul_h1_eq_zero_of_killedBy (mu_killedBy U n))
  let Λ := ULift.{u + 1} (ZMod n)
  let : HasExt.{u + 2} (ModuleSheaf C.left Λ) :=
    SheafOfModules.hasExt (constantRing C.left Λ)
  let : HasExt.{u + 2} (ModuleSheaf U Λ) := SheafOfModules.hasExt (constantRing U Λ)
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} C.left) := hasExtStandard C.left
  let := rootsOneZModModule.{u, u + 2} (X := C) n
  let : Fintype D := Fintype.ofFinite D
  let : Nonempty D := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, hx⟩⟩
  let A := Sheaf.H.{u + 2} (mu C.left n) 1
  let B := Sheaf.H.{w} (mu U n) 1
  let f : A →+ B := Kummer.rootsCohomologyPullback.{u, u + 2, w} j n hn
    (modulePoint_globalLevelInvertible n hunit) 1
  let b : B →+ (D → ZMod n) := rootsOneLocalizationBoundary hC D hclosed j hD n hn hunit
  have hr : b.range = (sumCoordinates n D).ker :=
    rootsOneLocalizationBoundary_range hC D hclosed j hD n hn hunit
  have hf : Function.Injective f.toFun :=
    rootsOne_restriction_injective hC D hclosed j hD n hn hunit
  have hfb : Function.Exact f.toFun b.toFun :=
    rootsOneLocalizationBoundary_exact hC D hclosed j hD n hn hunit
  let bA : Module.Basis (Fin (2 * coherentGenus k C)) (ZMod n) A :=
    rootsOneBasis.{u, u + 2} hC n hn hunit
  have hrank : 2 * coherentGenus k C + (Nat.card D - 1) =
      2 * coherentGenus k C + Nat.card D - 1 := by
    have : 0 < Nat.card D := Nat.card_pos
    omega
  exact (basisFromBoundary n _ f b hf hfb hr bA).reindex (finCongr hrank)

/-- A basis for the original constant coefficients, transported by the
existing constant-to-roots isomorphism on the same open scheme. -/
@[no_expose]
def constantOneOpenBasis :
    let V : FScheme k := Over.mk (j ≫ C.hom)
    let hk : KilledBy n (ConstantFinite.coefficient (ULift.{u} (ZMod n)) U) :=
      constantZMod_killedBy (X := V) n
    letI : Module (ZMod n)
        (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) U) 1) :=
      AddCommGroup.zmodModule (nsmul_h1_eq_zero_of_killedBy hk)
    Module.Basis (Fin (2 * coherentGenus k C + Nat.card D - 1)) (ZMod n)
      (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) U) 1) := by
  let V : FScheme k := Over.mk (j ≫ C.hom)
  let : HasExt.{w} (AbelianSheaf.{u, u + 1} V.left) := hU
  let hk : KilledBy n (ConstantFinite.coefficient (ULift.{u} (ZMod n)) U) :=
    constantZMod_killedBy (X := V) n
  let : Module (ZMod n)
      (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) U) 1) :=
    AddCommGroup.zmodModule (nsmul_h1_eq_zero_of_killedBy hk)
  let : Module (ZMod n) (Sheaf.H.{w} (mu U n) 1) :=
    AddCommGroup.zmodModule (nsmul_h1_eq_zero_of_killedBy (mu_killedBy U n))
  let e : Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) U) 1 ≃+
      Sheaf.H.{w} (mu U n) 1 := constantRootsAddEquiv.{u, w} (X := V) n hn hunit 1
  let E : Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) U) 1 ≃ₗ[ZMod n]
      Sheaf.H.{w} (mu U n) 1 :=
    { e with map_smul' := (e.toAddMonoidHom.toZModLinearMap n).map_smul }
  exact (rootsOneOpenBasis (hC := hC) (D := D) (hclosed := hclosed) (j := j)
    (hD := hD) (hne := hne) (n := n) (hn := hn) (hunit := hunit)).map E.symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
