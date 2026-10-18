/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction.Principal
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction.RingEquiv
public import Aglib.Algebra.Homology.Koszul.Coefficient.Regular
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Regular-list purity for native derived coinduction

For a finite weakly regular list `s` in any commutative ring `R`, the actual
installed D+ coinduction along `R → R / Ideal.ofList s` carries the regular
ring in degree zero to the actual quotient ring in degree `s.length`.
Native Ext from this quotient to the ring vanishes in all other natural
degrees. Its top Ext group is linearly the quotient ring, using the original
quotient-source action and original homology-to-Ext map.

The construction iterates the original regular-principal isomorphism through
native derived composition and literal quotient-ring equivalences. A private
standard-size model supplies the ordered top Ext line. The public derived
interfaces allow independent Ext and both derived-category size universes;
their actual single comparison is normalized by that same native Ext line
and is independent of the supplied injective resolution.

No Noetherian, flatness, finiteness or proper-ideal premise is imposed. Empty
lists, zero rings and unit equations are included. Ring and module carrier
universes are common, as in the finite Koszul and principal computations.
This ordered calculation does not yet identify the full Koszul top class,
its determinant under a change of generators, localization, or geometric
regular-immersion purity.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open ChainComplex.Koszul RingTheory.Sequence
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace ModuleCat
variable {R : Type u} [CommRing R]

private local instance standardDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u+1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

private local instance standardExt (A : Type u) [CommRing A] :
    HasExt.{u+1} (ModuleCat.{u} A) := hasExt_of_hasDerivedCategory _

private def quotSMulTopRingLinearEquiv (a : R) :
    QuotSMulTop a R ≃ₗ[R ⧸ Ideal.span {a}] R ⧸ Ideal.span {a} :=
  ((singleQuotientEquivQuotSMulTop (ModuleCat.of R R) a).symm.trans
    (singleQuotientIdealLinearEquiv a)).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

private theorem weaklyRegular_quotient_tail (a : R) (s : List R)
    (h : IsWeaklyRegular R (a :: s)) :
    IsWeaklyRegular (R ⧸ Ideal.span {a}) (s.map (Ideal.Quotient.mk (Ideal.span {a}))) :=
  (quotSMulTopRingLinearEquiv a).isWeaklyRegular_congr _ |>.mp
    ((isWeaklyRegular_cons_iff' R a s).mp h).2

private def regularQuotientConsRingEquiv (a : R) (s : List R) :
    (R ⧸ Ideal.span {a}) ⧸ Ideal.ofList (s.map (Ideal.Quotient.mk (Ideal.span {a}))) ≃+*
      R ⧸ Ideal.ofList (a :: s) :=
  (Ideal.quotEquivOfEq (Ideal.map_ofList (Ideal.Quotient.mk (Ideal.span {a})) s).symm).trans
    ((DoubleQuot.quotQuotEquivQuotSup (Ideal.span {a}) (Ideal.ofList s)).trans
      (Ideal.quotEquivOfEq (Ideal.ofList_cons a s).symm))

private theorem regularQuotientConsRingEquiv_apply_mk (a : R) (s : List R) (r : R) :
    regularQuotientConsRingEquiv a s
        (Ideal.Quotient.mk (Ideal.ofList (s.map (Ideal.Quotient.mk (Ideal.span {a}))))
          (Ideal.Quotient.mk (Ideal.span {a}) r)) =
      Ideal.Quotient.mk (Ideal.ofList (a :: s)) r := by
  simp only [regularQuotientConsRingEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  change Ideal.quotEquivOfEq (Ideal.ofList_cons a s).symm
    ((DoubleQuot.quotQuotEquivQuotSup (Ideal.span {a}) (Ideal.ofList s))
      (DoubleQuot.quotQuotMk (Ideal.span {a}) (Ideal.ofList s) r)) = _
  rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]

private theorem regularQuotientConsRingEquiv_comp (a : R) (s : List R) :
    (regularQuotientConsRingEquiv a s).toRingHom.comp
        ((Ideal.Quotient.mk (Ideal.ofList (s.map (Ideal.Quotient.mk (Ideal.span {a}))))).comp
          (Ideal.Quotient.mk (Ideal.span {a}))) =
      Ideal.Quotient.mk (Ideal.ofList (a :: s)) :=
  RingHom.ext (regularQuotientConsRingEquiv_apply_mk a s)

private abbrev ringSingle (A : Type u) [CommRing A] (i : ℤ) :=
  (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) i).obj (ModuleCat.of A A)

private abbrev derivedCoind {A B : Type u} [CommRing A] [CommRing B] (σ : A →+* B) :=
  (ModuleCat.coextendScalars σ).rightDerivedFunctorPlus

private def nilRingEquiv (A : Type u) [CommRing A] : A ≃+* A ⧸ Ideal.ofList ([] : List A) :=
  (RingEquiv.quotientBot A).symm.trans (Ideal.quotEquivOfEq Ideal.ofList_nil.symm)

private theorem nilRingEquiv_hom (A : Type u) [CommRing A] :
    (nilRingEquiv A).toRingHom = Ideal.Quotient.mk (Ideal.ofList ([] : List A)) := by
  ext a
  simp [nilRingEquiv]

private def nilIso (A : Type u) [CommRing A] :
    (derivedCoind (Ideal.Quotient.mk (Ideal.ofList ([] : List A)))).obj (ringSingle A 0) ≅
      ringSingle (A ⧸ Ideal.ofList ([] : List A)) 0 := by
  rw [← nilRingEquiv_hom A]
  exact ModuleCat.derivedCoextendScalarsPlusRingEquivRingIso (nilRingEquiv A) 0

private def shiftPureOne {A B : Type u} [CommRing A] [CommRing B]
    (σ : A →+* B) (n : ℕ)
    (e : (derivedCoind σ).obj (ringSingle A 0) ≅ ringSingle B (n : ℤ)) :
    (derivedCoind σ).obj (ringSingle A 1) ≅ ringSingle B ((n + 1 : ℕ) : ℤ) := by
  let F := derivedCoind σ
  exact ((((DerivedCategory.Plus.singleFunctors (ModuleCat.{u} A)).postcomp F).shiftIso
      (-1) 1 0 (by omega)).app (ModuleCat.of A A)).symm ≪≫
    (shiftFunctor (DerivedCategory.Plus (ModuleCat.{u} B)) (-1)).mapIso e ≪≫
    ((DerivedCategory.Plus.singleFunctors (ModuleCat.{u} B)).shiftIso
      (-1) ((n + 1 : ℕ) : ℤ) (n : ℤ) (by omega)).app (ModuleCat.of B B)

private def consIso (a : R) (s : List R) (ha : IsSMulRegular R a)
    (eTail :
      (derivedCoind (Ideal.Quotient.mk
        (Ideal.ofList (s.map (Ideal.Quotient.mk (Ideal.span {a})))))).obj
        (ringSingle (R ⧸ Ideal.span {a}) 0) ≅
      ringSingle ((R ⧸ Ideal.span {a}) ⧸
        Ideal.ofList (s.map (Ideal.Quotient.mk (Ideal.span {a})))) (s.length : ℤ)) :
    (derivedCoind (Ideal.Quotient.mk (Ideal.ofList (a :: s)))).obj (ringSingle R 0) ≅
      ringSingle (R ⧸ Ideal.ofList (a :: s)) ((s.length + 1 : ℕ) : ℤ) := by
  let S := R ⧸ Ideal.span {a}
  let T := S ⧸ Ideal.ofList (s.map (Ideal.Quotient.mk (Ideal.span {a})))
  let U := R ⧸ Ideal.ofList (a :: s)
  let σ : R →+* S := Ideal.Quotient.mk (Ideal.span {a})
  let τ : S →+* T := Ideal.Quotient.mk
    (Ideal.ofList (s.map (Ideal.Quotient.mk (Ideal.span {a}))))
  let e : T ≃+* U := regularQuotientConsRingEquiv a s
  let eFirst : (derivedCoind σ).obj (ringSingle R 0) ≅ ringSingle S 1 :=
    ModuleCat.derivedCoextendScalarsPlusPrincipalRingIso a ha
      (injectiveResolution (ModuleCat.of R R))
  let eTotal : (derivedCoind (τ.comp σ)).obj (ringSingle R 0) ≅
      ringSingle T ((s.length + 1 : ℕ) : ℤ) :=
    (ModuleCat.derivedCoextendScalarsPlusCompIso.{u,u,u,u,u+1,u+1,u+1}
      σ τ).app (ringSingle R 0) ≪≫
      (derivedCoind τ).mapIso eFirst ≪≫ shiftPureOne τ s.length eTail
  let eFinal : (derivedCoind (e.toRingHom.comp (τ.comp σ))).obj (ringSingle R 0) ≅
      ringSingle U ((s.length + 1 : ℕ) : ℤ) :=
    (ModuleCat.derivedCoextendScalarsPlusCompIso.{u,u,u,u,u+1,u+1,u+1}
      (τ.comp σ) e.toRingHom).app (ringSingle R 0) ≪≫
      (derivedCoind e.toRingHom).mapIso eTotal ≪≫
      ModuleCat.derivedCoextendScalarsPlusRingEquivRingIso e ((s.length + 1 : ℕ) : ℤ)
  have h : e.toRingHom.comp (τ.comp σ) = Ideal.Quotient.mk (Ideal.ofList (a :: s)) :=
    regularQuotientConsRingEquiv_comp a s
  rw [← h]
  exact eFinal

private def regularListIsoAux : (n : ℕ) →
    (A : Type u) → [CommRing A] → (s : List A) →
    IsWeaklyRegular A s → s.length = n →
    ((derivedCoind (Ideal.Quotient.mk (Ideal.ofList s))).obj (ringSingle A 0) ≅
      ringSingle (A ⧸ Ideal.ofList s) (s.length : ℤ)) := by
  intro n
  induction n with
  | zero =>
    intro A _ s hs hlen
    cases s with
    | nil => exact nilIso A
    | cons a s => simp at hlen
  | succ n ih =>
    intro A _ s hs hlen
    cases s with
    | nil => simp at hlen
    | cons a s =>
      have htail : s.length = n := Nat.succ.inj hlen
      let S := A ⧸ Ideal.span {a}
      let tail := s.map (Ideal.Quotient.mk (Ideal.span {a}))
      have hreg : IsWeaklyRegular S tail := weaklyRegular_quotient_tail a s hs
      have ht : tail.length = n := by simpa only [tail, List.length_map] using htail
      let eTail := ih S tail hreg ht
      exact consIso a s ((isWeaklyRegular_cons_iff A a s).mp hs).1
        (by simpa only [S, tail, List.length_map] using eTail)

private def regularListIso (s : List R) (hs : IsWeaklyRegular R s) :
    (derivedCoind (Ideal.Quotient.mk (Ideal.ofList s))).obj (ringSingle R 0) ≅
      ringSingle (R ⧸ Ideal.ofList s) (s.length : ℤ) :=
  regularListIsoAux s.length R s hs rfl

private theorem regularList_isGE (s : List R) (hs : IsWeaklyRegular R s) :
    ((derivedCoind (Ideal.Quotient.mk (Ideal.ofList s))).obj (ringSingle R 0)).IsGE
      (s.length : ℤ) :=
  DerivedCategory.Plus.TStructure.t.isGE_of_iso (regularListIso s hs).symm _

private theorem regularList_isLE (s : List R) (hs : IsWeaklyRegular R s) :
    ((derivedCoind (Ideal.Quotient.mk (Ideal.ofList s))).obj (ringSingle R 0)).IsLE
      (s.length : ℤ) :=
  DerivedCategory.Plus.TStructure.t.isLE_of_iso (regularListIso s hs).symm _

private theorem isZero_regularListHomology_of_ne (s : List R) (hs : IsWeaklyRegular R s)
    (i : ℤ) (hi : i ≠ (s.length : ℤ)) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.ofList s)) i).obj
      ((derivedCoind (Ideal.Quotient.mk (Ideal.ofList s))).obj (ringSingle R 0))) := by
  let := regularList_isGE s hs
  let := regularList_isLE s hs
  rcases lt_or_gt_of_ne hi with h | h
  · exact DerivedCategory.Plus.isZero_homology_of_isGE _ (s.length : ℤ) i h
  · exact DerivedCategory.Plus.isZero_homology_of_isLE _ (s.length : ℤ) i h

private def regularListHomologyLinearEquiv (s : List R) (hs : IsWeaklyRegular R s) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.ofList s))
      (s.length : ℤ)).obj
      ((derivedCoind (Ideal.Quotient.mk (Ideal.ofList s))).obj (ringSingle R 0)) ≃ₗ[
        R ⧸ Ideal.ofList s] R ⧸ Ideal.ofList s :=
  ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.ofList s))
      (s.length : ℤ)).mapIso (regularListIso s hs) ≪≫
    (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
      (C := ModuleCat.{u} (R ⧸ Ideal.ofList s)) (s.length : ℤ)).app
        (ModuleCat.of (R ⧸ Ideal.ofList s) (R ⧸ Ideal.ofList s))).toLinearEquiv

universe w
variable [HasExt.{w} (ModuleCat.{u} R)]

public section

/-- The ordered quotient line computes native top Ext with its original quotient-ring action. -/
def regularListQuotientExtLinearEquiv (s : List R) (hs : IsWeaklyRegular R s)
    (J : InjectiveResolution (ModuleCat.of R R)) :
    letI := Ext.quotientSourceModule.{u,w} (Ideal.ofList s) (ModuleCat.of R R) s.length
    (R ⧸ Ideal.ofList s) ≃ₗ[R ⧸ Ideal.ofList s]
      Ext.{w} (ModuleCat.of R (R ⧸ Ideal.ofList s)) (ModuleCat.of R R) s.length := by
  letI := Ext.quotientSourceModule.{u,w} (Ideal.ofList s) (ModuleCat.of R R) s.length
  exact (regularListHomologyLinearEquiv s hs).symm.trans
    (ModuleCat.derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv.{u,w,u+1,u+1}
      (Ideal.ofList s) (ModuleCat.of R R) J s.length)

end

@[expose] public section

/-- The ordered native top-Ext comparison is independent of the supplied resolution. -/
theorem regularListQuotientExtLinearEquiv_independent (s : List R) (hs : IsWeaklyRegular R s)
    (I J : InjectiveResolution (ModuleCat.of R R)) :
    letI := Ext.quotientSourceModule.{u,w} (Ideal.ofList s) (ModuleCat.of R R) s.length
    regularListQuotientExtLinearEquiv.{u,w} s hs I =
      regularListQuotientExtLinearEquiv.{u,w} s hs J := by
  let := Ext.quotientSourceModule.{u,w} (Ideal.ofList s) (ModuleCat.of R R) s.length
  unfold regularListQuotientExtLinearEquiv
  rw [ModuleCat.derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv_independent]

/-- Native Ext from a weakly regular quotient to the ring vanishes outside the list length. -/
theorem regularListQuotientExt_eq_zero_of_ne_length (s : List R) (hs : IsWeaklyRegular R s)
    (q : ℕ) (hq : q ≠ s.length)
    (z : Ext.{w} (ModuleCat.of R (R ⧸ Ideal.ofList s)) (ModuleCat.of R R) q) : z = 0 := by
  let E := ModuleCat.derivedCoextendScalarsPlusHomologyExtAddEquiv.{u,w,u+1,u+1}
    (Ideal.Quotient.mk (Ideal.ofList s)) (ModuleCat.of R R)
      (injectiveResolution (ModuleCat.of R R)) q
  have hq' : (q : ℤ) ≠ (s.length : ℤ) := by exact_mod_cast hq
  let := ModuleCat.subsingleton_of_isZero (isZero_regularListHomology_of_ne s hs q hq')
  exact E.symm.injective (Subsingleton.elim _ _)

section Derived
universe v z
variable (s : List R) (hs : IsWeaklyRegular R s)
  [HasDerivedCategory.{v} (ModuleCat.{u} R)]
  [HasDerivedCategory.{z} (ModuleCat.{u} (R ⧸ Ideal.ofList s))]

/-- Actual top homology is the original quotient line, through the native Ext comparison. -/
def derivedCoextendScalarsPlusRegularListHomologyLinearEquiv
    (J : InjectiveResolution (ModuleCat.of R R)) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.ofList s))
      (s.length : ℤ)).obj
      ((ModuleCat.coextendScalars (Ideal.Quotient.mk (Ideal.ofList s))).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) ≃ₗ[
          R ⧸ Ideal.ofList s] R ⧸ Ideal.ofList s := by
  letI := Ext.quotientSourceModule.{u,w} (Ideal.ofList s) (ModuleCat.of R R) s.length
  exact (ModuleCat.derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv.{u,w,v,z}
    (Ideal.ofList s) (ModuleCat.of R R) J s.length).trans
      (regularListQuotientExtLinearEquiv.{u,w} s hs J).symm

include hs in
/-- Weak regularity gives the actual lower cohomological bound at the list length. -/
theorem derivedCoextendScalarsPlusRegularList_isGE (J : InjectiveResolution (ModuleCat.of R R)) :
    ((ModuleCat.coextendScalars (Ideal.Quotient.mk (Ideal.ofList s))).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R R))).IsGE (s.length : ℤ) := by
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
  intro i hi
  by_cases hi0 : i < 0
  · exact Functor.isZero_homology_rightDerivedFunctorPlus_of_isGE
      (ModuleCat.coextendScalars (Ideal.Quotient.mk (Ideal.ofList s)))
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))
      0 i hi0
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
    apply ModuleCat.isZero_iff_subsingleton.mpr
    let E := ModuleCat.derivedCoextendScalarsPlusHomologyExtAddEquiv.{u,w,v,z}
      (Ideal.Quotient.mk (Ideal.ofList s)) (ModuleCat.of R R) J q
    refine ⟨fun x y => E.injective ?_⟩
    have hq : q ≠ s.length := by omega
    exact (regularListQuotientExt_eq_zero_of_ne_length s hs q hq (E x)).trans
      (regularListQuotientExt_eq_zero_of_ne_length s hs q hq (E y)).symm

include hs in
/-- Weak regularity gives the actual upper cohomological bound at the list length. -/
theorem derivedCoextendScalarsPlusRegularList_isLE (J : InjectiveResolution (ModuleCat.of R R)) :
    ((ModuleCat.coextendScalars (Ideal.Quotient.mk (Ideal.ofList s))).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R R))).IsLE (s.length : ℤ) := by
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff, DerivedCategory.isLE_iff]
  intro i hi
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  let E := ModuleCat.derivedCoextendScalarsPlusHomologyExtAddEquiv.{u,w,v,z}
    (Ideal.Quotient.mk (Ideal.ofList s)) (ModuleCat.of R R) J q
  refine ⟨fun x y => E.injective ?_⟩
  have hq : q ≠ s.length := by omega
  exact (regularListQuotientExt_eq_zero_of_ne_length s hs q hq (E x)).trans
    (regularListQuotientExt_eq_zero_of_ne_length s hs q hq (E y)).symm

/-- Actual derived coinduction is the original quotient ring in degree equal to the list length. -/
def derivedCoextendScalarsPlusRegularListRingIso (J : InjectiveResolution (ModuleCat.of R R)) :
    (ModuleCat.coextendScalars (Ideal.Quotient.mk (Ideal.ofList s))).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ≅
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} (R ⧸ Ideal.ofList s))
        (s.length : ℤ)).obj (ModuleCat.of (R ⧸ Ideal.ofList s) (R ⧸ Ideal.ofList s)) := by
  let K :=
    (ModuleCat.coextendScalars (Ideal.Quotient.mk (Ideal.ofList s))).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))
  let := derivedCoextendScalarsPlusRegularList_isGE.{u,w,v,z} s hs J
  let := derivedCoextendScalarsPlusRegularList_isLE.{u,w,v,z} s hs J
  exact DerivedCategory.Plus.isoSingleHomology K (s.length : ℤ) ≪≫
    (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} (R ⧸ Ideal.ofList s))
      (s.length : ℤ)).mapIso
        (derivedCoextendScalarsPlusRegularListHomologyLinearEquiv.{u,w,v,z} s hs J).toModuleIso

/-- The original top-homology comparison is independent of the supplied resolution. -/
theorem derivedCoextendScalarsPlusRegularListHomologyLinearEquiv_independent
    (I J : InjectiveResolution (ModuleCat.of R R)) :
    derivedCoextendScalarsPlusRegularListHomologyLinearEquiv.{u,w,v,z} s hs I =
      derivedCoextendScalarsPlusRegularListHomologyLinearEquiv.{u,w,v,z} s hs J := by
  let := Ext.quotientSourceModule.{u,w} (Ideal.ofList s) (ModuleCat.of R R) s.length
  unfold derivedCoextendScalarsPlusRegularListHomologyLinearEquiv
  rw [ModuleCat.derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv_independent
    (Ideal.ofList s) (ModuleCat.of R R) I J s.length,
    regularListQuotientExtLinearEquiv_independent s hs I J]

/-- The top-homology line retains the original native quotient-linear Ext comparison. -/
theorem derivedCoextendScalarsPlusRegularListHomologyLinearEquiv_ext
    (J : InjectiveResolution (ModuleCat.of R R))
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.ofList s))
      (s.length : ℤ)).obj
      ((ModuleCat.coextendScalars (Ideal.Quotient.mk (Ideal.ofList s))).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) :
    ModuleCat.derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv.{u,w,v,z}
      (Ideal.ofList s) (ModuleCat.of R R) J s.length x =
      regularListQuotientExtLinearEquiv.{u,w} s hs J
        (derivedCoextendScalarsPlusRegularListHomologyLinearEquiv.{u,w,v,z} s hs J x) := by
  let := Ext.quotientSourceModule.{u,w} (Ideal.ofList s) (ModuleCat.of R R) s.length
  simp only [derivedCoextendScalarsPlusRegularListHomologyLinearEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]

/-- The actual purity isomorphism induces the same original quotient-linear homology map. -/
@[reassoc]
theorem derivedCoextendScalarsPlusRegularListRingIso_homology
    (J : InjectiveResolution (ModuleCat.of R R)) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.ofList s))
        (s.length : ℤ)).map (derivedCoextendScalarsPlusRegularListRingIso.{u,w,v,z} s hs J).hom ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
        (C := ModuleCat.{u} (R ⧸ Ideal.ofList s)) (s.length : ℤ)).hom.app
          (ModuleCat.of (R ⧸ Ideal.ofList s) (R ⧸ Ideal.ofList s)) =
      (derivedCoextendScalarsPlusRegularListHomologyLinearEquiv.{u,w,v,z}
        s hs J).toModuleIso.hom := by
  let K :=
    (ModuleCat.coextendScalars (Ideal.Quotient.mk (Ideal.ofList s))).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))
  let := derivedCoextendScalarsPlusRegularList_isGE.{u,w,v,z} s hs J
  let := derivedCoextendScalarsPlusRegularList_isLE.{u,w,v,z} s hs J
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.ofList s))
    (s.length : ℤ)
  let S := DerivedCategory.Plus.singleFunctor (ModuleCat.{u} (R ⧸ Ideal.ofList s))
    (s.length : ℤ)
  let E := DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
    (C := ModuleCat.{u} (R ⧸ Ideal.ofList s)) (s.length : ℤ)
  let e := (derivedCoextendScalarsPlusRegularListHomologyLinearEquiv.{u,w,v,z} s hs J).toModuleIso
  have hn : H.map (DerivedCategory.Plus.isoSingleHomology K (s.length : ℤ)).hom ≫
      E.hom.app (H.obj K) = 𝟙 _ := by
    change (DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.ofList s))
      (s.length : ℤ)).map
        ((DerivedCategory.Plus.ι : _ ⥤ DerivedCategory
          (ModuleCat.{u} (R ⧸ Ideal.ofList s))).map
            (DerivedCategory.Plus.isoSingleHomology K (s.length : ℤ)).hom) ≫ _ = _
    rw [DerivedCategory.Plus.ι_map_isoSingleHomology_hom]
    exact DerivedCategory.isoSingleHomology_homology _ (s.length : ℤ)
  change H.map ((DerivedCategory.Plus.isoSingleHomology K (s.length : ℤ)).hom ≫
    S.map e.hom) ≫ E.hom.app _ = e.hom
  have he : H.map (S.map e.hom) ≫ E.hom.app _ =
      E.hom.app (H.obj K) ≫ e.hom := E.hom.naturality e.hom
  rw [Functor.map_comp, Category.assoc, he, ← Category.assoc, hn, Category.id_comp]

/-- The homology-normalized actual purity isomorphism is independent of the resolution. -/
theorem derivedCoextendScalarsPlusRegularListRingIso_independent
    (I J : InjectiveResolution (ModuleCat.of R R)) :
    derivedCoextendScalarsPlusRegularListRingIso.{u,w,v,z} s hs I =
      derivedCoextendScalarsPlusRegularListRingIso.{u,w,v,z} s hs J := by
  let := derivedCoextendScalarsPlusRegularList_isGE.{u,w,v,z} s hs I
  let := derivedCoextendScalarsPlusRegularList_isLE.{u,w,v,z} s hs I
  apply Iso.ext
  change (DerivedCategory.Plus.isoSingleHomology _ (s.length : ℤ)).hom ≫
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} (R ⧸ Ideal.ofList s))
        (s.length : ℤ)).map
          (derivedCoextendScalarsPlusRegularListHomologyLinearEquiv.{u,w,v,z}
            s hs I).toModuleIso.hom =
    (DerivedCategory.Plus.isoSingleHomology _ (s.length : ℤ)).hom ≫
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} (R ⧸ Ideal.ofList s))
        (s.length : ℤ)).map
          (derivedCoextendScalarsPlusRegularListHomologyLinearEquiv.{u,w,v,z}
            s hs J).toModuleIso.hom
  rw [derivedCoextendScalarsPlusRegularListHomologyLinearEquiv_independent s hs I J]


/-- The original ring coefficient action descends through the actual regular-list purity map. -/
@[reassoc]
theorem derivedCoextendScalarsPlusRegularListRingIso_smul
    (J : InjectiveResolution (ModuleCat.of R R)) (r : R) :
    (coextendScalars (Ideal.Quotient.mk (Ideal.ofList s))).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).map
          (r • 𝟙 (ModuleCat.of R R))) ≫
      (derivedCoextendScalarsPlusRegularListRingIso.{u,w,v,z} s hs J).hom =
    (derivedCoextendScalarsPlusRegularListRingIso.{u,w,v,z} s hs J).hom ≫
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} (R ⧸ Ideal.ofList s))
        (s.length : ℤ)).map
          (Ideal.Quotient.mk (Ideal.ofList s) r •
            𝟙 (ModuleCat.of (R ⧸ Ideal.ofList s) (R ⧸ Ideal.ofList s))) := by
  let S := R ⧸ Ideal.ofList s
  let F := (coextendScalars (Ideal.Quotient.mk (Ideal.ofList s))).rightDerivedFunctorPlus
  let K := F.obj ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))
  let p := derivedCoextendScalarsPlusRegularListRingIso.{u,w,v,z} s hs J
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (s.length : ℤ)
  let E := DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
    (C := ModuleCat.{u} S) (s.length : ℤ)
  let L := derivedCoextendScalarsPlusRegularListHomologyLinearEquiv.{u,w,v,z} s hs J
  let V := ModuleCat.of S S
  let g := Ideal.Quotient.mk (Ideal.ofList s) r • 𝟙 V
  let t := (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} S) (s.length : ℤ)).map g
  let f := F.map ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).map
    (r • 𝟙 (ModuleCat.of R R)))
  let := derivedCoextendScalarsPlusRegularList_isGE.{u,w,v,z} s hs J
  let := derivedCoextendScalarsPlusRegularList_isLE.{u,w,v,z} s hs J
  have hp : H.map p.hom ≫ E.hom.app V = L.toModuleIso.hom :=
    derivedCoextendScalarsPlusRegularListRingIso_homology s hs J
  have ht : H.map t ≫ E.hom.app V = E.hom.app V ≫ g := E.hom.naturality g
  apply (DerivedCategory.Plus.ι (C := ModuleCat.{u} S)).map_injective
  apply DerivedCategory.homology_map_injective_of_isGE_of_isLE _ _ (s.length : ℤ)
  change H.map (f ≫ p.hom) = H.map (p.hom ≫ t)
  apply (cancel_mono (E.hom.app V)).mp
  simp only [Functor.map_comp, Category.assoc, ht]
  rw [hp, ← Category.assoc (H.map p.hom) (E.hom.app V), hp]
  have hf : H.map f = Ideal.Quotient.mk (Ideal.ofList s) r • 𝟙 (H.obj K) :=
    derivedCoextendScalarsPlusQuotientHomology_map_smul_id
      (Ideal.ofList s) (ModuleCat.of R R) s.length r
  rw [hf]
  have hz {A B : ModuleCat.{u} S} (a : S) (e : A ⟶ B) :
      (a • 𝟙 A) ≫ e = e ≫ (a • 𝟙 B) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact e.hom.map_smul a x
  exact hz (Ideal.Quotient.mk (Ideal.ofList s) r) L.toModuleIso.hom

end Derived

end

end ModuleCat
