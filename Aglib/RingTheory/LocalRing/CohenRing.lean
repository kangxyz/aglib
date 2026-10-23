/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.PrincipalDiscreteValuationRing
public import Aglib.RingTheory.DiscreteValuationRing.FilteredColimit
public import Aglib.RingTheory.DiscreteValuationRing.ResidueExtension
public import Aglib.RingTheory.DiscreteValuationRing.SameUniformizer
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# An actual marked Cohen construction

The same-uniformizer successor and actual filtered colimit construction
produce a Cohen DVR for an arbitrary field of prime characteristic.
The marked full subcategory has its filtered colimits by the proved
DVR/kernel theorem. The original residue points are retained throughout.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped nonZeroDivisors

namespace CohenConstruction

universe u

private structure Marked (p : ℕ) {K : Type u} [Field K]
    (X : Over (CommRingCat.of K)) : Prop where
  domain : IsDomain X.left
  dvr : @IsDiscreteValuationRing X.left _ domain
  charZero : CharZero X.left
  uniformizer : Irreducible (p : X.left)
  kernel :
    let _ : IsDomain X.left := domain
    let _ : IsDiscreteValuationRing X.left := dvr
    RingHom.ker X.hom.hom = maximalIdeal X.left

private def marked (p : ℕ) (K : Type u) [Field K] :
    ObjectProperty (Over (CommRingCat.of K)) := Marked p

private abbrev Stage (p : ℕ) (K : Type u) [Field K] := (marked p K).FullSubcategory

private theorem charZero_of_uniformizer_map
    {B D : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CharZero B]
    [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    (p : ℕ) (f : B →+* D) (hpB : Irreducible (p : B)) (hpD : Irreducible (p : D)) :
    CharZero D := by
  have hf : Function.Injective f := IsDiscreteValuationRing.injective_of_map_irreducible f hpB
    (by simpa only [map_natCast] using hpD)
  constructor
  intro m n h
  apply Nat.cast_injective (R := B)
  apply hf
  simpa only [map_natCast] using h

private theorem marked_of_isColimit (p : ℕ) (K : Type u) [Field K]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Over (CommRingCat.of K)) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ i, Marked p (F.obj i)) : Marked p c.pt := by
  let F' := F ⋙ Over.forget (CommRingCat.of K)
  let c' := (Over.forget (CommRingCat.of K)).mapCocone c
  have hc' : IsColimit c' := isColimitOfPreserves (Over.forget (CommRingCat.of K)) hc
  let : ∀ i, IsDomain (F'.obj i) := fun i ↦ (hF i).domain
  let : ∀ i, IsDiscreteValuationRing (F'.obj i) := fun i ↦ (hF i).dvr
  have hp (i : J) : Irreducible (p : F'.obj i) := (hF i).uniformizer
  have hg (i : J) : RingHom.ker (c.pt.hom.hom.comp (c'.ι.app i).hom) =
      maximalIdeal (F'.obj i) := by
    have hw : c.pt.hom.hom.comp (c.ι.app i).left.hom = (F.obj i).hom.hom := by
      simpa only [Functor.const_obj_obj, CommRingCat.hom_comp] using
        congrArg (fun f : (F.obj i).left ⟶ CommRingCat.of K ↦ f.hom) (Over.w (c.ι.app i))
    change RingHom.ker (c.pt.hom.hom.comp (c.ι.app i).left.hom) = _
    rw [hw]
    exact (hF i).kernel
  let : IsDomain c.pt.left := CommRingCat.isDomain_of_isColimit_of_uniformizer F' c' hc' p hp
  let : IsDiscreteValuationRing c.pt.left :=
    CommRingCat.isDiscreteValuationRing_of_isColimit_of_uniformizer F' c' hc' p hp c.pt.hom.hom hg
  have hp' : Irreducible (p : c.pt.left) :=
    CommRingCat.irreducible_natCast_of_isColimit F' c' hc' p hp c.pt.hom.hom hg
  have hchar : CharZero c.pt.left := by
    let i : J := Classical.choice (IsFiltered.nonempty (C := J))
    let : CharZero (F'.obj i) := (hF i).charZero
    exact charZero_of_uniformizer_map p (c'.ι.app i).hom (hp i) hp'
  exact {
    domain := inferInstance
    dvr := inferInstance
    charZero := hchar
    uniformizer := hp'
    kernel := CommRingCat.ker_point_of_isColimit_of_uniformizer F' c' hc' p hp c.pt.hom.hom hg }

private instance marked_closedUnderFilteredColimits (p : ℕ) (K : Type u) [Field K]
    (J : Type u) [SmallCategory J] [IsFiltered J] :
    (marked p K).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le X hX := by
    obtain ⟨h⟩ := hX
    exact marked_of_isColimit p K h.diag ⟨X, h.ι⟩ h.isColimit h.prop_diag_obj

private instance marked_hasIteration (p : ℕ) (K : Type u) [Field K]
    (J : Type u) [LinearOrder J] [Nonempty J] :
    HasIterationOfShape J (Stage p K) where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    let : Nonempty (Set.Iio j) := hj.nonempty_Iio.to_subtype
    infer_instance
  hasColimitsOfShape := inferInstance

private def initialStage (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [CharP K p] :
    Stage p K := by
  let B := ULift.{u} (PadicInt p)
  let e : B ≃+* PadicInt p := ULift.ringEquiv
  let : IsDomain B := MulEquiv.isDomain (PadicInt p) e.toMulEquiv
  let : IsDiscreteValuationRing B :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm
  let : CharZero B := ⟨fun m n h ↦ by
    apply Nat.cast_injective (R := PadicInt p)
    calc
      (m : PadicInt p) = e.toRingHom (m : B) := (map_natCast e.toRingHom m).symm
      _ = e.toRingHom (n : B) := congrArg e.toRingHom h
      _ = (n : PadicInt p) := map_natCast e.toRingHom n⟩
  let : Algebra (ZMod p) K := ZMod.algebra K p
  have hp0 : Irreducible (p : B) := by
    have hpadic : Irreducible (p : PadicInt p) := PadicInt.irreducible_p
    have hmap : Irreducible (e.symm.toRingHom (p : PadicInt p)) :=
      hpadic.map e.symm.toMulEquiv
    simpa only [map_natCast] using hmap
  let g : B →+* K := (algebraMap (ZMod p) K).comp (PadicInt.toZMod.comp e.toRingHom)
  have hker : RingHom.ker g = maximalIdeal B := by
    let : IsLocalHom e.toRingHom := IsDiscreteValuationRing.isLocalHom_of_map_irreducible
      e.toRingHom hp0 (by simpa only [map_natCast] using (PadicInt.irreducible_p :
        Irreducible (p : PadicInt p)))
    calc
      RingHom.ker g = RingHom.ker (PadicInt.toZMod.comp e.toRingHom) :=
        RingHom.ker_comp_of_injective _ (f := algebraMap (ZMod p) K)
          (algebraMap (ZMod p) K).injective
      _ = (maximalIdeal (PadicInt p)).comap e.toRingHom := by
        rw [← RingHom.comap_ker, PadicInt.ker_toZMod]
      _ = maximalIdeal B := IsLocalRing.maximalIdeal_comap e.toRingHom
  exact ⟨Over.mk (CommRingCat.ofHom g), {
    domain := (inferInstance : IsDomain B)
    dvr := (inferInstance : IsDiscreteValuationRing B)
    charZero := (inferInstance : CharZero B)
    uniformizer := hp0
    kernel := hker }⟩

private def extendElement (p : ℕ) (K : Type u) [Field K]
    (X : Stage p K) (a : K) : Σ Y : Stage p K, X ⟶ Y := by
  let : IsDomain X.obj.left := X.property.domain
  let : IsDiscreteValuationRing X.obj.left := X.property.dvr
  let : CharZero X.obj.left := X.property.charZero
  let e := IsDiscreteValuationRing.residueExtension p X.property.uniformizer
    X.obj.hom.hom X.property.kernel a
  let Y : Stage p K := ⟨Over.mk (CommRingCat.ofHom e.point), {
    domain := e.isDomain
    dvr := e.isDiscreteValuationRing
    charZero := charZero_of_uniformizer_map (D := e.ring) p e.map
      X.property.uniformizer e.irreducible
    uniformizer := e.irreducible
    kernel := e.ker_point }⟩
  refine ⟨Y, ObjectProperty.homMk (Over.homMk (CommRingCat.ofHom e.map) ?_)⟩
  exact CommRingCat.hom_ext e.point_comp

private theorem extendElement_mem_range (p : ℕ) (K : Type u) [Field K]
    (X : Stage p K) (a : K) :
    a ∈ Set.range (extendElement p K X a).1.obj.hom.hom := by
  let : IsDomain X.obj.left := X.property.domain
  let : IsDiscreteValuationRing X.obj.left := X.property.dvr
  exact (IsDiscreteValuationRing.residueExtension p X.property.uniformizer
    X.obj.hom.hom X.property.kernel a).mem_range

private def missingElement (p : ℕ) (K : Type u) [Field K] (X : Stage p K)
    (h : ¬Function.Surjective X.obj.hom.hom) : K :=
  (not_forall.mp h).choose

private theorem missingElement_not_mem_range (p : ℕ) (K : Type u) [Field K]
    (X : Stage p K) (h : ¬Function.Surjective X.obj.hom.hom) :
    missingElement p K X h ∉ Set.range X.obj.hom.hom :=
  (not_forall.mp h).choose_spec

private def successorArrow (p : ℕ) (K : Type u) [Field K]
    (X : Stage p K) : Σ Y : Stage p K, X ⟶ Y := by
  classical
  exact if h : Function.Surjective X.obj.hom.hom then ⟨X, 𝟙 X⟩
    else extendElement p K X (missingElement p K X h)

private def successor (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [CharP K p] :
    CategoryTheory.SmallObject.SuccStruct (Stage p K) where
  X₀ := initialStage p K
  succ X := (successorArrow p K X).1
  toSucc X := (successorArrow p K X).2

private theorem missingElement_mem_successor (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [CharP K p] (X : Stage p K)
    (h : ¬Function.Surjective X.obj.hom.hom) :
    missingElement p K X h ∈ Set.range ((successor p K).succ X).obj.hom.hom := by
  change missingElement p K X h ∈ Set.range (successorArrow p K X).1.obj.hom.hom
  rw [successorArrow, dite_eq_right h]
  exact extendElement_mem_range p K X (missingElement p K X h)

private theorem point_range_mono {p : ℕ} {K : Type u} [Field K]
    {X Y : Stage p K} (f : X ⟶ Y) :
    Set.range X.obj.hom.hom ⊆ Set.range Y.obj.hom.hom := by
  rintro a ⟨x, rfl⟩
  refine ⟨f.hom.left.hom x, ?_⟩
  have hw : Y.obj.hom.hom.comp f.hom.left.hom = X.obj.hom.hom := by
    simpa only [CommRingCat.hom_comp] using
      congrArg (fun g : X.obj.left ⟶ CommRingCat.of K ↦ g.hom) (Over.w f.hom)
  exact RingHom.congr_fun hw x

private theorem iteration_surjective (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [CharP K p]
    (J : Type u) [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] [NoMaxOrder J]
    (hcard : Cardinal.mk K < Cardinal.mk J) :
    Function.Surjective ((successor p K).iteration J).obj.hom.hom := by
  classical
  let Φ := successor p K
  let F := Φ.iterationFunctor J
  let c := Φ.iterationCocone J
  change Function.Surjective c.pt.obj.hom.hom
  by_contra hfinal
  have hstage (i : J) : ¬Function.Surjective (F.obj i).obj.hom.hom := by
    intro hi
    apply hfinal
    intro a
    exact point_range_mono (c.ι.app i) (hi a)
  let pick : J → K := fun i ↦ missingElement p K (F.obj i) (hstage i)
  have hnot (i : J) : pick i ∉ Set.range (F.obj i).obj.hom.hom :=
    missingElement_not_mem_range p K (F.obj i) (hstage i)
  have hmem {i j : J} (hij : i < j) : pick i ∈ Set.range (F.obj j).obj.hom.hom := by
    have hsucc : pick i ∈ Set.range (Φ.succ (F.obj i)).obj.hom.hom :=
      missingElement_mem_successor p K (F.obj i) (hstage i)
    have hmax : ¬IsMax i := not_isMax_of_lt (exists_gt i).choose_spec
    have hsucc' : pick i ∈ Set.range (F.obj (Order.succ i)).obj.hom.hom :=
      point_range_mono (Φ.iterationFunctorObjSuccIso (J := J) i hmax).inv hsucc
    exact point_range_mono (F.map (homOfLE (Order.succ_le_of_lt hij))) hsucc'
  have hinj : Function.Injective pick := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hnot j (hij ▸ hmem hlt)
    · exact hnot i (hij.symm ▸ hmem hgt)
  exact hcard.2 (Cardinal.mk_le_of_injective hinj)

private def surjectiveStage (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [CharP K p] :
    {X : Stage p K // Function.Surjective X.obj.hom.hom} := by
  let κ : Cardinal.{u} := Order.succ (max Cardinal.aleph0 (Cardinal.mk K))
  let J := κ.ord.ToType
  let : Nonempty J := Cardinal.nonempty_ord_toType (Cardinal.succ_ne_zero _)
  let : OrderBot J := WellFoundedLT.toOrderBot J
  let : SuccOrder J := SuccOrder.ofLinearWellFoundedLT J
  let : NoMaxOrder J := Cardinal.noMaxOrder
    ((le_max_left Cardinal.aleph0 (Cardinal.mk K)).trans (Order.le_succ _))
  have hcard : Cardinal.mk K < Cardinal.mk J := by
    change Cardinal.mk K < Cardinal.mk κ.ord.ToType
    rw [Cardinal.mk_ord_toType]
    exact (le_max_right Cardinal.aleph0 (Cardinal.mk K)).trans_lt (Order.lt_succ _)
  exact ⟨(successor p K).iteration J, iteration_surjective p K J hcard⟩

/-- Every field of prime characteristic is the marked residue field of
an actual complete characteristic-zero DVR with that prime as uniformizer.
The construction allows arbitrary imperfect residue fields. -/
theorem _root_.IsDiscreteValuationRing.exists_complete_residuePoint
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [CharP K p] :
    ∃ (C : CommRingCat.{u}) (hD : IsDomain C),
      let _ : IsDomain C := hD
      ∃ hV : IsDiscreteValuationRing C,
        let _ : IsDiscreteValuationRing C := hV
        CharZero C ∧ IsAdicComplete (maximalIdeal C) C ∧ Irreducible (p : C) ∧
          ∃ g : C →+* K, Function.Surjective g ∧ RingHom.ker g = maximalIdeal C := by
  let X := (surjectiveStage p K).val
  let B := X.obj.left
  let : IsDomain B := X.property.domain
  let : IsDiscreteValuationRing B := X.property.dvr
  let : CharZero B := X.property.charZero
  let g : B →+* K := X.obj.hom.hom
  have hg : Function.Surjective g := (surjectiveStage p K).property
  have hker : RingHom.ker g = maximalIdeal B := X.property.kernel
  have hp : Irreducible (p : B) := X.property.uniformizer
  have hm : maximalIdeal B = Ideal.span {(p : B)} := hp.maximalIdeal_eq
  have hpreg : (p : B) ∈ B⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hp.ne_zero
  let C := AdicCompletion (Ideal.span {(p : B)}) B
  let : IsDomain C := AdicCompletion.isDomain_span_singleton B (p : B) hm hpreg
  let : IsDiscreteValuationRing C :=
    AdicCompletion.isDiscreteValuationRing_span_singleton B (p : B) hm hpreg
  let : IsLocalHom (algebraMap B C) :=
    AdicCompletion.algebraMap_isLocalHom_span_singleton B (p : B) hm
  have hcomplete : IsAdicComplete (maximalIdeal C) C :=
    AdicCompletion.isAdicComplete_maximalIdeal_span_singleton B (p : B) hm
  have hpC : Irreducible (p : C) := by
    simpa only [map_natCast] using
      AdicCompletion.irreducible_algebraMap_span_singleton B (p : B) hm hpreg
  have hchar : CharZero C := charZero_of_uniformizer_map p (algebraMap B C) hp hpC
  let eB : ResidueField B ≃+* K :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hg)
  let eC : ResidueField C ≃+* K :=
    (AdicCompletion.residueFieldEquivSpanSingleton B (p : B) hm).trans eB
  let s : C →+* K := eC.toRingHom.comp (residue C)
  have hcompletion (b : B) : s (algebraMap B C b) = g b := by
    change eB (AdicCompletion.residueFieldEquivSpanSingleton B (p : B) hm
      (residue C (algebraMap B C b))) = g b
    rw [← ResidueField.map_residue,
      AdicCompletion.residueFieldEquivSpanSingleton_map]
    rfl
  have hs : Function.Surjective s := by
    intro a
    obtain ⟨b, hb⟩ := hg a
    exact ⟨algebraMap B C b, (hcompletion b).trans hb⟩
  have hsker : RingHom.ker s = maximalIdeal C :=
    (RingHom.ker_comp_of_injective (residue C) (f := eC.toRingHom) eC.injective).trans ker_residue
  exact ⟨CommRingCat.of C, inferInstance, inferInstance, hchar, hcomplete, hpC, s, hs, hsker⟩

end CohenConstruction
