/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.GlobalSections
public import Aglib.AlgebraicGeometry.Geometrically.Integral.GlobalSections
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality
public import Aglib.AlgebraicGeometry.Properties.Normal.Components
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.Topology.Connected.Clopen

/-!
# Geometric connectedness of the actual pointed smooth proper field curve

The original rational section identifies the integral proper scheme's actual
constant ring with the base field. The proved degree-zero field base-change
map preserves that identification. Sheaf gluing then excludes a nontrivial
clopen decomposition after every field extension, using its associated
idempotent global section. No geometric-connectedness or cohomology theorem
family is an input. The unrestricted legacy connected-pointed-scheme family
is outside this pointwise smooth proper Noetherian statement.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u
attribute [local instance] globalSectionsModule

private theorem connected_of_domain_globalSections
    {K : Type u} [Field K] (X : FScheme K) [Nonempty X.left]
    [IsDomain Γ(X.left, ⊤)] : ConnectedSpace X.left := by
  classical
  apply connectedSpace_iff_clopen.mpr
  refine ⟨inferInstance, ?_⟩
  intro S hS
  by_cases hS0 : S = ∅
  · exact Or.inl hS0
  by_cases hS1 : S = Set.univ
  · exact Or.inr hS1
  let U : ULift.{u} Bool → X.left.Opens := fun i =>
    if i.down then ⟨S, hS.2⟩ else ⟨Sᶜ, hS.1.isOpen_compl⟩
  have hcover : iSup U = ⊤ := by
    apply top_unique
    intro x _
    rw [Opens.mem_iSup]
    by_cases hx : x ∈ S
    · exact ⟨⟨true⟩, by simpa [U] using hx⟩
    · exact ⟨⟨false⟩, by simpa [U] using hx⟩
  have hinter : U ⟨false⟩ ⊓ U ⟨true⟩ = ⊥ := by
    apply SetLike.coe_injective
    ext x
    simp [U]
  let a : ∀ i, Γ(X.left, U i) := fun i => if i.down then 1 else 0
  have hcompatible : TopCat.Presheaf.IsCompatible X.left.presheaf U a := by
    rintro ⟨i⟩ ⟨j⟩
    cases i <;> cases j
    · rfl
    · have : Subsingleton Γ(X.left, U ⟨false⟩ ⊓ U ⟨true⟩) := by
        rw [hinter]
        infer_instance
      exact Subsingleton.elim _ _
    · have : Subsingleton Γ(X.left, U ⟨true⟩ ⊓ U ⟨false⟩) := by
        rw [inf_comm, hinter]
        infer_instance
      exact Subsingleton.elim _ _
    · rfl
  have hd : Cohomology.coverSectionsDifference X U a = 0 := by
    funext p
    exact sub_eq_zero.mpr (hcompatible p.1 p.2)
  obtain ⟨e, heq⟩ := (Cohomology.globalSectionsToCover_exact X U hcover a).mp hd
  have he (i) : X.left.presheaf.map (homOfLE le_top).op e = a i := congrFun heq i
  have hid : e * e = e := by
    apply Cohomology.globalSectionsToCover_injective X U hcover
    funext i
    change X.left.presheaf.map (homOfLE le_top).op (e * e) =
      X.left.presheaf.map (homOfLE le_top).op e
    rw [map_mul, he i]
    rcases i with ⟨i⟩
    cases i <;> simp [a]
  have hneU : Nonempty (U ⟨true⟩) := by
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hS0
    exact ⟨⟨x, by simpa [U] using hx⟩⟩
  have hneV : Nonempty (U ⟨false⟩) := by
    obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem S).mp hS1
    exact ⟨⟨x, by simpa [U] using hx⟩⟩
  let : Nontrivial Γ(X.left, U ⟨true⟩) := Scheme.component_nontrivial _ _
  let : Nontrivial Γ(X.left, U ⟨false⟩) := Scheme.component_nontrivial _ _
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hid with h | h
  · have hh := he ⟨true⟩
    simp [h, a] at hh
  · have hh := he ⟨false⟩
    simp [h, a] at hh

private def sectionEvaluation {K : Type u} [Field K] (X : FScheme K)
    (o : Spec (.of K) ⟶ X.left) : Γ(X.left, ⊤) →+* K :=
  (Scheme.ΓSpecIso (.of K)).hom.hom.comp o.appTop.hom

private theorem sectionEvaluation_constants {K : Type u} [Field K] (X : FScheme K)
    (o : Spec (.of K) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _) :
    (sectionEvaluation X o).comp (constants X) = RingHom.id K := by
  have hc : ((Scheme.ΓSpecIso (.of K)).inv ≫ X.hom.appTop) ≫
      (o.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom) = 𝟙 (CommRingCat.of K) := by
    calc
      _ = (Scheme.ΓSpecIso (.of K)).inv ≫ (X.hom.appTop ≫ o.appTop) ≫
          (Scheme.ΓSpecIso (.of K)).hom := by simp only [Category.assoc]
      _ = _ := by rw [← Scheme.Hom.comp_appTop, ho]; simp
  exact congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of K => f.hom) hc

private theorem constants_bijective_of_pointed_proper_integral
    {K : Type u} [Field K] (X : FScheme K) [IsProper X.hom] [IsIntegral X.left]
    (o : Spec (.of K) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _) :
    Function.Bijective (constants X) := by
  let : Algebra K Γ(X.left, ⊤) := (constants X).toAlgebra
  let : Algebra.IsIntegral K Γ(X.left, ⊤) := ⟨constants_isIntegral_of_proper X⟩
  let : Field Γ(X.left, ⊤) :=
    (isField_of_isIntegral_of_isField' (Field.toIsField K)).toField
  refine ⟨(constants X).injective, ?_⟩
  intro a
  refine ⟨sectionEvaluation X o a, ?_⟩
  apply (sectionEvaluation X o).injective
  exact RingHom.congr_fun (sectionEvaluation_constants X o ho) _

private theorem constants_surjective_fieldBaseChange
    {K : Type u} [Field K] (L : Type u) [Field L] [Algebra K L]
    (X : FScheme K) [QuasiCompact X.hom] [IsSeparated X.hom]
    (hc : Function.Surjective (constants X)) :
    Function.Surjective (constants (Cohomology.fieldBaseChange L X)) := by
  intro a
  obtain ⟨t, rfl⟩ :=
    (Cohomology.structureSectionsBaseChangeMap_bijective_of_quasiCompact_of_isSeparated L X).2 a
  induction t using TensorProduct.inductionOn with
  | add t v ht hv =>
    obtain ⟨b, hb⟩ := ht
    obtain ⟨c, hc⟩ := hv
    exact ⟨b + c, by simp only [map_add, hb, hc]⟩
  | tmul l a =>
    obtain ⟨b, rfl⟩ := hc a
    refine ⟨l * algebraMap K L b, ?_⟩
    rw [Cohomology.structureSectionsBaseChangeMap_tmul]
    calc
      _ = l • constants (Cohomology.fieldBaseChange L X) (algebraMap K L b) := by
        change constants (Cohomology.fieldBaseChange L X) (l * algebraMap K L b) =
          constants (Cohomology.fieldBaseChange L X) l *
            constants (Cohomology.fieldBaseChange L X) (algebraMap K L b)
        exact map_mul _ _ _
      _ = _ := congrArg (fun z : Γ((Cohomology.fieldBaseChange L X).left, ⊤) ↦ l • z)
        (Cohomology.map_constants_of_baseMap (algebraMap K L)
          (Cohomology.fieldBaseChange L X) X (pullback.fst _ _) pullback.condition b).symm

/-- A connected smooth proper Noetherian field curve with its actual rational
section is geometrically connected. The conclusion concerns this same structure
map and section; no `Curve.Properties` or unrestricted theorem family is used. -/
theorem geometricallyConnected_of_pointed_proper_smooth_curve
    {K : Type u} [Field K] {X : Scheme.{u}} (q : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 1 q] [IsProper q] [hN : IsNoetherian X] [ConnectedSpace X]
    (o : Spec (.of K) ⟶ X) (ho : o ≫ q = 𝟙 _) : GeometricallyConnected q := by
  let : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  let : IsLocallyNoetherian X := hN.toIsLocallyNoetherian
  let : IsIntegral X :=
    isIntegral_of_connected_normalStalks_actual X (smoothFieldNormality K X q inferInstance)
  let Y : FScheme K := Over.mk q
  let : IsProper Y.hom := by change IsProper q; infer_instance
  let : IsIntegral Y.left := by change IsIntegral X; infer_instance
  have hc : Function.Bijective (constants Y) :=
    constants_bijective_of_pointed_proper_integral Y o ho
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun Z : Scheme.{u} => ConnectedSpace Z) (R := K) (f := q)).mpr
  intro L _ _
  let s := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let Z := Cohomology.fieldBaseChange L Y
  let oL : Spec (.of L) ⟶ Z.left := pullback.lift (s ≫ o) (𝟙 _) (by
    change (s ≫ o) ≫ q = (𝟙 _) ≫ s
    simp only [Category.assoc, ho, Category.comp_id, Category.id_comp])
  let : Nonempty Z.left := ⟨oL (default : Spec (.of L))⟩
  let : Nonempty (⊤ : Z.left.Opens) := ⟨⟨oL (default : Spec (.of L)), trivial⟩⟩
  let : Nontrivial Γ(Z.left, ⊤) := Scheme.component_nontrivial _ _
  have hcL : Function.Bijective (constants Z) :=
    ⟨(constants Z).injective, constants_surjective_fieldBaseChange L Y hc.2⟩
  let e := RingEquiv.ofBijective (constants Z) hcL
  let : IsDomain Γ(Z.left, ⊤) := MulEquiv.isDomain L e.symm.toMulEquiv
  exact connected_of_domain_globalSections Z

end AlgebraicGeometry.Scheme
