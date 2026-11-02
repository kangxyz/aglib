/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.RegularScheme
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
public import Aglib.AlgebraicGeometry.Morphisms.FormallyUnramified.Immersions
public import Aglib.AlgebraicGeometry.Geometrically.Connected.RationalPoint
public import Aglib.AlgebraicGeometry.Curves.Projectivity.Embedding
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Aglib.AlgebraicGeometry.Normalization.FiniteTypeField
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.RadicalSubscheme
public import Aglib.AlgebraicGeometry.Dimension.Finite
public import Aglib.AlgebraicGeometry.Stalk.Dimension
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Limits
public import Aglib.AlgebraicGeometry.Morphisms.Finite.Coproduct

/-! # Normal component covers of proper curves over an algebraically closed field

Each original irreducible closed component is given its radical subscheme
structure and normalized in its own function field. These actual finite maps
jointly cover the original scheme, including its nonreduced case. Every source
is internally shown to be either a point or a pointed smooth projective curve.
No normality, Nagata, smoothness or section certificate is required of the input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Normalization

/-- Actual normal local rings of a dimension-at-most-one locally Noetherian scheme
are regular; no smoothness premise is introduced. -/
private theorem regularStalks_of_normal_dim_le_one
    (C : Scheme.{u}) [IsLocallyNoetherian C]
    (hN : Scheme.NormalStalks C) (hd : topologicalKrullDim C ≤ 1) :
    Scheme.RegularStalks C := by
  intro x
  let R := C.presheaf.stalk x
  let : IsDomain R := (hN x).1
  let : IsIntegrallyClosed R := (hN x).2
  have hR : ringKrullDim R ≤ 1 := by
    calc
      ringKrullDim R ≤ ⨆ y : C, ringKrullDim (C.presheaf.stalk y) :=
        le_iSup (fun y : C => ringKrullDim (C.presheaf.stalk y)) x
      _ = topologicalKrullDim C := (Scheme.topologicalKrullDim_eq_iSup_stalk C).symm
      _ ≤ 1 := hd
  let : Ring.DimensionLEOne R := {
    maximalOfPrime := by
      intro I hI hprime
      apply (PrimeSpectrum.isMax_iff (x := ⟨I, hprime⟩)).mp
      apply (Order.krullDim_le_one_iff_forall_isMax.mp hR) ⟨I, hprime⟩
      intro heq
      exact hI (congrArg PrimeSpectrum.asIdeal heq) }
  let : IsDedekindDomain R := {
    toIsDomain := inferInstance
    toIsDedekindRing := {
      toIsNoetherian := inferInstance
      toDimensionLEOne := inferInstance
      toIsIntegralClosure := inferInstance } }
  exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing R

/-- The original normal integral proper field scheme is either a point or an
actual pointed smooth projective curve. The point, branch and embedding are
constructed internally on the original objects. -/
private theorem normal_dim_le_one_point_or_curve
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (C : Scheme.{u}) [IsIntegral C] (p : C ⟶ Spec (.of Ω)) [IsProper p]
    (hN : Scheme.NormalStalks C) (hd : topologicalKrullDim C ≤ 1) :
    ∃ o : Spec (.of Ω) ⟶ C, o ≫ p = 𝟙 _ ∧
      (IsIso p ∨
        (Properties (Over.mk p) ∧
          ∃ (N : ℕ) (i : C ⟶ ProjectiveSpace Ω (ULift.{u} (Fin (N + 1)))),
            IsClosedImmersion i ∧
              i ≫ ProjectiveSpace.toSpec Ω (ULift.{u} (Fin (N + 1))) = p)) := by
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian p
  let : Smooth p := Smooth.of_regularStalks_of_perfectField Ω p
    (regularStalks_of_normal_dim_le_one C hN hd)
  let : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨x⟩ := (inferInstance : Nonempty C)
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := Set.univ) ⟨x, trivial⟩
    isOpen_univ.isLocallyClosed
  let o := pointOfClosedPoint p z hz
  have ho : o ≫ p = 𝟙 _ := pointOfClosedPoint_comp p z hz
  refine ⟨o, ho, ?_⟩
  obtain ⟨n, hn⟩ := Scheme.exists_smoothOfRelativeDimension_of_preconnected p x
  let : SmoothOfRelativeDimension n p := hn
  have hdim : topologicalKrullDim C = n :=
    Scheme.smoothFieldDimension Ω C p n hn inferInstance
  have hnle : n ≤ 1 := by exact_mod_cast (hdim.symm.trans_le hd)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hnle with hzero | hone
  · subst n
    left
    let : Etale p := (Etale.iff_smoothOfRelativeDimension_zero p).mpr hn
    let : IsOpenImmersion o := IsOpenImmersion.of_section_formallyUnramified o p ho
    let : IsClosedImmersion o := isClosedImmersion_of_comp_eq_id p o ho
    have hdense : DenseRange o := o.isOpenMap.denseRange_of_isPreirreducibleSpace
    have hrange : Set.range o = Set.univ := by
      rw [← o.isClosedEmbedding.isClosed_range.closure_eq]
      exact hdense.closure_range
    let : Surjective o := ⟨Set.range_eq_univ.mp hrange⟩
    let : IsIso o := isIso_of_isClosedImmersion_of_surjective o
    let : IsIso (o ≫ p) := by rw [ho]; infer_instance
    exact IsIso.of_isIso_comp_left (f := o) p
  · subst n
    right
    have hconn : GeometricallyConnected p :=
      Scheme.Geometrically.geometricallyConnected_of_connectedSpace_of_section p o ho
    let : IsProper (Over.mk p).hom := ‹IsProper p›
    let : IsIntegral (Over.mk p).left := ‹IsIntegral C›
    refine ⟨⟨hn, inferInstance, hconn⟩, ?_⟩
    exact Projectivity.exists_projectiveEmbedding_of_normal (Over.mk p) hN hdim

/-- The normalization of the original reduced closed component is finite and
has precisely that component as its image. -/
private theorem exists_normal_component
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (X : Scheme.{u}) (p : X ⟶ Spec (.of Ω)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1)
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    ∃ (C : Scheme.{u}) (ν : C ⟶ X), IsFinite ν ∧ Set.range ν = Z ∧
      Scheme.NormalStalks C ∧
      ∃ o : Spec (.of Ω) ⟶ C, o ≫ (ν ≫ p) = 𝟙 _ ∧
        (IsIso (ν ≫ p) ∨
          (Properties (Over.mk (ν ≫ p)) ∧
            ∃ (N : ℕ) (i : C ⟶ ProjectiveSpace Ω (ULift.{u} (Fin (N + 1)))),
              IsClosedImmersion i ∧
                i ≫ ProjectiveSpace.toSpec Ω (ULift.{u} (Fin (N + 1))) = ν ≫ p)) := by
  let Zc : TopologicalSpace.Closeds X :=
    ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Zc
  have hI : I.radical = I := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support]
    rfl
  let W := I.subscheme
  let : IsReduced W := Scheme.IdealSheafData.subscheme_reduced_of_radical I hI
  let : IrreducibleSpace W := by
    change IrreducibleSpace Z
    exact Subtype.irreducibleSpace hZ.1
  let : IsIntegral W := isIntegral_of_irreducibleSpace_of_isReduced W
  let j : W ⟶ X := I.subschemeι
  let : IsClosedImmersion j := inferInstanceAs (IsClosedImmersion I.subschemeι)
  let γ := W.fromSpecStalk (genericPoint W)
  let C := γ.normalization
  let a : C ⟶ W := γ.fromNormalization
  let : IsFinite a := Scheme.genericNormalization_isFinite_of_finiteType_field Ω W (j ≫ p)
  let : IsDominant a := Scheme.genericNormalization_isDominant W
  let : Surjective a :=
    surjective_of_isDominant_of_isClosed_range a a.isClosedMap.isClosed_range
  let ν : C ⟶ X := a ≫ j
  let : IsIntegral C := inferInstanceAs (IsIntegral γ.normalization)
  have hN : Scheme.NormalStalks C := Scheme.genericNormalization_normalStalks W
  have hdim : topologicalKrullDim C ≤ 1 :=
    ν.topologicalKrullDim_le_of_isFinite.trans hd
  have hr : Set.range ν = Z := by
    change Set.range (j ∘ a) = Z
    rw [Set.range_comp, a.surjective.range_eq, Set.image_univ]
    exact I.range_subschemeι
  refine ⟨C, ν, inferInstance, hr, hN, ?_⟩
  exact normal_dim_le_one_point_or_curve Ω C (ν ≫ p) hN hdim

/-- A finite family of actual finite normalization maps covers a proper
algebraically closed field scheme of dimension at most one. The indexing set is
literally its irreducible components; the empty scheme yields the empty family.
Every normal source is internally classified as a point or a pointed smooth
projective geometrically connected curve. -/
theorem exists_finite_normal_component_cover
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (X : Scheme.{u}) (p : X ⟶ Spec (.of Ω)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) :
    Finite ↥(irreducibleComponents X) ∧
      ∃ (C : ↥(irreducibleComponents X) → Scheme.{u}) (ν : ∀ z, C z ⟶ X),
        (∀ z, IsFinite (ν z)) ∧
        (∀ z, Set.range (ν z) = z.1) ∧
        IsFinite (Sigma.desc ν) ∧ Surjective (Sigma.desc ν) ∧
        ∀ z, Scheme.NormalStalks (C z) ∧
          ∃ o : Spec (.of Ω) ⟶ C z, o ≫ (ν z ≫ p) = 𝟙 _ ∧
            (IsIso (ν z ≫ p) ∨
              (Properties (Over.mk (ν z ≫ p)) ∧
                ∃ (N : ℕ) (i : C z ⟶ ProjectiveSpace Ω (ULift.{u} (Fin (N + 1)))),
                  IsClosedImmersion i ∧
                    i ≫ ProjectiveSpace.toSpec Ω (ULift.{u} (Fin (N + 1))) = ν z ≫ p)) := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := ⟨⟩
  have hf : Finite ↥(irreducibleComponents X) :=
    (finite_irreducibleComponents_of_isNoetherian (X := X)).to_subtype
  choose C ν hfin hr hnormal hmodel using
    fun z : ↥(irreducibleComponents X) => exists_normal_component Ω X p hd z.1 z.2
  let : Finite ↥(irreducibleComponents X) := hf
  let : ∀ z, IsFinite (ν z) := hfin
  have htotal : IsFinite (Sigma.desc ν) := Scheme.Hom.isFinite_sigmaDesc C X ν
  have hsurj : Surjective (Sigma.desc ν) := by
    constructor
    intro x
    let z : ↥(irreducibleComponents X) :=
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    have hx : x ∈ Set.range (ν z) := by
      rw [hr z]
      exact mem_irreducibleComponent
    obtain ⟨y, hy⟩ := hx
    refine ⟨Sigma.ι C z y, ?_⟩
    have he := congrArg (fun f : C z ⟶ X => f y) (Sigma.ι_comp_desc ν z)
    exact he.trans hy
  exact ⟨hf, C, ν, hfin, hr, htotal, hsurj, fun z => ⟨hnormal z, hmodel z⟩⟩

end AlgebraicGeometry.Scheme.OverField.Curve.Normalization
