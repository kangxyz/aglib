/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.Etale
public import Aglib.AlgebraicGeometry.AffineScheme.AlgebraMapTriangles
public import Aglib.AlgebraicGeometry.AffineScheme.BaseChangeCoordinates
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Basic
public import Aglib.AlgebraicGeometry.Spec.ResidueFiber

/-!
# Sections of finite etale covers from their residue points

A residue-field-valued point of the actual closed fibre of a finite etale cover of a Henselian
local ring lifts to a unique section of that same cover. The construction
preserves the original structural map and the literal residue-spectrum map.
No Noetherian, DVR, excellence or completeness assumption is needed.

This section-lifting result does not assert an equivalence of finite-etale
categories, and it does not inhabit `ProperHenselianComparison`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale.HenselianResidue

universe u
variable (R : Type u) [CommRing R] [HenselianLocalRing R]

private theorem existsUnique_affine_section
    (A : Type u) [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (t : Spec (.of (IsLocalRing.ResidueField R)) ⟶ Spec (.of A))
    (ht : t ≫ Spec.algebraMap R A = Scheme.LocalRing.residueSpecMap R) :
    ∃! s : Spec (.of R) ⟶ Spec (.of A),
      s ≫ Spec.algebraMap R A = 𝟙 _ ∧ Scheme.LocalRing.residueSpecMap R ≫ s = t := by
  have hself : Spec.algebraMap R R = 𝟙 (Spec (.of R)) := by
    simp [Spec.algebraMap]
  have hres : Spec.algebraMap R (IsLocalRing.ResidueField R) =
      Scheme.LocalRing.residueSpecMap R := rfl
  let a : A →ₐ[R] IsLocalRing.ResidueField R :=
    Spec.homEquivAlgHom ⟨t, by simpa only [hres] using ht⟩
  have ha : Spec.map (CommRingCat.ofHom a.toRingHom) = t :=
    congrArg Subtype.val (Spec.homEquivAlgHom.symm_apply_apply
      ⟨t, by simpa only [hres] using ht⟩)
  obtain ⟨b, hb⟩ := (HenselianLocalRing.residue_comp_bijective_of_etale R A).2 a
  let s : Spec (.of R) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom b.toRingHom)
  have hs : Scheme.LocalRing.residueSpecMap R ≫ s = t := by
    calc
      _ = Spec.map (CommRingCat.ofHom a.toRingHom) := by
        dsimp only [Scheme.LocalRing.residueSpecMap, s]
        rw [← Spec.map_comp]
        congr 1
        apply CommRingCat.hom_ext
        exact congrArg AlgHom.toRingHom hb
      _ = t := ha
  refine ⟨s, ⟨?_, hs⟩, ?_⟩
  · simpa only [hself] using Spec.map_algHom_algebraMap b
  · intro q hq
    let c : A →ₐ[R] R :=
      Spec.homEquivAlgHom ⟨q, by simpa only [hself] using hq.1⟩
    have hc : Spec.map (CommRingCat.ofHom c.toRingHom) = q :=
      congrArg Subtype.val (Spec.homEquivAlgHom.symm_apply_apply
        ⟨q, by simpa only [hself] using hq.1⟩)
    have hca : (Algebra.ofId R (IsLocalRing.ResidueField R)).comp c = a := by
      have he : CommRingCat.ofHom
          (((Algebra.ofId R (IsLocalRing.ResidueField R)).comp c).toRingHom) =
          CommRingCat.ofHom a.toRingHom := by
        apply Spec.map_injective
        calc
          _ = Scheme.LocalRing.residueSpecMap R ≫ q := by
            rw [← hc]
            rw [← Spec.map_comp]
            rfl
          _ = t := hq.2
          _ = Spec.map (CommRingCat.ofHom a.toRingHom) := ha.symm
      apply AlgHom.ext
      intro x
      exact congrArg
        (fun f : CommRingCat.of A ⟶ CommRingCat.of (IsLocalRing.ResidueField R) => f.hom x) he
    have hcb : c = b := (HenselianLocalRing.residue_comp_bijective_of_etale R A).1
      (hca.trans hb.symm)
    calc
      q = Spec.map (CommRingCat.ofHom c.toRingHom) := hc.symm
      _ = s := by rw [hcb]

/-- Every actual residue point of a finite etale scheme over a Henselian local
ring has a unique section lifting it, with both original triangles. -/
theorem existsUnique_section_lift {X : Scheme.{u}} (p : X ⟶ Spec (.of R))
    [IsFinite p] [Etale p]
    (t : Spec (.of (IsLocalRing.ResidueField R)) ⟶ X)
    (ht : t ≫ p = Scheme.LocalRing.residueSpecMap R) :
    ∃! s : Spec (.of R) ⟶ X,
      s ≫ p = 𝟙 _ ∧ Scheme.LocalRing.residueSpecMap R ≫ s = t := by
  let : IsAffine X := isAffine_of_isAffineHom p
  let : IsAffine (Over.mk p).left := inferInstanceAs (IsAffine X)
  let A : Type u := Γ(X, ⊤)
  let : CommRing A := inferInstanceAs (CommRing Γ(X, ⊤))
  let : Algebra R A := Scheme.AffineBaseChange.coordinateAlgebra R (Over.mk p)
  have hcoord : X.isoSpec.inv ≫ p = Spec.algebraMap R A :=
    Scheme.AffineBaseChange.isoSpec_inv_over R (Over.mk p)
  have hcoord' : X.isoSpec.hom ≫ Spec.algebraMap R A = p := by
    rw [← hcoord]
    simp
  have : Algebra.Etale R A := by
    have he : Etale (Spec.algebraMap R A) := by
      rw [← hcoord]
      infer_instance
    exact RingHom.etale_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Etale.{u})).mp he)
  let t' : Spec (.of (IsLocalRing.ResidueField R)) ⟶ Spec (.of A) := t ≫ X.isoSpec.hom
  have ht' : t' ≫ Spec.algebraMap R A = Scheme.LocalRing.residueSpecMap R := by
    dsimp only [t']
    rw [Category.assoc, hcoord', ht]
  obtain ⟨s, hs, hu⟩ := existsUnique_affine_section R A t' ht'
  refine ⟨s ≫ X.isoSpec.inv, ⟨?_, ?_⟩, ?_⟩
  · simpa only [Category.assoc, hcoord] using hs.1
  · rw [← Category.assoc, hs.2]
    simp only [t', Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · intro q hq
    have hqs : q ≫ X.isoSpec.hom = s := hu (q ≫ X.isoSpec.hom)
      ⟨by rw [Category.assoc, hcoord', hq.1], by rw [← Category.assoc, hq.2]⟩
    calc
      q = (q ≫ X.isoSpec.hom) ≫ X.isoSpec.inv := by simp
      _ = s ≫ X.isoSpec.inv := by rw [hqs]

/-- The chosen section lifts the specified residue point of the same cover. -/
def liftResiduePoint {X : Scheme.{u}} (p : X ⟶ Spec (.of R))
    [IsFinite p] [Etale p]
    (t : Spec (.of (IsLocalRing.ResidueField R)) ⟶ X)
    (ht : t ≫ p = Scheme.LocalRing.residueSpecMap R) : Spec (.of R) ⟶ X :=
  Classical.choose (existsUnique_section_lift R p t ht)

@[reassoc (attr := simp)] theorem liftResiduePoint_over {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) [IsFinite p] [Etale p]
    (t : Spec (.of (IsLocalRing.ResidueField R)) ⟶ X)
    (ht : t ≫ p = Scheme.LocalRing.residueSpecMap R) :
    liftResiduePoint R p t ht ≫ p = 𝟙 _ :=
  (Classical.choose_spec (existsUnique_section_lift R p t ht)).1.1

@[reassoc (attr := simp)] theorem liftResiduePoint_restrict {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) [IsFinite p] [Etale p]
    (t : Spec (.of (IsLocalRing.ResidueField R)) ⟶ X)
    (ht : t ≫ p = Scheme.LocalRing.residueSpecMap R) :
    Scheme.LocalRing.residueSpecMap R ≫ liftResiduePoint R p t ht = t :=
  (Classical.choose_spec (existsUnique_section_lift R p t ht)).1.2

theorem liftResiduePoint_unique {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) [IsFinite p] [Etale p]
    (t : Spec (.of (IsLocalRing.ResidueField R)) ⟶ X)
    (ht : t ≫ p = Scheme.LocalRing.residueSpecMap R)
    (s : Spec (.of R) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (hst : Scheme.LocalRing.residueSpecMap R ≫ s = t) :
    s = liftResiduePoint R p t ht :=
  (Classical.choose_spec (existsUnique_section_lift R p t ht)).2 s ⟨hs, hst⟩

end AlgebraicGeometry.Scheme.FiniteEtale.HenselianResidue
