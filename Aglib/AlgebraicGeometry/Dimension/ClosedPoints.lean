/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NoetherNormalization.Dimension
public import Aglib.AlgebraicGeometry.Dimension.OpenCover
public import Aglib.AlgebraicGeometry.Stalk.Dimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Closed-point local dimension of integral field schemes

For an integral scheme locally of finite type over a field, every closed
point has actual local-ring dimension equal to the global topological
dimension. One affine chart uses the native finite-type domain
maximal-height theorem and its actual localization stalk. Nonempty affine
charts meet at a globally closed point by irreducibility and the native
Jacobson property, so the open-cover dimension bound globalizes the result.

No perfection, separability, properness or chosen normalization is an input.
The field map, affine-open maps and actual stalks are unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- A globally closed point in an actual affine chart of an integral
finite-type field scheme has local dimension equal to that chart ring's
Krull dimension. -/
theorem ringKrullDim_stalk_eq_of_closed_affineChart
    (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    {A : CommRingCat.{u}} (j : Spec A ⟶ X) [IsOpenImmersion j]
    (p : Spec A) (hp : IsClosed ({j p} : Set X)) :
    ringKrullDim (X.presheaf.stalk (j p)) = ringKrullDim A := by
  let : Nonempty (Spec A) := ⟨p⟩
  let : IsIntegral (Spec A) := isIntegral_of_isOpenImmersion j
  let : IsDomain A := (affine_isIntegral_iff A).mp inferInstance
  let φ : CommRingCat.of k ⟶ A := Spec.preimage (j ≫ f)
  let : Algebra k A := φ.hom.toAlgebra
  let : Algebra.FiniteType k A := by
    have hφ : LocallyOfFiniteType (Spec.map φ) := by
      rw [Spec.map_preimage]
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hφ
  have hpre : j ⁻¹' ({j p} : Set X) = {p} := by
    ext q
    change j q = j p ↔ q = p
    exact j.isOpenEmbedding.injective.eq_iff
  have hpclosed : IsClosed ({p} : Set (Spec A)) := by
    rw [← hpre]
    exact hp.preimage j.continuous
  let : p.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp hpclosed
  let : Algebra A ((Spec A).presheaf.stalk p) := StructureSheaf.stalkAlgebra A p
  let : IsLocalization.AtPrime ((Spec A).presheaf.stalk p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A p
  have hdim : ringKrullDim ((Spec A).presheaf.stalk p) = ringKrullDim A :=
    (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal ((Spec A).presheaf.stalk p)).trans
      (Ideal.height_eq_ringKrullDim_of_finiteType_field k A p.asIdeal)
  rw [ringKrullDim_stalk_eq_coheight] at hdim ⊢
  rwa [← coheight_eq_of_isOpenImmersion j] at hdim

/-- Every closed point of an integral scheme locally of finite type over
a field has actual local-ring dimension equal to the original scheme's
global topological Krull dimension. -/
theorem ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed
    (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = topologicalKrullDim X := by
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  let C := X.affineOpenCover
  obtain ⟨i₀, p₀, hp₀⟩ := C.openCover.exists_eq x
  let a := C.f i₀
  let : IsOpenImmersion a := C.map_prop i₀
  have ha₀ : a p₀ = x := hp₀
  have href : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (C.X i₀) := by
    have hclosed : IsClosed ({a p₀} : Set X) := by rwa [ha₀]
    exact (congrArg (fun z : X => ringKrullDim (X.presheaf.stalk z)) ha₀).symm.trans
      (ringKrullDim_stalk_eq_of_closed_affineChart k f a p₀ hclosed)
  apply le_antisymm
  · rw [topologicalKrullDim_eq_iSup_stalk]
    exact le_iSup (fun y : X => ringKrullDim (X.presheaf.stalk y)) x
  · apply topologicalKrullDim_le_of_openCover C.openCover
    intro i
    let j := C.f i
    let : IsOpenImmersion j := C.map_prop i
    by_cases hnon : Nonempty (Spec (C.X i))
    · obtain ⟨p⟩ := hnon
      have haopen : IsOpen (Set.range a) := a.isOpenEmbedding.isOpen_range
      have hjopen : IsOpen (Set.range j) := j.isOpenEmbedding.isOpen_range
      have hmeet : (Set.range a ∩ Set.range j).Nonempty :=
        nonempty_preirreducible_inter haopen hjopen ⟨a p₀, p₀, rfl⟩ ⟨j p, p, rfl⟩
      obtain ⟨y, hy, hyclosed⟩ :=
        nonempty_inter_closedPoints hmeet (haopen.inter hjopen).isLocallyClosed
      obtain ⟨pa, hpa⟩ := hy.1
      obtain ⟨pj, hpj⟩ := hy.2
      have haY : ringKrullDim (X.presheaf.stalk y) = ringKrullDim (C.X i₀) := by
        have hclosed : IsClosed ({a pa} : Set X) := by rwa [hpa]
        exact (congrArg (fun z : X => ringKrullDim (X.presheaf.stalk z)) hpa).symm.trans
          (ringKrullDim_stalk_eq_of_closed_affineChart k f a pa hclosed)
      have hjY : ringKrullDim (X.presheaf.stalk y) = ringKrullDim (C.X i) := by
        have hclosed : IsClosed ({j pj} : Set X) := by rwa [hpj]
        exact (congrArg (fun z : X => ringKrullDim (X.presheaf.stalk z)) hpj).symm.trans
          (ringKrullDim_stalk_eq_of_closed_affineChart k f j pj hclosed)
      apply le_of_eq
      calc
        topologicalKrullDim (C.openCover.X i) = ringKrullDim (C.X i) :=
          PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (C.X i)
        _ = ringKrullDim (X.presheaf.stalk y) := hjY.symm
        _ = ringKrullDim (C.X i₀) := haY
        _ = ringKrullDim (X.presheaf.stalk x) := href.symm
    · rw [topologicalKrullDim_eq_iSup_stalk]
      exact iSup_le fun y => (hnon ⟨y⟩).elim

end AlgebraicGeometry.Scheme
