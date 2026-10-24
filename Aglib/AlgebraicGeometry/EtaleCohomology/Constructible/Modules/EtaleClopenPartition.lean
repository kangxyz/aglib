/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.ReducedPartition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.DescentEtale
public import Aglib.AlgebraicGeometry.Morphisms.Immersion.ReducedFactor

/-! # Whole-source module restrictions on geometric etale partitions

Clopen preimages of the original module strata form an actual open cover of
each reduced pulled-back source. Their original maps factor through the
original strata, so finite-type local constancy holds on the whole source.
Actual common refinements give the same assertion for a finite family of
affine etale charts, without changing the coefficient universe or ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u r v

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R]

/-- Finiteness and local constancy on an entire pulled-back source survive
an actual refinement through the literal source comparison map. -/
theorem FiniteLocallyClosedPartition.Refinement.isFiniteTypeLocallyConstant_pullback
    {X Y : Scheme.{u}} {q p : FiniteLocallyClosedPartition X} (r : q.Refinement p)
    (f : Y ⟶ X) (F : Modules.ModuleSheaf R Y)
    (hF : ∀ i, Modules.IsFiniteTypeLocallyConstant
      ((Modules.moduleInverseImage R (pullback.fst f (p.inclusion i))).obj F)) :
    ∀ i, Modules.IsFiniteTypeLocallyConstant
      ((Modules.moduleInverseImage R (pullback.fst f (q.inclusion i))).obj F) := by
  intro i
  rw [← r.pullbackMap_fst f i]
  exact (Modules.isFiniteTypeLocallyConstant_iff_of_iso
    ((Modules.moduleInverseImageComp R (pullback.fst f (p.inclusion (r.indexMap i)))
      (r.pullbackMap f i)).app F)).mpr
    (Modules.isFiniteTypeLocallyConstant_pullback (r.pullbackMap f i) (hF (r.indexMap i)))

namespace Modules

/-- A reduced source with clopen preimages of an original module partition
has finite-type locally constant original inverse image. -/
theorem isFiniteTypeLocallyConstant_pullback_of_clopen_partition
    {Y Z : Scheme.{u}} [IsReduced Z] (a : Z ⟶ Y) {F : ModuleSheaf R Y}
    (q : ConstructiblePartition F)
    (hq : ∀ i, IsClopen (a ⁻¹' Set.range (q.inclusion i))) :
    IsFiniteTypeLocallyConstant ((moduleInverseImage R a).obj F) := by
  let V (i : Fin q.count) : Z.Opens := ⟨a ⁻¹' Set.range (q.inclusion i), (hq i).isOpen⟩
  let U (i : ULift.{u} (Fin q.count)) : Z.Etale := Scheme.Etale.mk (V i.down).ι
  refine isFiniteTypeLocallyConstant_of_etaleCover U ?_
    ((moduleInverseImage R a).obj F) ?_
  · intro z
    obtain ⟨i, y, hy⟩ := q.covers (a z)
    exact ⟨⟨i⟩, ⟨z, ⟨y, hy⟩⟩, rfl⟩
  · intro i
    have : IsReduced (V i.down).toScheme := isReduced_of_isOpenImmersion (V i.down).ι
    have := q.immersion i.down
    have hsub : Set.range ((V i.down).ι ≫ a) ⊆ Set.range (q.inclusion i.down) := by
      rintro _ ⟨z, rfl⟩
      exact z.property
    let b := liftReducedToImmersion (q.inclusion i.down) ((V i.down).ι ≫ a) hsub
    have hb : b ≫ q.inclusion i.down = (V i.down).ι ≫ a :=
      liftReducedToImmersion_fac _ _ _
    change IsFiniteTypeLocallyConstant
      ((moduleInverseImage R (V i.down).ι).obj ((moduleInverseImage R a).obj F))
    apply (isFiniteTypeLocallyConstant_iff_of_iso
      ((moduleInverseImageComp R a (V i.down).ι).app F)).mp
    rw [← hb]
    exact (isFiniteTypeLocallyConstant_iff_of_iso
      ((moduleInverseImageComp R (q.inclusion i.down) b).app F)).mpr
      (isFiniteTypeLocallyConstant_pullback b (q.locally_constant i.down))

/-- An original constructible module on an affine etale source is
finite-type locally constant on the entire source over each part of an
actual finite base partition. -/
theorem exists_wholeSource_partition_of_isAffineHom_of_etale
    {X Y : Scheme.{u}} [IsAffine X] (f : Y ⟶ X) [IsAffineHom f] [Etale f]
    {F : ModuleSheaf R Y} (hF : IsConstructible F) :
    ∃ p : FiniteLocallyClosedPartition X,
      ∀ k, IsFiniteTypeLocallyConstant
        ((moduleInverseImage R (pullback.fst f (p.inclusion k))).obj F) := by
  have : IsAffine Y := isAffine_of_isAffineHom f
  obtain ⟨q⟩ := nonempty_constructiblePartition hF
  obtain ⟨p, -, -, hred, hp⟩ :=
    exists_reduced_finite_clopen_partition_of_isAffineHom_of_etale f
      (fun i => Set.range (q.inclusion i)) q.constructible_range
  refine ⟨p, fun k => ?_⟩
  have := hred k
  exact isFiniteTypeLocallyConstant_pullback_of_clopen_partition
    (pullback.fst f (p.inclusion k)) q (fun i => hp i k)

private theorem exists_common_wholeSource_partition_fin {X : Scheme.{u}}
    (n : ℕ) (U : Fin n → X.Etale) (F : ModuleSheaf R X)
    (hF : ∀ i, ∃ p : FiniteLocallyClosedPartition X,
      ∀ k, IsFiniteTypeLocallyConstant
        ((moduleInverseImage R (pullback.fst (U i).hom (p.inclusion k))).obj
          ((moduleInverseImage R (U i).hom).obj F))) :
    ∃ p : FiniteLocallyClosedPartition X,
      ∀ i k, IsFiniteTypeLocallyConstant
        ((moduleInverseImage R (pullback.fst (U i).hom (p.inclusion k))).obj
          ((moduleInverseImage R (U i).hom).obj F)) := by
  induction n with
  | zero => exact ⟨.singleton X, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih (fun i => U i.succ) (fun i => hF i.succ)
    obtain ⟨q, hq⟩ := hF 0
    refine ⟨p.intersection q, ?_⟩
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact (p.intersectionRefinesRight q).isFiniteTypeLocallyConstant_pullback
        (U 0).hom ((moduleInverseImage R (U 0).hom).obj F) hq
    · exact (p.intersectionRefinesLeft q).isFiniteTypeLocallyConstant_pullback
        (U k.succ).hom ((moduleInverseImage R (U k.succ).hom).obj F) (hp k)

/-- Finite affine etale charts with constructible original module pullbacks
have one actual common base partition with whole-source finite-type local
constancy. No initial common partition is supplied. -/
theorem exists_common_wholeSource_partition_of_affine_etale
    {X : Scheme.{u}} [IsAffine X] {ι : Type v} [Finite ι]
    (U : ι → X.Etale) (hU : ∀ i, IsAffine (U i).left) (F : ModuleSheaf R X)
    (hF : ∀ i, IsConstructible ((moduleInverseImage R (U i).hom).obj F)) :
    ∃ p : FiniteLocallyClosedPartition X,
      ∀ i k, IsFiniteTypeLocallyConstant
        ((moduleInverseImage R (pullback.fst (U i).hom (p.inclusion k))).obj
          ((moduleInverseImage R (U i).hom).obj F)) := by
  classical
  let := Fintype.ofFinite ι
  have hlocal (i : ι) : ∃ p : FiniteLocallyClosedPartition X,
      ∀ k, IsFiniteTypeLocallyConstant
        ((moduleInverseImage R (pullback.fst (U i).hom (p.inclusion k))).obj
          ((moduleInverseImage R (U i).hom).obj F)) := by
    have := hU i
    exact exists_wholeSource_partition_of_isAffineHom_of_etale
      (X := X) (Y := (U i).left) (U i).hom (hF i)
  obtain ⟨p, hp⟩ := exists_common_wholeSource_partition_fin (Fintype.card ι)
    (fun i => U ((Fintype.equivFin ι).symm i)) F
    (fun i => hlocal ((Fintype.equivFin ι).symm i))
  refine ⟨p, ?_⟩
  intro i k
  obtain ⟨j, rfl⟩ := (Fintype.equivFin ι).symm.surjective i
  exact hp j k

end Modules

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
