/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AffineScheme.BaseChangeCoordinates
public import Aglib.AlgebraicGeometry.AffineScheme.TensorPullback
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange
public import Aglib.AlgebraicGeometry.Spec.ResidueFiber
public import Aglib.RingTheory.LocalRing.EtaleLift

/-!
# Faithfulness and essential surjectivity of finite etale residue base change

Every actual finite etale cover of the residue spectrum of a local ring is
the literal base change of a finite etale cover of the original spectrum.
The lifted cover is the spectrum of an actual finite etale algebra. The
comparison is an isomorphism over the residue spectrum, with both projections
supplied by the native tensor-pullback comparison.

The open diagonal equalizer and the closed image of its complement also prove
faithfulness. More generally, maps through an unramified target are determined
by residue restriction when the source is universally closed over the base.

No Henselian, Noetherian or excellent assumption is used. Fullness and a proper
comparison remain separate obligations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- An actual finite etale residue cover occurs in a pullback square whose
opposite edge is the spectrum of a finite etale algebra over the local ring.
The given cover's structural map is retained literally. -/
theorem exists_spec_residue_pullback
    (Y : FiniteEtale (Spec (.of (IsLocalRing.ResidueField R)))) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A),
      Module.Finite R A ∧ Algebra.Etale R A ∧
        ∃ g : Y.obj.left ⟶ Spec (.of A),
          IsPullback g Y.obj.hom (Spec.algebraMap R A) (LocalRing.residueSpecMap R) := by
  let : IsAffine Y.obj.left := isAffine_of_isAffineHom Y.obj.hom
  let B : Type u := Γ(Y.obj.left, ⊤)
  let : CommRing B := inferInstanceAs (CommRing Γ(Y.obj.left, ⊤))
  let : Algebra (IsLocalRing.ResidueField R) B :=
    AffineBaseChange.coordinateAlgebra (IsLocalRing.ResidueField R) Y.obj
  have hcoord : Y.obj.left.isoSpec.inv ≫ Y.obj.hom =
      Spec.algebraMap (IsLocalRing.ResidueField R) B :=
    AffineBaseChange.isoSpec_inv_over (IsLocalRing.ResidueField R) Y.obj
  have hcoord' : Y.obj.left.isoSpec.hom ≫
      Spec.algebraMap (IsLocalRing.ResidueField R) B = Y.obj.hom := by
    rw [← hcoord]
    simp
  have : Algebra.Etale (IsLocalRing.ResidueField R) B := by
    have he : Etale (Spec.algebraMap (IsLocalRing.ResidueField R) B) := by
      rw [← hcoord]
      infer_instance
    exact RingHom.etale_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Etale.{u})).mp he)
  obtain ⟨A, hA, hAlg, hfin, het, ⟨e⟩⟩ :=
    IsLocalRing.exists_finite_etale_residue_lift_of_etale R B
  let : CommRing A := hA
  let : Algebra R A := hAlg
  let a : A →+* B := e.toRingHom.comp
    (Algebra.TensorProduct.includeRight :
      A →ₐ[R] IsLocalRing.ResidueField R ⊗[R] A).toRingHom
  have hp : IsPullback (Spec.map (CommRingCat.ofHom a))
      (Spec.algebraMap (IsLocalRing.ResidueField R) B)
      (Spec.algebraMap R A) (LocalRing.residueSpecMap R) :=
    Spec.isPullback_of_tensorEquiv e a rfl
  refine ⟨A, hA, hAlg, hfin, het,
    Y.obj.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom a), ?_⟩
  exact hp.of_iso' Y.obj.left.isoSpec (.refl _) (.refl _) (.refl _)
    (by simp) (by simpa using hcoord') (by simp) (by simp)

/-- The constructed spectrum has the original cover as its literal residue
pullback, by an isomorphism over the actual residue spectrum. -/
theorem exists_spec_residue_lift
    (Y : FiniteEtale (Spec (.of (IsLocalRing.ResidueField R)))) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A),
      Module.Finite R A ∧ Algebra.Etale R A ∧
        Nonempty (Over.mk (pullback.snd (Spec.algebraMap R A)
          (LocalRing.residueSpecMap R)) ≅ Y.obj) := by
  obtain ⟨A, hA, hAlg, hfin, het, g, hg⟩ := exists_spec_residue_pullback R Y
  exact ⟨A, hA, hAlg, hfin, het,
    ⟨Over.isoMk hg.isoPullback.symm hg.isoPullback_inv_snd⟩⟩

/-- Every finite etale cover of the residue spectrum lies in the essential
image of the actual finite-etale base-change functor. -/
theorem exists_residue_baseChange_iso
    (Y : FiniteEtale (Spec (.of (IsLocalRing.ResidueField R)))) :
    ∃ X : FiniteEtale (Spec (.of R)),
      Nonempty ((baseChange (LocalRing.residueSpecMap R)).obj X ≅ Y) := by
  obtain ⟨A, hA, hAlg, hfin, het, ⟨e⟩⟩ := exists_spec_residue_lift R Y
  let : CommRing A := hA
  let : Algebra R A := hAlg
  let : IsFinite (Spec.algebraMap R A) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfin)
  let : Etale (Spec.algebraMap R A) :=
    (HasRingHomProperty.Spec_iff (P := @Etale.{u})).mpr (RingHom.etale_algebraMap.mpr het)
  exact ⟨mk (Spec.algebraMap R A), ⟨ObjectProperty.isoMk _ e⟩⟩

/-- Residue base change on actual finite etale covers is essentially surjective
for every commutative local ring. -/
instance residueSpecMap_baseChange_essSurj :
    (baseChange (LocalRing.residueSpecMap R)).EssSurj where
  mem_essImage Y := exists_residue_baseChange_iso R Y

end AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Maps through an unramified morphism from a universally closed scheme over
a local spectrum are determined by their restriction to the actual residue
fibre. The source need not be connected or reduced. -/
theorem eq_of_residue_pullback_eq {X Y : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) [UniversallyClosed p]
    (q : Y ⟶ Spec (.of R)) [FormallyUnramified q] [LocallyOfFiniteType q]
    (f g : X ⟶ Y) (hf : f ≫ q = p) (hg : g ≫ q = p)
    (hr : pullback.fst p (LocalRing.residueSpecMap R) ≫ f =
      pullback.fst p (LocalRing.residueSpecMap R) ≫ g) : f = g := by
  classical
  let i := pullback.fst p (LocalRing.residueSpecMap R)
  let a : X ⟶ pullback q q := pullback.lift f g (hf.trans hg.symm)
  let j : pullback a (pullback.diagonal q) ⟶ X := pullback.fst _ _
  have hjopen : IsOpenImmersion j := by dsimp [j]; infer_instance
  have hia : i ≫ a = (i ≫ f) ≫ pullback.diagonal q := by
    apply pullback.hom_ext
    · simp [a]
    · simpa [a] using hr.symm
  let l : pullback p (LocalRing.residueSpecMap R) ⟶ pullback a (pullback.diagonal q) :=
    pullback.lift i (i ≫ f) hia
  have hlj : l ≫ j = i := by simp [l, j]
  have hclosed : IsClosed (p '' (Set.range j)ᶜ) :=
    p.isClosedMap _ j.isOpenEmbedding.isOpen_range.isClosed_compl
  have hclosedPoint : IsLocalRing.closedPoint R ∈ Set.range (LocalRing.residueSpecMap R) := by
    refine ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField R), ?_⟩
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
  have hjsurj : Surjective j := by
    constructor
    intro x
    by_contra hx
    have hximage : p x ∈ p '' (Set.range j)ᶜ := ⟨x, hx, rfl⟩
    have hm : IsLocalRing.closedPoint R ∈ p '' (Set.range j)ᶜ :=
      (IsLocalRing.specializes_closedPoint (p x)).mem_closed hclosed hximage
    obtain ⟨z, hz, hzm⟩ := hm
    have hzi : z ∈ Set.range i := by
      change z ∈ Set.range (pullback.fst p (LocalRing.residueSpecMap R))
      rw [Scheme.Pullback.range_fst]
      change p z ∈ Set.range (LocalRing.residueSpecMap R)
      rwa [hzm]
    obtain ⟨w, hw⟩ := hzi
    exact hz ⟨l w, (congrArg (fun t : pullback p (LocalRing.residueSpecMap R) ⟶ X => t w)
      hlj).trans hw⟩
  have : IsIso j :=
    (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨hjopen, hjsurj⟩
  apply (cancel_epi j).mp
  have hj : j ≫ a = pullback.snd a (pullback.diagonal q) ≫ pullback.diagonal q :=
    pullback.condition
  calc
    j ≫ f = (j ≫ a) ≫ pullback.fst q q := by simp [a]
    _ = (pullback.snd a (pullback.diagonal q) ≫ pullback.diagonal q) ≫
        pullback.fst q q := by rw [hj]
    _ = pullback.snd a (pullback.diagonal q) := by simp
    _ = (pullback.snd a (pullback.diagonal q) ≫ pullback.diagonal q) ≫
        pullback.snd q q := by simp
    _ = (j ≫ a) ≫ pullback.snd q q := by rw [hj]
    _ = j ≫ g := by simp [a]

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Residue base change is faithful on finite etale covers over every local
ring. The proof uses the actual pullback projection and the open equalizer. -/
instance residueSpecMap_baseChange_faithful :
    (baseChange (LocalRing.residueSpecMap R)).Faithful where
  map_injective := by
    intro X Y f g h
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply Hom.eq_of_residue_pullback_eq R X.obj.hom Y.obj.hom f.hom.left g.hom.left
      (Over.w f.hom) (Over.w g.hom)
    calc
      pullback.fst X.obj.hom (LocalRing.residueSpecMap R) ≫ f.hom.left =
          ((baseChange (LocalRing.residueSpecMap R)).map f).hom.left ≫
          pullback.fst Y.obj.hom (LocalRing.residueSpecMap R) :=
        (pullback.lift_fst _ _ _).symm
      _ = ((baseChange (LocalRing.residueSpecMap R)).map g).hom.left ≫
          pullback.fst Y.obj.hom (LocalRing.residueSpecMap R) :=
        congrArg (fun k => k.hom.left ≫
          pullback.fst Y.obj.hom (LocalRing.residueSpecMap R)) h
      _ = pullback.fst X.obj.hom (LocalRing.residueSpecMap R) ≫ g.hom.left :=
        pullback.lift_fst _ _ _

end AlgebraicGeometry.Scheme.FiniteEtale
