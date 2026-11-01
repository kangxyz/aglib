/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Kernel.Basic
public import Aglib.AlgebraicGeometry.Group.BaseChange.MarkedKernel
public import Aglib.AlgebraicGeometry.Morphisms.Finite.ClosedPointFibres
public import Aglib.AlgebraicGeometry.Morphisms.Finite.PointLifts
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# A finite actual group kernel gives local quasi-finiteness

For a morphism of group schemes locally of finite type over any base scheme, a finite universal
marked kernel gives finite original topological fibres, hence local quasi-finiteness. The native
categorical kernel is the final specialization.

For each target point, the proof uses the algebraic closure of its actual residue field. The
original marked kernel and group morphism are pulled back by the native constructors, and the
whole original cartesian map square identifies the image of the geometric fibre with the
original fibre. Over the algebraically closed geometric field, the all-test-scheme torsor
translation equivalence gives finite rational-point fibres. Jacobson closed-point density gives
the full topological fibre. No ground-field rational lift or source properness is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Group.Kernel

attribute [local instance] Over.cartesianMonoidalCategory

section GeometricField

variable {k : Type u} [Field k]

private theorem finite_preimage_point_of_isFinite_kernelMarking_of_isAlgClosed
    [IsAlgClosed k] {M G H : Grp (Over (Spec (.of k)))} {f : G ⟶ H}
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
    (m : KernelMarking M G H f) [IsFinite M.X.hom]
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ H.X) :
    (f.hom.hom.left ⁻¹' {y.left (IsLocalRing.closedPoint k)}).Finite := by
  have : JacobsonSpace G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
  have hclosed : IsClosed {y.left (IsLocalRing.closedPoint k)} :=
    (pointEquivClosedPoint H.X.hom ⟨y.left, Over.w y⟩).2
  have hpoints : {p : 𝟙_ (Over (Spec (.of k))) ⟶ G.X | p ≫ f.hom.hom = y}.Finite := by
    have : Finite (𝟙_ (Over (Spec (.of k))) ⟶ M.X) :=
      Scheme.Finite.finite_hom_over_field M.X.hom
    rcases Set.eq_empty_or_nonempty
        {p : 𝟙_ (Over (Spec (.of k))) ⟶ G.X | p ≫ f.hom.hom = y} with h | ⟨p₀, hp₀⟩
    · rw [h]
      exact Set.finite_empty
    have : Finite {p : 𝟙_ (Over (Spec (.of k))) ⟶ G.X |
        p ≫ f.hom.hom = p₀ ≫ f.hom.hom} :=
      Finite.of_equiv _ (m.toTorsorAction.fiberEquiv p₀)
    have hfin : {p : 𝟙_ (Over (Spec (.of k))) ⟶ G.X |
        p ≫ f.hom.hom = p₀ ≫ f.hom.hom}.Finite := Set.toFinite _
    change p₀ ≫ f.hom.hom = y at hp₀
    rw [hp₀] at hfin
    exact hfin
  refine JacobsonSpace.finite_of_isClosed_of_finite_inter_closedPoints
    (hclosed.preimage f.hom.hom.left.continuous) ?_
  refine (hpoints.image fun p => p.left (IsLocalRing.closedPoint k)).subset ?_
  rintro z ⟨hz, hzc⟩
  change f.hom.hom.left z = y.left (IsLocalRing.closedPoint k) at hz
  let pz : 𝟙_ (Over (Spec (.of k))) ⟶ G.X :=
    Over.homMk (pointOfClosedPoint G.X.hom z hzc) (pointOfClosedPoint_comp G.X.hom z hzc)
  have hpz : pz.left (IsLocalRing.closedPoint k) = z :=
    pointOfClosedPoint_apply G.X.hom z hzc _
  refine ⟨pz, ?_, hpz⟩
  apply Over.OverMorphism.ext
  exact ext_of_apply_closedPoint_eq H.X.hom (Over.w (pz ≫ f.hom.hom)) (Over.w y)
    (by
      change f.hom.hom.left (pz.left (IsLocalRing.closedPoint k)) =
        y.left (IsLocalRing.closedPoint k)
      rw [hpz]
      exact hz)

end GeometricField

section GeneralBase

variable {S : Scheme.{u}}

/-- A finite universal marked kernel gives finite original fibres over every base scheme. The
geometric fibre used for each target point is formed from its actual residue field. -/
theorem finite_preimage_singleton_of_isFinite_kernelMarking
    {M G H : Grp (Over S)} {f : G ⟶ H}
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
    (m : KernelMarking M G H f) [IsFinite M.X.hom] (y : H.X.left) :
    (f.hom.hom.left ⁻¹' {y}).Finite := by
  let Ω := AlgebraicClosure (H.X.left.residueField y)
  let y₀ : Spec (.of Ω) ⟶ H.X.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (H.X.left.residueField y) Ω)) ≫
      H.X.left.fromSpecResidueField y
  let s : Spec (.of Ω) ⟶ S := y₀ ≫ H.X.hom
  let G' := BaseChange.baseChangedGroup s G
  let H' := BaseChange.baseChangedGroup s H
  let M' := BaseChange.baseChangedGroup s M
  let f' := (BaseChange.groupSchemeBaseChange s).functor.map f
  let m' := BaseChange.kernelMarking s m
  have : LocallyOfFiniteType G'.X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom s)
    infer_instance
  have : LocallyOfFiniteType H'.X.hom := by
    change LocallyOfFiniteType (pullback.snd H.X.hom s)
    infer_instance
  have : IsFinite M'.X.hom := by
    change IsFinite (pullback.snd M.X.hom s)
    infer_instance
  let y' : 𝟙_ (Over (Spec (.of Ω))) ⟶ H'.X :=
    Over.homMk (pullback.lift y₀ (𝟙 _) (by simp [s])) (by
      change pullback.lift y₀ (𝟙 _) _ ≫ pullback.snd H.X.hom s = 𝟙 _
      exact pullback.lift_snd _ _ _)
  have hy' : pullback.fst H.X.hom s (y'.left (IsLocalRing.closedPoint Ω)) = y := by
    change (y'.left ≫ pullback.fst H.X.hom s) (IsLocalRing.closedPoint Ω) = y
    rw [show y'.left ≫ pullback.fst H.X.hom s = y₀ from pullback.lift_fst _ _ _]
    exact H.X.left.fromSpecResidueField_apply y _
  have hfin := (finite_preimage_point_of_isFinite_kernelMarking_of_isAlgClosed m' y').image
    (pullback.fst G.X.hom s)
  have himage := Scheme.image_preimage_eq_of_isPullback (BaseChange.map_isPullback s f).flip
    ({y'.left (IsLocalRing.closedPoint Ω)} : Set H'.X.left)
  simp only [Set.image_singleton] at himage
  have hfin' : (f.hom.hom.left ⁻¹'
      {pullback.fst H.X.hom s (y'.left (IsLocalRing.closedPoint Ω))}).Finite :=
    Eq.mp (congrArg (fun Z : Set G.X.left => Z.Finite) himage) hfin
  exact Eq.mp (congrArg (fun z : H.X.left => (f.hom.hom.left ⁻¹' {z}).Finite) hy') hfin'

/-- A group morphism with a finite universal marked kernel is locally quasi-finite over the
original base. Its locally finite-type hypothesis is derived from the original source. -/
theorem locallyQuasiFinite_of_isFinite_kernelMarking
    {M G H : Grp (Over S)} {f : G ⟶ H}
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
    (m : KernelMarking M G H f) [IsFinite M.X.hom] : LocallyQuasiFinite f.hom.hom.left := by
  have : LocallyOfFiniteType (f.hom.hom.left ≫ H.X.hom) := by
    rw [Over.w f.hom.hom]
    infer_instance
  have : LocallyOfFiniteType f.hom.hom.left :=
    locallyOfFiniteType_of_comp f.hom.hom.left H.X.hom
  exact LocallyQuasiFinite.of_finite_preimage_singleton _
    (finite_preimage_singleton_of_isFinite_kernelMarking m)

/-- Finiteness of the actual categorical kernel makes the original native group morphism
locally quasi-finite, retaining the original kernel and its marking on every test scheme. -/
theorem locallyQuasiFinite_of_isFinite_group
    {G H : Grp (Over S)} (f : G ⟶ H)
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
    [IsFinite (group f).X.hom] : LocallyQuasiFinite f.hom.hom.left :=
  locallyQuasiFinite_of_isFinite_kernelMarking (marking f)

end GeneralBase

end AlgebraicGeometry.Scheme.Group.Kernel
