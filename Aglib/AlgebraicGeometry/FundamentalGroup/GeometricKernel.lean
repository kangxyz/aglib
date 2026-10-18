/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The actual geometric-fibre map into the arithmetic projection kernel

Prerequisite for `K2-018#eq:k2018-pointed-character` and
`K2-018#prop:k2018-arithmetic-characters`, on source bases
`e73d98b1b5c1e5abcdebf7d058e436d792b87982` and
`ac804cb2f648f42380e612235b972786506d0b9f`.
The accepted fibre-automorphism API is `EtaleFundamentalGroups.lean`, SHA256
`f45f9cb6815524a8b04347d98bd51d0a95dd787e6499cec65af8a8171c31101f`.

The base change, its point, the inclusion into the original pointed scheme,
and all induced group homomorphisms are actual scheme constructions. The
identity point of a field spectrum has trivial fibre-automorphism group:
naturality along each point's morphism from the identity cover proves this
without a Galois-category classification theorem. The resulting commutative
pointed diagram shows that the geometric map lands in the actual projection
kernel. Its continuity is proved for the canonical evaluation/subgroup topologies.

The retained standard theorem is the Stacks Project, Lemma 58.14.3, tag `0BTX`,
https://stacks.math.columbia.edu/tag/0BTX (statement and proof checked).
It asserts the geometric/arithmetic short exact sequence when `X` is
quasi-compact and quasi-separated and `X` over the algebraic closure is connected.
The application below explicitly retains bijectivity of the constructed
geometric-to-kernel homomorphism as `Stacks0BTX`; this is a premise, not a proved
exact-sequence theorem. Properness and geometric connectedness are used only to
verify its geometric hypotheses. Given that premise, compactness and Hausdorffness
prove that the constructed group equivalence is a homeomorphism.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.PreGaloisCategory
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberToFinite_map)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel

universe u

section IdentityPoint

variable (K : Type u) [Field K]

/-- The identity finite étale cover of the field spectrum. -/
abbrev identityCover : Scheme.FiniteEtale (Spec (CommRingCat.of K)) :=
  _root_.AlgebraicGeometry.Scheme.FiniteEtale.mk (𝟙 (Spec (CommRingCat.of K)))

/-- The identity point has no nontrivial natural fibre automorphism. -/
theorem identityFiberAut_eq_one (a : FiberAutGroup (𝟙 (Spec (CommRingCat.of K)))) :
    a = 1 := by
  let I := identityCover K
  let q : Fiber (𝟙 (Spec (CommRingCat.of K))) I := 𝟙 _
  have hq : a.hom.app I q = q := by
    apply Over.OverMorphism.ext
    have h := Over.w (a.hom.app I q)
    change (a.hom.app I q).left ≫ 𝟙 _ = 𝟙 _ at h
    change (a.hom.app I q).left = 𝟙 _
    simpa only [Category.comp_id] using h
  apply Aut.ext
  apply NatTrans.ext
  funext Y
  apply FintypeCat.hom_ext
  intro p
  change a.hom.app Y p = p
  let f : I ⟶ Y := ObjectProperty.homMk p
  have hn := evaluate_naturality (𝟙 (Spec (CommRingCat.of K))) a f q
  rw [hq] at hn
  simpa [q, f, fiberToFinite_map] using hn.symm

instance identityFiberAut_subsingleton : Subsingleton (FiberAutGroup (𝟙 (Spec (CommRingCat.of
  K)))) :=
  ⟨fun a b => (identityFiberAut_eq_one K a).trans (identityFiberAut_eq_one K b).symm⟩

end IdentityPoint

section BaseChange

variable {B X : Scheme.{u}} {K : Type u} [Field K]
variable (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B)
variable (o : B ⟶ X) (h : o ≫ p = 𝟙 B)

/-- The actual point on the base change induced by the rational section. -/
def baseChangePoint : Spec (CommRingCat.of K) ⟶ pullback p b :=
  pullback.lift (b ≫ o) (𝟙 _) (by simp [Category.assoc, h])

@[simp] theorem baseChangePoint_fst :
    baseChangePoint b p o h ≫ pullback.fst p b = b ≫ o := by simp [baseChangePoint]

@[simp] theorem baseChangePoint_snd :
    baseChangePoint b p o h ≫ pullback.snd p b = 𝟙 _ := by simp [baseChangePoint]

/-- Inclusion of the actual base-changed pointed scheme. -/
def pointedInclusion : Under.mk (baseChangePoint b p o h) ⟶ Under.mk (b ≫ o) :=
  Under.homMk (pullback.fst p b) (baseChangePoint_fst b p o h)

/-- Projection of the base-changed pointed scheme to the identity field point. -/
def pointedBaseProjection :
    Under.mk (baseChangePoint b p o h) ⟶ Under.mk (𝟙 (Spec (CommRingCat.of K))) :=
  Under.homMk (pullback.snd p b) (baseChangePoint_snd b p o h)

/-- The chosen field point itself, as a morphism of pointed schemes. -/
def pointedBase : Under.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Under.mk b :=
  Under.homMk b (by simp)

/-- The two composites are equal by the actual pullback square. -/
theorem pointedSquare :
    pointedInclusion b p o h ≫ pointedProjection b p o h =
      pointedBaseProjection b p o h ≫ pointedBase b := by
  apply Under.UnderMorphism.ext
  exact pullback.condition

/-- The actual fibre automorphism group of the pointed base change. -/
abbrev BaseChangeGroup := FiberAutGroup (baseChangePoint b p o h)

/-- The actual subgroup used by the rational pointed-character model. -/
abbrev ProjectionKernel := (projectionHom b p o h).ker

/-- The homomorphism induced by projection from the actual base-changed scheme. -/
def baseChangeHom : BaseChangeGroup b p o h →* FiberAutGroup (b ≫ o) :=
  pointedMap (pointedInclusion b p o h)

theorem continuous_baseChangeHom : Continuous (baseChangeHom b p o h) :=
  continuous_pointedMap (pointedInclusion b p o h)

/-- Evaluation is the existing pullback-fibre conjugation formula. -/
theorem baseChangeHom_apply (a : BaseChangeGroup b p o h) (Y : Scheme.FiniteEtale X)
    (q : Fiber (b ≫ o) Y) :
    (baseChangeHom b p o h a).hom.app Y q =
      (pointedFiberEquiv (pointedInclusion b p o h) Y).symm
        (a.hom.app ((baseChange (pullback.fst p b)).obj Y)
          (pointedFiberEquiv (pointedInclusion b p o h) Y q)) :=
  pointedMap_apply (pointedInclusion b p o h) a Y q

/-- On underlying scheme points, evaluation is followed by the first projection of the pulled-back
cover. -/
theorem baseChangeHom_apply_left (a : BaseChangeGroup b p o h) (Y : Scheme.FiniteEtale X)
    (q : Fiber (b ≫ o) Y) :
    ((baseChangeHom b p o h a).hom.app Y q).left =
      (a.hom.app ((baseChange (pullback.fst p b)).obj Y)
        (pointedFiberEquiv (pointedInclusion b p o h) Y q)).left ≫
          pullback.fst Y.obj.hom (pullback.fst p b) := by
  rw [baseChangeHom_apply, pointedFiberEquiv_symm_left]
  rfl

/-- The projection of the geometric map is trivial, by the pointed square and identity-point
group. -/
@[simp] theorem projection_baseChangeHom (a : BaseChangeGroup b p o h) :
    projectionHom b p o h (baseChangeHom b p o h a) = 1 := by
  have hs := congrArg (fun f => pointedMap f a) (pointedSquare b p o h)
  rw [pointedMap_comp, pointedMap_comp] at hs
  change projectionHom b p o h (baseChangeHom b p o h a) =
    pointedMap (pointedBase b) (pointedMap (pointedBaseProjection b p o h) a) at hs
  rw [identityFiberAut_eq_one K (pointedMap (pointedBaseProjection b p o h) a), map_one] at hs
  exact hs

/-- The constructed map into the actual projection kernel; no exactness hypothesis is needed. -/
def kernelHom : BaseChangeGroup b p o h →* ProjectionKernel b p o h where
  toFun a := ⟨baseChangeHom b p o h a, projection_baseChangeHom b p o h a⟩
  map_one' := Subtype.ext (map_one (baseChangeHom b p o h))
  map_mul' a c := Subtype.ext (map_mul (baseChangeHom b p o h) a c)

@[simp] theorem kernelHom_val (a : BaseChangeGroup b p o h) :
    (kernelHom b p o h a : FiberAutGroup (b ≫ o)) = baseChangeHom b p o h a := rfl

theorem continuous_kernelHom : Continuous (kernelHom b p o h) :=
  (continuous_baseChangeHom b p o h).subtype_mk _

/-- The canonical geometric-to-kernel homomorphism with its proved continuity. -/
def continuousKernelHom : BaseChangeGroup b p o h →ₜ* ProjectionKernel b p o h :=
  { kernelHom b p o h with continuous_toFun := continuous_kernelHom b p o h }

theorem isClosed_projectionKernel :
    IsClosed ((projectionHom b p o h).ker : Set (FiberAutGroup (b ≫ o))) :=
  isClosed_eq (continuous_projectionHom b p o h) continuous_const

instance compactSpace_projectionKernel : CompactSpace (ProjectionKernel b p o h) :=
  isCompact_iff_compactSpace.mp (isClosed_projectionKernel b p o h).isCompact

theorem t2Space_projectionKernel : T2Space (ProjectionKernel b p o h) := inferInstance

theorem isTopologicalGroup_projectionKernel : IsTopologicalGroup (ProjectionKernel b p o h) :=
  inferInstance

/-- Conditional group identification for the constructed canonical map.
The bijectivity argument is an explicit exact-sequence premise. -/
def kernelMulEquiv (hExact : Function.Bijective (kernelHom b p o h)) :
    BaseChangeGroup b p o h ≃* ProjectionKernel b p o h :=
  MulEquiv.ofBijective (kernelHom b p o h) hExact

/-- Compact source and Hausdorff kernel turn the conditional group identification into a
homeomorphism. -/
def kernelHomeomorph (hExact : Function.Bijective (kernelHom b p o h)) :
    BaseChangeGroup b p o h ≃ₜ ProjectionKernel b p o h :=
  (kernelMulEquiv b p o h hExact).toEquiv.toHomeomorphOfContinuousClosed
    (continuous_kernelHom b p o h) (continuous_kernelHom b p o h).isClosedMap

/-- Conditional topological group identification; inverse continuity is proved, not assumed. -/
def kernelContinuousEquiv (hExact : Function.Bijective (kernelHom b p o h)) :
    BaseChangeGroup b p o h ≃ₜ* ProjectionKernel b p o h :=
  { kernelMulEquiv b p o h hExact with
    continuous_toFun := continuous_kernelHom b p o h
    continuous_invFun := (kernelHomeomorph b p o h hExact).continuous_invFun }

@[simp] theorem kernelContinuousEquiv_apply
    (hExact : Function.Bijective (kernelHom b p o h)) (a : BaseChangeGroup b p o h) :
    kernelContinuousEquiv b p o h hExact a = kernelHom b p o h a := rfl

@[simp] theorem kernelContinuousEquiv_symm_kernelHom
    (hExact : Function.Bijective (kernelHom b p o h)) (a : BaseChangeGroup b p o h) :
    (kernelContinuousEquiv b p o h hExact).symm (kernelHom b p o h a) = a :=
  (kernelContinuousEquiv b p o h hExact).symm_apply_apply a

/-- The inverse of the conditional identification maps back to the actual kernel inclusion. -/
@[simp] theorem baseChangeHom_kernelContinuousEquiv_symm
    (hExact : Function.Bijective (kernelHom b p o h)) (n : ProjectionKernel b p o h) :
    baseChangeHom b p o h ((kernelContinuousEquiv b p o h hExact).symm n) =
      (n : FiberAutGroup (b ≫ o)) :=
  congrArg (fun m : ProjectionKernel b p o h => (m : FiberAutGroup (b ≫ o)))
    ((kernelContinuousEquiv b p o h hExact).apply_symm_apply n)

end BaseChange

section Field

variable (F : Type u) [Field F]
variable {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of F))
variable (o : Spec (CommRingCat.of F) ⟶ X) (h : o ≫ p = 𝟙 _)

/-- The fixed algebraic-closure point of the field spectrum. -/
abbrev algebraicClosurePoint := fieldPoint F (AlgebraicClosure F)

/-- The actual geometric base change of the given scheme over `F`. -/
abbrev geometricBaseChange := pullback p (algebraicClosurePoint F)

/-- The actual geometric point obtained by base-changing the rational section. -/
abbrev geometricPoint : Spec (CommRingCat.of (AlgebraicClosure F)) ⟶ geometricBaseChange F p :=
  baseChangePoint (algebraicClosurePoint F) p o h

/-- The actual fundamental group of the geometric fibre at its rational origin. -/
abbrev GeometricGroup := FundamentalGroup (geometricPoint F p o h)

/-- The subgroup of the actual arithmetic group killed by the actual scheme projection. -/
abbrev ArithmeticKernel := ProjectionKernel (algebraicClosurePoint F) p o h

/-- The geometric-to-arithmetic homomorphism induced by the actual first pullback projection. -/
abbrev geometricHom : GeometricGroup F p o h →*
    FiberAutGroup (algebraicClosurePoint F ≫ o) :=
  baseChangeHom (algebraicClosurePoint F) p o h

/-- The unconditional canonical homomorphism from the geometric group into the actual kernel. -/
abbrev geometricKernelHom : GeometricGroup F p o h →* ArithmeticKernel F p o h :=
  kernelHom (algebraicClosurePoint F) p o h

theorem continuous_geometricKernelHom : Continuous (geometricKernelHom F p o h) :=
  continuous_kernelHom (algebraicClosurePoint F) p o h

/-- The actual geometric-to-kernel map with its proved continuity. -/
abbrev continuousGeometricKernelHom : GeometricGroup F p o h →ₜ* ArithmeticKernel F p o h :=
  continuousKernelHom (algebraicClosurePoint F) p o h

@[simp] theorem geometricKernelHom_val (a : GeometricGroup F p o h) :
    (geometricKernelHom F p o h a : FiberAutGroup (algebraicClosurePoint F ≫ o)) =
      geometricHom F p o h a := rfl

/-- Composing the kernel map with the actual subgroup inclusion recovers the scheme-induced map. -/
theorem geometricKernelHom_inclusion :
    ((projectionHom (algebraicClosurePoint F) p o h).ker.subtype).comp
      (geometricKernelHom F p o h) = geometricHom F p o h := rfl

/-- Evaluation on a cover uses its actual pullback to the geometric fibre. -/
theorem geometricKernelHom_evaluate (a : GeometricGroup F p o h) (Y : Scheme.FiniteEtale X)
    (q : Fiber (algebraicClosurePoint F ≫ o) Y) :
    (geometricKernelHom F p o h a : FiberAutGroup (algebraicClosurePoint F ≫ o)).hom.app Y q =
      (pointedFiberEquiv (pointedInclusion (algebraicClosurePoint F) p o h) Y).symm
        (a.hom.app ((baseChange (pullback.fst p (algebraicClosurePoint F))).obj Y)
          (pointedFiberEquiv (pointedInclusion (algebraicClosurePoint F) p o h) Y q)) :=
  baseChangeHom_apply (algebraicClosurePoint F) p o h a Y q

/-- The geometric hypotheses of Stacks `0BTX` hold for a proper geometrically connected scheme.
This verifies applicability only; it does not prove the retained exact-sequence conclusion. -/
theorem proper_geometricallyConnected_conditions [IsProper p] [GeometricallyConnected p] :
    CompactSpace X ∧ QuasiSeparatedSpace X ∧ ConnectedSpace (geometricBaseChange F p) := by
  refine ⟨(quasiCompact_iff_compactSpace p).mp inferInstance,
    quasiSeparatedSpace_of_quasiSeparated p, ?_⟩
  exact GeometricallyConnected.connectedSpace_of_subsingleton
    (pullback.snd p (algebraicClosurePoint F))

end Field

/-- Explicit retained standard theorem, the kernel-identification part of Stacks `0BTX`,
Lemma 58.14.3, restricted to a displayed rational section. The groups and map in this
premise have already been constructed above. No instance or proof of this premise is supplied. -/
structure Stacks0BTX (F : Type u) [Field F] : Prop where
  kernel_bijective : ∀ {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of F))
    (o : Spec (CommRingCat.of F) ⟶ X) (h : o ≫ p = 𝟙 _),
    CompactSpace X → QuasiSeparatedSpace X → ConnectedSpace (geometricBaseChange F p) →
    Function.Bijective (geometricKernelHom F p o h)

section RetainedExactSequence

variable (F : Type u) [Field F] (h0BTX : Stacks0BTX F)
variable {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of F))
variable (o : Spec (CommRingCat.of F) ⟶ X) (h : o ≫ p = 𝟙 _)
variable [IsProper p] [GeometricallyConnected p]
include h0BTX

/-- Conditional bijectivity of the actual map, with the retained standard theorem explicit. -/
theorem geometricKernelHom_bijective : Function.Bijective (geometricKernelHom F p o h) := by
  obtain ⟨hqc, hqs, hconn⟩ := proper_geometricallyConnected_conditions F p
  exact h0BTX.kernel_bijective p o h hqc hqs hconn

/-- Identification with the actual arithmetic projection kernel, conditional on Stacks `0BTX`.
The topology, inverse continuity, and the underlying homomorphism are all constructed. -/
def geometricKernelContinuousEquiv : GeometricGroup F p o h ≃ₜ* ArithmeticKernel F p o h :=
  kernelContinuousEquiv (algebraicClosurePoint F) p o h
    (geometricKernelHom_bijective F h0BTX p o h)

@[simp] theorem geometricKernelContinuousEquiv_apply (a : GeometricGroup F p o h) :
    geometricKernelContinuousEquiv F h0BTX p o h a = geometricKernelHom F p o h a := rfl

@[simp] theorem geometricKernelContinuousEquiv_val (a : GeometricGroup F p o h) :
    (geometricKernelContinuousEquiv F h0BTX p o h a :
      FiberAutGroup (algebraicClosurePoint F ≫ o)) = geometricHom F p o h a := rfl

/-- The conditional inverse is compatible with the actual kernel inclusion. -/
@[simp] theorem geometricHom_geometricKernelContinuousEquiv_symm (n : ArithmeticKernel F p o h) :
    geometricHom F p o h ((geometricKernelContinuousEquiv F h0BTX p o h).symm n) =
      (n : FiberAutGroup (algebraicClosurePoint F ≫ o)) :=
  baseChangeHom_kernelContinuousEquiv_symm (algebraicClosurePoint F) p o h _ n

end RetainedExactSequence

end AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 9c5233b1722965c518e9340f2a10b142d9017b3a2e87698ef8ad3e8dda15b6b3.
Definitions, hypotheses and universes are retained modulo native names. -/
