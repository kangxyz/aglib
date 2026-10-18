/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Basic
public import Aglib.TopologicalGroup.SplitExtension
public import Aglib.GroupCohomology.H1.SplitExtension

/-!
# Split coordinates for the actual finite-étale fibre groups

Source: `K2-018#eq:k2018-pointed-character` and
`K2-018#prop:k2018-arithmetic-characters`,
`research/exposes/K2/018/expose.tex`, at mathematical snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`. The existing scheme and pointed-H¹
interfaces have basis `ac804cb2f648f42380e612235b972786506d0b9f`.
This realization consumes `EtaleFundamentalGroups.lean`, SHA256
`f45f9cb6815524a8b04347d98bd51d0a95dd787e6499cec65af8a8171c31101f`,
and `SplitExtension.lean`, SHA256
`8da703b63f50c322ea9bb901252f049b86de0ea91c50df498db68a1ca8a2352a`.

For an actual scheme section `o ≫ p = 𝟙 B` and a field-valued point `b`,
the two groups are automorphism groups of the actual finite-étale fibre
functors. Their projection and section are the proved scheme-induced maps.
The kernel, its conjugation action, continuity, semidirect group law, and
coordinate homeomorphism are constructed from those maps. No independent
splitting or continuity certificate is supplied.

The rational-origin specialization supplies the actual `G` and `N` for the
direct continuous pointed-H¹ model. The additive coefficient action and its
topology remain inputs. For a separably closed point field these fibre groups
are the `FundamentalGroup` types of `EtaleFundamentalGroups`. Identification
of the kernel with the group of the geometric fibre, identification of the
field group with `Field.absoluteGaloisGroup`, and comparison with étale H¹
or a continuous-cohomology complex remain separate steps. The continuous H¹
appearing below is precisely `PointedCohomology`'s cocycle/coboundary quotient
in the constructed coordinates.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open GroupCohomology TopologicalGroup

namespace AlgebraicGeometry.Scheme.EtaleFundamentalGroups.Split

universe u

variable {B X : Scheme.{u}} {K : Type u} [Field K]

variable (b : Spec (CommRingCat.of K) ⟶ B)
  (p : X ⟶ B) (o : B ⟶ X) (h : o ≫ p = 𝟙 B)

/-- `K2-018#eq:k2018-pointed-character`, on the module's source basis:
the actual kernel of the scheme-induced projection. Identification with the
fundamental group of the geometric fibre is not part of this definition. -/
abbrev Kernel := (projectionHom b p o h).ker

/-- Auxiliary realization for `K2-018#eq:k2018-pointed-character`, on the
module's source basis: the actual section acts on the kernel by conjugation. -/
abbrev kernelAction : MulDistribMulAction (FiberAutGroup b) (Kernel b p o h) :=
  TopologicalGroup.SplitExtension.kernelAction (projectionHom b p o h) (originHom b o)

/-- Auxiliary action formula for `K2-018#eq:k2018-pointed-character`, on the
module's source basis. It uses the actual origin homomorphism. -/
theorem kernelAction_smul_val (g : FiberAutGroup b) (n : Kernel b p o h) :
    letI := kernelAction b p o h
    ((g • n : Kernel b p o h) : FiberAutGroup (b ≫ o)) =
      originHom b o g * n * (originHom b o g)⁻¹ :=
  TopologicalGroup.SplitExtension.kernelAction_smul_val (projectionHom b p o h) (originHom b o) g n

/-- Auxiliary continuity realization for `K2-018#eq:k2018-pointed-character`,
on the module's source basis: continuity is derived from the scheme origin map. -/
theorem kernelContinuousSMul :
    letI := kernelAction b p o h
    ContinuousSMul (FiberAutGroup b) (Kernel b p o h) :=
  TopologicalGroup.SplitExtension.kernelContinuousSMul (projectionHom b p o h) (originHom b o)
    (continuous_originHom b o)

/-- `K2-018#eq:k2018-pointed-character`, on the module's source basis:
canonical coordinates obtained from the proved actual group retraction. -/
def coordinates : FiberAutGroup (b ≫ o) → Kernel b p o h × FiberAutGroup b :=
  TopologicalGroup.SplitExtension.toCoordinates (projectionHom b p o h) (originHom b o)
    (originHom_projectionHom_apply b p o h)

/-- Auxiliary reassembly map for `K2-018#eq:k2018-pointed-character`, on the
module's source basis. -/
def reassemble : Kernel b p o h × FiberAutGroup b → FiberAutGroup (b ≫ o) :=
  TopologicalGroup.SplitExtension.fromCoordinates (projectionHom b p o h) (originHom b o)

/-- Auxiliary semidirect group structure for
`K2-018#eq:k2018-pointed-character`, on the module's source basis. This selects
the semidirect operations, rather than the ordinary product-group operations. -/
abbrev coordinateGroup : Group (Kernel b p o h × FiberAutGroup b) :=
  TopologicalGroup.SplitExtension.coordinateGroup (projectionHom b p o h) (originHom b o)

/-- `K2-018#eq:k2018-pointed-character`, on the module's source basis:
the actual fibre group is isomorphic to its constructed semidirect coordinates. -/
def coordinateMulEquiv :
    letI : Mul (Kernel b p o h × FiberAutGroup b) := (coordinateGroup b p o h).toMul
    FiberAutGroup (b ≫ o) ≃* Kernel b p o h × FiberAutGroup b :=
  TopologicalGroup.SplitExtension.coordinateMulEquiv (projectionHom b p o h) (originHom b o)
    (originHom_projectionHom_apply b p o h)

/-- `K2-018#eq:k2018-pointed-character`, on the module's source basis:
the same coordinates are a homeomorphism for the actual evaluation topologies. -/
def coordinateHomeomorph :
    FiberAutGroup (b ≫ o) ≃ₜ Kernel b p o h × FiberAutGroup b :=
  TopologicalGroup.SplitExtension.coordinateHomeomorph (projectionHom b p o h) (originHom b o)
    (originHom_projectionHom_apply b p o h)
    (continuous_projectionHom b p o h) (continuous_originHom b o)

/-- Auxiliary continuity of the selected semidirect group operations for
`K2-018#eq:k2018-pointed-character`, on the module's source basis. -/
theorem coordinateIsTopologicalGroup :
    letI := coordinateGroup b p o h
    IsTopologicalGroup (Kernel b p o h × FiberAutGroup b) :=
  TopologicalGroup.SplitExtension.coordinateIsTopologicalGroup (projectionHom b p o h) (originHom
    b o)
    (continuous_originHom b o)

/-- Auxiliary kernel-coordinate formula for `K2-018#eq:k2018-pointed-character`,
on the module's source basis. -/
@[simp] theorem coordinates_fst_val (a : FiberAutGroup (b ≫ o)) :
    ((coordinates b p o h a).1 : FiberAutGroup (b ≫ o)) =
      a * (originHom b o (projectionHom b p o h a))⁻¹ := rfl

/-- Projection formula for `K2-018#eq:k2018-pointed-character`, on the
module's source basis. -/
@[simp] theorem coordinates_projection (a : FiberAutGroup (b ≫ o)) :
    (coordinates b p o h a).2 = projectionHom b p o h a := rfl

/-- Section formula for `K2-018#eq:k2018-pointed-character`, on the
module's source basis: the actual origin maps to `(1,g)`. -/
@[simp] theorem coordinates_origin (g : FiberAutGroup b) :
    coordinates b p o h (originHom b o g) = (1, g) :=
  TopologicalGroup.SplitExtension.toCoordinates_section (projectionHom b p o h) (originHom b o)
    (originHom_projectionHom_apply b p o h) g

/-- Kernel-inclusion formula for `K2-018#eq:k2018-pointed-character`, on the
module's source basis. -/
@[simp] theorem coordinates_kernel (n : Kernel b p o h) :
    coordinates b p o h (n : FiberAutGroup (b ≫ o)) = (n, 1) :=
  TopologicalGroup.SplitExtension.toCoordinates_kernel (projectionHom b p o h) (originHom b o)
    (originHom_projectionHom_apply b p o h) n

/-- The actual multiplication formula needed by
`K2-018#eq:k2018-pointed-character`, on the module's source basis. -/
theorem coordinates_mul (a c : FiberAutGroup (b ≫ o)) :
    letI := kernelAction b p o h
    coordinates b p o h (a * c) =
      ((coordinates b p o h a).1 * (coordinates b p o h a).2 •
        (coordinates b p o h c).1,
        (coordinates b p o h a).2 * (coordinates b p o h c).2) :=
  TopologicalGroup.SplitExtension.toCoordinates_mul (projectionHom b p o h) (originHom b o)
    (originHom_projectionHom_apply b p o h) a c

/-- Auxiliary actual reassembly formula for
`K2-018#eq:k2018-pointed-character`, on the module's source basis. -/
@[simp] theorem reassemble_apply (x : Kernel b p o h × FiberAutGroup b) :
    reassemble b p o h x = x.1 * originHom b o x.2 := rfl

/-- Auxiliary inverse identity for `K2-018#eq:k2018-pointed-character`, on
the module's source basis. -/
-- Keep this original specific simp shortcut alongside the lower generic normalization rules.
@[simp, nolint simpNF] theorem reassemble_coordinates (a : FiberAutGroup (b ≫ o)) :
    reassemble b p o h (coordinates b p o h a) = a :=
  TopologicalGroup.SplitExtension.fromCoordinates_toCoordinates (projectionHom b p o h)
    (originHom b o)
    (originHom_projectionHom_apply b p o h) a

/-- Auxiliary inverse identity for `K2-018#eq:k2018-pointed-character`, on
the module's source basis. -/
-- Keep this original canonical-map simp formula alongside its lower evaluation expansion.
@[simp, nolint simpNF] theorem coordinates_reassemble (x : Kernel b p o h × FiberAutGroup b) :
    coordinates b p o h (reassemble b p o h x) = x :=
  TopologicalGroup.SplitExtension.toCoordinates_fromCoordinates (projectionHom b p o h)
    (originHom b o)
    (originHom_projectionHom_apply b p o h) x

/-- Auxiliary projection of reassembly for
`K2-018#eq:k2018-pointed-character`, on the module's source basis. -/
-- Keep this original canonical-map simp formula alongside its lower evaluation expansion.
@[simp, nolint simpNF] theorem projection_reassemble (x : Kernel b p o h × FiberAutGroup b) :
    projectionHom b p o h (reassemble b p o h x) = x.2 :=
  TopologicalGroup.SplitExtension.projection_fromCoordinates (projectionHom b p o h) (originHom b o)
    (originHom_projectionHom_apply b p o h) x

/-- Auxiliary origin-coordinate reassembly for
`K2-018#eq:k2018-pointed-character`, on the module's source basis. -/
-- Keep this original specific simp shortcut alongside the lower generic normalization rules.
@[simp, nolint simpNF] theorem reassemble_origin (g : FiberAutGroup b) :
    reassemble b p o h (1, g) = originHom b o g :=
  TopologicalGroup.SplitExtension.fromCoordinates_section (projectionHom b p o h) (originHom b o) g

/-- Auxiliary kernel-coordinate reassembly for
`K2-018#eq:k2018-pointed-character`, on the module's source basis. -/
-- Keep this original specific simp shortcut alongside the lower generic normalization rules.
@[simp, nolint simpNF] theorem reassemble_kernel (n : Kernel b p o h) :
    reassemble b p o h (n, 1) = (n : FiberAutGroup (b ≫ o)) :=
  TopologicalGroup.SplitExtension.fromCoordinates_kernel (projectionHom b p o h) (originHom b o) n

/-- Auxiliary identity of the selected group coordinates for
`K2-018#eq:k2018-pointed-character`, on the module's source basis. -/
@[simp] theorem coordinateMulEquiv_apply (a : FiberAutGroup (b ≫ o)) :
    coordinateMulEquiv b p o h a = coordinates b p o h a := rfl

/-- Auxiliary identity of the selected topological coordinates for
`K2-018#eq:k2018-pointed-character`, on the module's source basis. -/
@[simp] theorem coordinateHomeomorph_apply (a : FiberAutGroup (b ≫ o)) :
    coordinateHomeomorph b p o h a = coordinates b p o h a := rfl

/-- Auxiliary inverse topological-coordinate formula for
`K2-018#eq:k2018-pointed-character`, on the module's source basis. -/
@[simp] theorem coordinateHomeomorph_symm_apply
    (x : Kernel b p o h × FiberAutGroup b) :
    (coordinateHomeomorph b p o h).symm x = reassemble b p o h x := rfl

section PointedCohomology

variable (A : Type*) [AddCommGroup A] [DistribMulAction (FiberAutGroup b) A]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul (FiberAutGroup b) A]

/-- Direct continuous pointed-H¹ calculation for
`K2-018#eq:k2018-pointed-character`, on the module's source basis, now with
the actual fibre group and actual projection kernel. This is the existing
cocycle/coboundary quotient in the constructed coordinates, not an étale-H¹
comparison. The projection kernel acts trivially on the coefficients. -/
def pointedCharactersEquiv :
    letI := kernelAction b p o h
    PointedCohomology.PointedH1 (G := FiberAutGroup b) (N := Kernel b p o h) (A := A) ≃+
      PointedCohomology.EquivariantCharacter (FiberAutGroup b) (Kernel b p o h) A := by
  letI := kernelAction b p o h
  exact PointedCohomology.pointedH1AddEquiv

end PointedCohomology

section RationalOrigin

variable {F : Type u} [Field F] [Algebra F K]
  (Y : Over (Spec (CommRingCat.of F)))
  (r : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ Y)

/-- `K2-018#eq:k2018-pointed-character` and
`K2-018#prop:k2018-arithmetic-characters`, on the module's source basis:
the actual arithmetic projection kernel at an actual rational origin. -/
abbrev rationalKernel := Kernel (fieldPoint F K) Y.hom r.left (Over.w r)

/-- Auxiliary rational-origin action realization for
`K2-018#eq:k2018-pointed-character`, on the module's source basis. -/
abbrev rationalKernelAction :
    MulDistribMulAction (FiberAutGroup (fieldPoint F K)) (rationalKernel (K := K) Y r) :=
  kernelAction (fieldPoint F K) Y.hom r.left (Over.w r)

/-- Auxiliary rational-origin continuity realization for
`K2-018#eq:k2018-pointed-character`, on the module's source basis. -/
theorem rationalKernelContinuousSMul :
    letI := rationalKernelAction (K := K) Y r
    ContinuousSMul (FiberAutGroup (fieldPoint F K)) (rationalKernel (K := K) Y r) :=
  kernelContinuousSMul (fieldPoint F K) Y.hom r.left (Over.w r)

/-- Constructed rational-origin coordinates for
`K2-018#eq:k2018-pointed-character`, on the module's source basis. -/
abbrev rationalCoordinates :
    FiberAutGroup (fieldPoint F K ≫ r.left) →
      rationalKernel (K := K) Y r × FiberAutGroup (fieldPoint F K) :=
  coordinates (fieldPoint F K) Y.hom r.left (Over.w r)

/-- Constructed rational-origin coordinate homeomorphism for
`K2-018#eq:k2018-pointed-character`, on the module's source basis. -/
def rationalCoordinateHomeomorph :
    FiberAutGroup (fieldPoint F K ≫ r.left) ≃ₜ
      rationalKernel (K := K) Y r × FiberAutGroup (fieldPoint F K) :=
  coordinateHomeomorph (fieldPoint F K) Y.hom r.left (Over.w r)

/-- Rational arithmetic projection formula for
`K2-018#eq:k2018-pointed-character`, on the module's source basis. -/
-- Keep this original canonical-map simp formula alongside its lower evaluation expansion.
@[simp, nolint simpNF] theorem rationalCoordinates_projection
    (a : FiberAutGroup (fieldPoint F K ≫ r.left)) :
    (rationalCoordinates (K := K) Y r a).2 = rationalPointProjectionHom Y r a := rfl

/-- Actual rational origin formula for `K2-018#eq:k2018-pointed-character`,
on the module's source basis. -/
@[simp] theorem rationalCoordinates_origin (g : FiberAutGroup (fieldPoint F K)) :
    rationalCoordinates (K := K) Y r (rationalPointOriginHom Y r g) = (1, g) :=
  coordinates_origin (fieldPoint F K) Y.hom r.left (Over.w r) g

variable (A : Type*) [AddCommGroup A]
  [DistribMulAction (FiberAutGroup (fieldPoint F K)) A]
  [TopologicalSpace A] [IsTopologicalAddGroup A]
  [ContinuousSMul (FiberAutGroup (fieldPoint F K)) A]

/-- `K2-018#eq:k2018-pointed-character`, on the module's source basis:
the proved direct pointed-H¹ equivalence specialized to the actual rational
origin. Only the additive coefficient action/topology is supplied independently;
the two groups and kernel action are constructed from the actual scheme maps. -/
def rationalPointedCharactersEquiv :
    letI := rationalKernelAction (K := K) Y r
    PointedCohomology.PointedH1 (G := FiberAutGroup (fieldPoint F K))
        (N := rationalKernel (K := K) Y r) (A := A) ≃+
      PointedCohomology.EquivariantCharacter (FiberAutGroup (fieldPoint F K))
        (rationalKernel (K := K) Y r) A :=
  pointedCharactersEquiv (fieldPoint F K) Y.hom r.left (Over.w r) A

end RationalOrigin

end AlgebraicGeometry.Scheme.EtaleFundamentalGroups.Split

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 97943daf852d748f7bca3e089cf922150bea6e91cd4003f40efdd2cae6b6928b.
Definitions, hypotheses and universes are retained modulo native names. -/
