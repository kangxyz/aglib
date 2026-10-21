/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Kernel.Basic
public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.Basic
public import Aglib.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
# Actual multiplication kernels and geometric torsion points

For a commutative group scheme over a field in universe `u`, literal multiplication
by any natural number (including zero) has the original origin-pullback fibre.
The native `Kernel.group` is compared with that pullback by its canonical scheme
square. Its actual algebraic-closure-valued points are exactly the point-group
`n`-torsion, with the contravariant `Spec` Galois action. Finiteness requires
`IsFinite` of the displayed multiplication; no degree or rank conclusion is made.

Source: `R5Lab.AlgebraicGeometry.EllipticCurve.Torsion.FiniteLevel`, lines 53–197,
packet SHA-256 `4713f0f004da1f37065a679853621758c0a084e6380da28bfdfc2a4a01030473`.
The elliptic wrapper supplies no data used in this slice besides its actual
commutative group object. Current consumer: multiplication-cover monodromy and
its literal finite-level transition maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField (FScheme)
open _root_.AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.Group.MultiplicationKernel

universe u
attribute [local instance] Over.cartesianMonoidalCategory
variable {F : Type u} [Field F]
variable (E : Grp (FScheme F)) [IsCommMonObj E.X]

/-- Literal multiplication by n on the given group scheme. -/
def multiplication (n : ℕ) : E.X ⟶ E.X := (𝟙 E.X) ^ n

/-- The scheme-theoretic kernel, formed with the actual identity section. -/
def kernelScheme (n : ℕ) : FScheme F :=
  Over.mk (pullback.snd (multiplication E n).left η[E.X].left)

/-- Multiplication as a morphism of the actual group objects. -/
def multiplicationHom (n : ℕ) : E ⟶ E := (𝟙 E) ^ n

/-- The group-object power has the same literal underlying multiplication map. -/
@[simp] theorem multiplicationHom_hom (n : ℕ) :
    (multiplicationHom E n).hom.hom = multiplication E n := by
  simp only [multiplicationHom, Grp.Hom.hom_pow, Mon.Hom.hom_pow]
  rfl

/-- The existing actual kernel group, with no new kernel group law. -/
abbrev kernelGroup (n : ℕ) : Grp (FScheme F) := Kernel.group (multiplicationHom E n)

/-- The native kernel group has the literal source kernel square on schemes. -/
theorem kernelSquare (n : ℕ) :
    IsPullback (Kernel.inclusion (multiplicationHom E n)).hom.hom.left
      (kernelGroup E n).X.hom (multiplication E n).left η[E.X].left := by
  simpa only [multiplicationHom_hom] using Kernel.schemeSquare (multiplicationHom E n)

/-- Canonical comparison of the native kernel group with the literal origin pullback. -/
def kernelSchemeIso (n : ℕ) : (kernelGroup E n).X ≅ kernelScheme E n :=
  Over.isoMk (kernelSquare E n).isoPullback (kernelSquare E n).isoPullback_hom_snd

/-- This comparison preserves the original kernel inclusion. -/
@[reassoc (attr := simp)] theorem kernelSchemeIso_hom_fst (n : ℕ) :
    (kernelSchemeIso E n).hom.left ≫ pullback.fst (multiplication E n).left η[E.X].left =
      (Kernel.inclusion (multiplicationHom E n)).hom.hom.left :=
  (kernelSquare E n).isoPullback_hom_fst

/-- Actual geometric points of the group, with additive notation for its group law. -/
abbrev geometricPoints := Additive (Over.mk (FieldGalois.geometricPoint F) ⟶ E.X)

/-- The subgroup of actual geometric points killed by multiplication by n. -/
def torsionSubgroup (n : ℕ) : AddSubgroup (geometricPoints E) :=
  (nsmulAddMonoidHom n : geometricPoints E →+ geometricPoints E).ker

/-- The actual finite-level point group. Finiteness is a theorem, not a field. -/
abbrev finiteTorsionPoints (n : ℕ) := torsionSubgroup E n

@[simp] theorem torsion_killed (n : ℕ) (x : finiteTorsionPoints E n) :
    n • (x.val : geometricPoints E) = 0 := x.property

omit [IsCommMonObj E.X] in
/-- Multiplication on every actual test-scheme point is literal nth power. -/
theorem point_multiplication (n : ℕ) {U : FScheme F} (x : U ⟶ E.X) :
    x ≫ multiplication E n = x ^ n := by
  simp only [multiplication, MonObj.comp_pow, Category.comp_id]

/-- The torsion condition is the actual scheme-fibre equation. -/
theorem torsion_fibre_equation (n : ℕ) (x : finiteTorsionPoints E n) :
    x.val.toMul.left ≫ (multiplication E n).left =
      FieldGalois.geometricPoint F ≫ η[E.X].left := by
  have hx : x.val.toMul ^ n = 1 := x.property
  have he : x.val.toMul ≫ multiplication E n = 1 :=
    (point_multiplication E n x.val.toMul).trans hx
  have hh := congrArg (fun f => f.left) he
  exact hh

/-- A torsion point gives an actual point of the scheme-theoretic kernel. -/
def toKernelPoint (n : ℕ) (x : finiteTorsionPoints E n) :
    Over.mk (FieldGalois.geometricPoint F) ⟶ kernelScheme E n :=
  Over.homMk (pullback.lift x.val.toMul.left (FieldGalois.geometricPoint F)
    (torsion_fibre_equation E n x)) (by
      exact pullback.lift_snd _ _ _)

/-- Every point of the literal kernel is a torsion point of E. -/
def fromKernelPoint (n : ℕ)
    (x : Over.mk (FieldGalois.geometricPoint F) ⟶ kernelScheme E n) :
    finiteTorsionPoints E n := by
  let p : Over.mk (FieldGalois.geometricPoint F) ⟶ E.X :=
    Over.homMk (x.left ≫ pullback.fst (multiplication E n).left η[E.X].left) (by
      have hs : (multiplication E n).left ≫ E.X.hom = E.X.hom :=
        Over.w (multiplication E n)
      have ho : η[E.X].left ≫ E.X.hom = 𝟙 _ := Over.w η[E.X]
      change (x.left ≫ pullback.fst _ _) ≫ E.X.hom = FieldGalois.geometricPoint F
      calc
        _ = x.left ≫ (pullback.fst _ _ ≫ (multiplication E n).left) ≫ E.X.hom := by
          simp only [Category.assoc, hs]
        _ = x.left ≫ (pullback.snd _ _ ≫ η[E.X].left) ≫ E.X.hom := by
          rw [pullback.condition]
        _ = x.left ≫ pullback.snd _ _ := by
          rw [Category.assoc, ho, Category.comp_id]
        _ = FieldGalois.geometricPoint F := Over.w x)
  refine ⟨Additive.ofMul p, ?_⟩
  change p ^ n = 1
  rw [← point_multiplication E n]
  apply Over.OverMorphism.ext
  change (x.left ≫ pullback.fst _ _) ≫ (multiplication E n).left = _
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (fun f => f ≫ η[E.X].left) (Over.w x)

/-- Geometric points of the literal kernel are precisely E[n]. -/
def kernelPointEquiv (n : ℕ) : finiteTorsionPoints E n ≃
    (Over.mk (FieldGalois.geometricPoint F) ⟶ kernelScheme E n) where
  toFun := toKernelPoint E n
  invFun := fromKernelPoint E n
  left_inv x := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  right_inv x := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · change pullback.lift _ _ _ ≫ pullback.snd _ _ = x.left ≫ pullback.snd _ _
      rw [pullback.lift_snd]
      exact (Over.w x).symm

/-- The same torsion points, now valued in the existing native kernel group. -/
def nativeKernelPointEquiv (n : ℕ) : finiteTorsionPoints E n ≃
    (Over.mk (FieldGalois.geometricPoint F) ⟶ (kernelGroup E n).X) :=
  (kernelPointEquiv E n).trans
    { toFun := fun x => x ≫ (kernelSchemeIso E n).inv
      invFun := fun x => x ≫ (kernelSchemeIso E n).hom
      left_inv := fun x => by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      right_inv := fun x => by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] }

/-- Native kernel coordinates recover the very same actual geometric point. -/
@[simp] theorem nativeKernelPointEquiv_inclusion (n : ℕ) (x : finiteTorsionPoints E n) :
    nativeKernelPointEquiv E n x ≫ (Kernel.inclusion (multiplicationHom E n)).hom.hom =
      x.val.toMul := by
  apply Over.OverMorphism.ext
  change ((toKernelPoint E n x).left ≫ (kernelSquare E n).isoPullback.inv) ≫
    (Kernel.inclusion (multiplicationHom E n)).hom.hom.left = x.val.toMul.left
  calc
    _ = (toKernelPoint E n x).left ≫
        pullback.fst (multiplication E n).left η[E.X].left :=
      (Category.assoc _ _ _).trans
        (congrArg (fun f => (toKernelPoint E n x).left ≫ f)
          (kernelSquare E n).isoPullback_inv_fst)
    _ = _ := pullback.lift_fst _ _ _

/-- Finiteness comes from base-changing the finite multiplication morphism. -/
instance kernelScheme_finite (n : ℕ) [IsFinite (multiplication E n).left] :
    IsFinite (kernelScheme E n).hom := by
  exact inferInstanceAs (IsFinite (pullback.snd (multiplication E n).left η[E.X].left))

/-- Finiteness of actual torsion points, from the independent multiplication theorem. -/
instance finiteTorsionPoints_finite (n : ℕ) [IsFinite (multiplication E n).left] :
    Finite (finiteTorsionPoints E n) := by
  let : Finite (Over.mk (FieldGalois.geometricPoint F) ⟶ kernelScheme E n) :=
    _root_.AlgebraicGeometry.Scheme.Finite.finite_hom_over_point (kernelScheme E n).hom
      (FieldGalois.geometricPoint F)
  exact Finite.of_equiv _ (kernelPointEquiv E n).symm

/-- Actual Galois action on the curve points, by contravariant Spec precomposition. -/
def geometricGalois (σ : Field.absoluteGaloisGroup F) :
    geometricPoints E →+ geometricPoints E where
  toFun x := Additive.ofMul (FieldGalois.pointEnd F σ ≫ x.toMul)
  map_zero' := by
    change FieldGalois.pointEnd F σ ≫ (1 : _ ⟶ E.X) = 1
    exact MonObj.comp_one _
  map_add' x y := MonObj.comp_mul _ x.toMul y.toMul

/-- Galois preserves the literal torsion kernel. -/
def torsionGalois (n : ℕ) (σ : Field.absoluteGaloisGroup F) :
    finiteTorsionPoints E n →+ finiteTorsionPoints E n :=
  { toFun := fun x => ⟨geometricGalois E σ x.val, by
      change n • geometricGalois E σ x.val = 0
      rw [← map_nsmul, torsion_killed E n x, map_zero]⟩
    map_zero' := by apply Subtype.ext; exact map_zero (geometricGalois E σ)
    map_add' x y := by apply Subtype.ext; exact map_add (geometricGalois E σ) x.val y.val }

@[simp] theorem torsionGalois_val (n : ℕ) (σ : Field.absoluteGaloisGroup F)
    (x : finiteTorsionPoints E n) :
    (torsionGalois E n σ x).val.toMul = FieldGalois.pointEnd F σ ≫ x.val.toMul := rfl

@[simp] theorem torsionGalois_one (n : ℕ) (x : finiteTorsionPoints E n) :
    torsionGalois E n 1 x = x := by
  apply Subtype.ext
  change Additive.ofMul (FieldGalois.pointEnd F 1 ≫ x.val.toMul) = x.val
  rw [FieldGalois.pointEnd_one, Category.id_comp]
  rfl

@[simp] theorem torsionGalois_mul (n : ℕ) (σ τ : Field.absoluteGaloisGroup F)
    (x : finiteTorsionPoints E n) :
    torsionGalois E n (σ * τ) x = torsionGalois E n σ (torsionGalois E n τ x) := by
  apply Subtype.ext
  change Additive.ofMul (FieldGalois.pointEnd F (σ * τ) ≫ x.val.toMul) =
    Additive.ofMul (FieldGalois.pointEnd F σ ≫ (FieldGalois.pointEnd F τ ≫ x.val.toMul))
  rw [FieldGalois.pointEnd_mul, Category.assoc]

/-- The field action on E[n], including its additive compatibility. -/
instance torsionGaloisAction (n : ℕ) :
    DistribMulAction (Field.absoluteGaloisGroup F) (finiteTorsionPoints E n) where
  smul := fun σ x => torsionGalois E n σ x
  one_smul := torsionGalois_one E n
  mul_smul := torsionGalois_mul E n
  smul_zero σ := map_zero (torsionGalois E n σ)
  smul_add σ := map_add (torsionGalois E n σ)


/-- The literal kernel-point equivalence respects actual Galois precomposition. -/
theorem kernelPointEquiv_galois (n : ℕ) (σ : Field.absoluteGaloisGroup F)
    (x : finiteTorsionPoints E n) :
    kernelPointEquiv E n (torsionGalois E n σ x) =
      FieldGalois.pointEnd F σ ≫ kernelPointEquiv E n x := by
  have hfst (y : finiteTorsionPoints E n) :
      (toKernelPoint E n y).left ≫
        pullback.fst (multiplication E n).left η[E.X].left = y.val.toMul.left :=
    pullback.lift_fst _ _ _
  have hsnd (y : finiteTorsionPoints E n) :
      (toKernelPoint E n y).left ≫
        pullback.snd (multiplication E n).left η[E.X].left = FieldGalois.geometricPoint F :=
    pullback.lift_snd _ _ _
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc]
    change (toKernelPoint E n (torsionGalois E n σ x)).left ≫ pullback.fst _ _ =
      (FieldGalois.pointEnd F σ).left ≫ ((toKernelPoint E n x).left ≫ pullback.fst _ _)
    rw [hfst, hfst]
    rfl
  · simp only [Over.comp_left, Category.assoc]
    change (toKernelPoint E n (torsionGalois E n σ x)).left ≫ pullback.snd _ _ =
      (FieldGalois.pointEnd F σ).left ≫ ((toKernelPoint E n x).left ≫ pullback.snd _ _)
    rw [hsnd, hsnd]
    exact (Over.w (FieldGalois.pointEnd F σ)).symm

end AlgebraicGeometry.Scheme.Group.MultiplicationKernel
