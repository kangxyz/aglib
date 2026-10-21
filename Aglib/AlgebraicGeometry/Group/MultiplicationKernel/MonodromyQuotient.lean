/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.MultiplicationKernel
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GeometricConnectedness
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TorsorAction
public import Aglib.TopologicalGroup.SplitExtension

/-!
# The additive quotient from actual multiplication monodromy

The arithmetic projection kernel acts on the actual multiplication-cover fibre
by translation. The proof uses the literal pair cover and its difference `t-s`
map to the same origin kernel. Evaluation at zero is therefore an additive
quotient homomorphism, intertwines the actual Galois section by conjugation,
and is continuous for the discrete topology on the actual torsion points.

Source: `R5Lab.AlgebraicGeometry.EllipticCurve.Torsion.MultiplicationMonodromy`,
lines 52–331 and 357–405, packet SHA-256
`6eef22e0460bc2a0ef72e577392b9b174e92dc762246d54b7787960087967e89`.
The group scheme is arbitrary and commutative. The actual multiplication is
explicitly finite and etale. Only surjectivity additionally uses properness,
geometric connectedness, characteristic zero, the original geometric
Galois-category/fibre-functor classes and the universal `Stacks0BTX` and
`Stacks0387` premises. These premises are not proved here. Coefficient twists
and arithmetic character pullbacks remain downstream. Current consumer: the
same-group finite-level transition square.
-/

@[expose] public noncomputable section

open AlgebraicGeometry.Scheme.OverField (Base FScheme)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberToFinite mk)
open _root_.AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open AlgebraicGeometry.Scheme.Group.MultiplicationKernel

namespace AlgebraicGeometry.Scheme.Group.MultiplicationKernel.MonodromyQuotient
universe u
attribute [local instance] Over.cartesianMonoidalCategory
variable {F : Type u} [Field F]
  (E : Grp (FScheme F)) [IsCommMonObj E.X] (n : ℕ)

abbrev b := FieldGalois.geometricPoint F
abbrev o := η[E.X].left
abbrev x0 := b (F := F) ≫ o E
abbrev N := GeometricKernel.ArithmeticKernel F E.X.hom (o E) (Over.w η[E.X])

variable [IsFinite (multiplication E n).left] [Etale (multiplication E n).left]

/-- The literal multiplication cover, with no quotient or realization data. -/
abbrev multiplicationCover : Scheme.FiniteEtale E.X.left :=
  _root_.AlgebraicGeometry.Scheme.FiniteEtale.mk (multiplication E n).left

/-- Its origin fibre consists of precisely the native torsion points. -/
def fiberEquiv : finiteTorsionPoints E n ≃ Fiber (x0 E) (multiplicationCover E n) where
  toFun t := Over.homMk t.val.toMul.left (torsion_fibre_equation E n t)
  invFun q := by
    let p : Over.mk (b (F := F)) ⟶ E.X := Over.homMk q.left (by
      calc
        q.left ≫ E.X.hom =
            (q.left ≫ (multiplication E n).left) ≫ E.X.hom := by
          rw [Category.assoc, Over.w]
        _ = b (F := F) := by
          have hq : q.left ≫ (multiplication E n).left = x0 E := Over.w q
          rw [hq, Category.assoc, Over.w]
          exact Category.comp_id _)
    refine ⟨Additive.ofMul p, ?_⟩
    change p ^ n = 1
    rw [← point_multiplication E n]
    apply Over.OverMorphism.ext
    exact Over.w q
  left_inv t := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Over.OverMorphism.ext
    rfl
  right_inv q := by apply Over.OverMorphism.ext; rfl

/-- Evaluate an actual geometric-kernel automorphism on the literal zero lift. -/
def quotientMap (g : N E) : finiteTorsionPoints E n :=
  (fiberEquiv E n).symm
    (g.val.hom.app (multiplicationCover E n) (fiberEquiv E n 0))

theorem quotientMap_one : quotientMap E n 1 = 0 :=
  (fiberEquiv E n).symm_apply_apply 0

section Surjectivity
variable [CharZero F] [IsProper E.X.hom] [GeometricallyConnected E.X.hom]
  [GaloisCategory (Scheme.FiniteEtale (GeometricKernel.geometricBaseChange F E.X.hom))]
  [PreGaloisCategory.FiberFunctor (fiberToFinite
    (GeometricKernel.geometricPoint F E.X.hom (o E) (Over.w η[E.X])))]
  (h0BTX : GeometricKernel.Stacks0BTX F)
  (h0387 : GeometricCoverConnectedness.Stacks0387 F)

include h0BTX h0387 in
/-- Surjectivity follows from actual geometric connectedness of the source E. -/
theorem quotientMap_surjective : Function.Surjective (quotientMap E n) := by
  have hc : GeometricallyConnected ((multiplicationCover E n).obj.hom ≫ E.X.hom) := by
    change GeometricallyConnected ((multiplication E n).left ≫ E.X.hom)
    rw [Over.w]
    infer_instance
  have ht := ((GeometricCoverConnectedness.geometricallyConnected_iff_kernel_evaluation F
    E.X.hom (o E) (Over.w η[E.X]) h0BTX h0387 (multiplicationCover E n)).mp hc).2
  intro t
  obtain ⟨g, hg⟩ := ht (fiberEquiv E n 0) (fiberEquiv E n t)
  exact ⟨g, by rw [quotientMap, hg, Equiv.symm_apply_apply]⟩
end Surjectivity

attribute [local instance] GroupDescent.coverCartesian

abbrev pairCover : Scheme.FiniteEtale E.X.left
    := multiplicationCover E n ⊗ multiplicationCover E n
abbrev pairOverF : FScheme F := Over.mk ((pairCover E n).obj.hom ≫ E.X.hom)

def first : pairOverF E n ⟶ E.X := Over.homMk
  (fst (multiplicationCover E n).obj (multiplicationCover E n).obj).left (by
    rw [← Over.w (multiplication E n), ← Category.assoc]
    exact congrArg (fun f => f ≫ E.X.hom)
      (Over.w (fst (multiplicationCover E n).obj (multiplicationCover E n).obj)))

def second : pairOverF E n ⟶ E.X := Over.homMk
  (snd (multiplicationCover E n).obj (multiplicationCover E n).obj).left (by
    rw [← Over.w (multiplication E n), ← Category.assoc]
    exact congrArg (fun f => f ≫ E.X.hom)
      (Over.w (snd (multiplicationCover E n).obj (multiplicationCover E n).obj)))

omit [IsCommMonObj E.X] in
theorem pair_multiplication : first E n ≫ multiplication E n = second E n ≫ multiplication E n := by
  apply Over.OverMorphism.ext
  exact (Over.w (fst (multiplicationCover E n).obj (multiplicationCover E n).obj)).trans
    (Over.w (snd (multiplicationCover E n).obj (multiplicationCover E n).obj)).symm

theorem difference_killed : (first E n / second E n) ≫ multiplication E n = 1 := by
  rw [multiplication, MonObj.comp_pow, Category.comp_id, div_pow]
  have h := pair_multiplication E n
  simp only [point_multiplication] at h
  rw [h, div_self']

/-- Difference of two lifts lands in the literal scheme-theoretic kernel. -/
def difference : pairOverF E n ⟶ kernelScheme E n := Over.homMk
  (pullback.lift (first E n / second E n).left (pairOverF E n).hom
    (congrArg Over.Hom.left (difference_killed E n))) (pullback.lift_snd _ _ _)

abbrev kernelCover : Scheme.FiniteEtale (Base F) :=
  ⟨kernelScheme E n, inferInstance, inferInstanceAs
    (Etale (pullback.snd (multiplication E n).left η[E.X].left))⟩

abbrev relativeKernelCover : Scheme.FiniteEtale E.X.left := (baseChange E.X.hom).obj
    (kernelCover E n)

def differenceCoverMap : pairCover E n ⟶ relativeKernelCover E n := ObjectProperty.homMk
  (Over.homMk (pullback.lift (difference E n).left (pairCover E n).obj.hom
    (Over.w (difference E n))) (pullback.lift_snd _ _ _))

theorem differenceCoverMap_fst :
    (differenceCoverMap E n).hom.left ≫ pullback.fst (kernelScheme E n).hom E.X.hom =
      (difference E n).left :=
  pullback.lift_fst (f := (kernelScheme E n).hom) (g := E.X.hom)
    (difference E n).left (pairCover E n).obj.hom (Over.w (difference E n))

def pairPoint (t s : finiteTorsionPoints E n) : Fiber (x0 E) (pairCover E n) :=
  lift (fiberEquiv E n t) (fiberEquiv E n s)

def pairPointOverF (t s : finiteTorsionPoints E n) :
    Over.mk (b (F := F)) ⟶ pairOverF E n := Over.homMk (pairPoint E n t s).left (by
  change _ ≫ ((pairCover E n).obj.hom ≫ E.X.hom) = _
  rw [← Category.assoc, Over.w]
  change (b (F := F) ≫ o E) ≫ E.X.hom = b
  rw [Category.assoc, Over.w]
  exact Category.comp_id _)

theorem pairPointOverF_first (t s : finiteTorsionPoints E n) :
    pairPointOverF E n t s ≫ first E n = t.val.toMul := by
  apply Over.OverMorphism.ext
  change (lift (fiberEquiv E n t) (fiberEquiv E n s)).left ≫
    (fst (multiplicationCover E n).obj (multiplicationCover E n).obj).left = _
  have hf : (fst (multiplicationCover E n).obj (multiplicationCover E n).obj).left =
    pullback.fst (multiplicationCover E n).obj.hom (multiplicationCover E n).obj.hom := rfl
  simp only [Over.lift_left, hf, pullback.lift_fst]
  rfl

theorem pairPointOverF_second (t s : finiteTorsionPoints E n) :
    pairPointOverF E n t s ≫ second E n = s.val.toMul := by
  apply Over.OverMorphism.ext
  change (lift (fiberEquiv E n t) (fiberEquiv E n s)).left ≫
    (snd (multiplicationCover E n).obj (multiplicationCover E n).obj).left = _
  have hs : (snd (multiplicationCover E n).obj (multiplicationCover E n).obj).left =
    pullback.snd (multiplicationCover E n).obj.hom (multiplicationCover E n).obj.hom := rfl
  simp only [Over.lift_left, hs, pullback.lift_snd]
  rfl

theorem pairPoint_fst (t s : finiteTorsionPoints E n) :
    pairPoint E n t s ≫ fst (multiplicationCover E n).obj (multiplicationCover E n).obj =
      fiberEquiv E n t := by
  apply Over.OverMorphism.ext
  have h := congrArg Over.Hom.left (pairPointOverF_first E n t s)
  exact h

theorem pairPoint_snd (t s : finiteTorsionPoints E n) :
    pairPoint E n t s ≫ snd (multiplicationCover E n).obj (multiplicationCover E n).obj =
      fiberEquiv E n s := by
  apply Over.OverMorphism.ext
  have h := congrArg Over.Hom.left (pairPointOverF_second E n t s)
  exact h

def kernelFiberEquiv : Fiber (x0 E) (relativeKernelCover E n) ≃
    Fiber (b (F := F)) (kernelCover E n) :=
  (pointedFiberEquiv
    (pointedProjection (b (F := F)) E.X.hom (o E) (Over.w η[E.X]))
    (kernelCover E n)).symm

omit [IsCommMonObj E.X] in
theorem kernelFiberEquiv_left (q : Fiber (x0 E) (relativeKernelCover E n)) :
    (kernelFiberEquiv E n q).left =
      q.left ≫ pullback.fst (kernelCover E n).obj.hom E.X.hom :=
  pointFiberIso_inv_left E.X.hom (x0 E) (b (F := F))
    (Under.w (pointedProjection (b (F := F)) E.X.hom (o E) (Over.w η[E.X])))
    (kernelCover E n) q

theorem differenceCoverMap_point (p : Fiber (x0 E) (pairCover E n)) :
    (kernelFiberEquiv E n (p ≫ (differenceCoverMap E n).hom)).left =
      p.left ≫ (difference E n).left := by
  rw [kernelFiberEquiv_left]
  change (p.left ≫ (differenceCoverMap E n).hom.left) ≫
    pullback.fst (kernelScheme E n).hom E.X.hom = _
  exact (Category.assoc _ _ _).trans
    (congrArg (fun f => p.left ≫ f) (differenceCoverMap_fst E n))

theorem difference_pairPoint (t s : finiteTorsionPoints E n) :
    kernelFiberEquiv E n (pairPoint E n t s ≫ (differenceCoverMap E n).hom) =
      kernelPointEquiv E n (t - s) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [differenceCoverMap_point, Category.assoc]
    change (pairPoint E n t s).left ≫ (difference E n).left ≫
      pullback.fst _ _ = (toKernelPoint E n (t - s)).left ≫ pullback.fst _ _
    change (pairPoint E n t s).left ≫ (pullback.lift _ _ _ ≫ _) =
      pullback.lift _ _ _ ≫ _
    rw [pullback.lift_fst, pullback.lift_fst]
    change (pairPointOverF E n t s ≫ (first E n / second E n)).left =
      (t.val.toMul / s.val.toMul).left
    rw [GrpObj.comp_div, pairPointOverF_first, pairPointOverF_second]
  · exact (Over.w _).trans (Over.w _).symm

omit [IsCommMonObj E.X] in
theorem kernelFiberEquiv_evaluation (g : N E) (q : Fiber (x0 E) (relativeKernelCover E n)) :
    kernelFiberEquiv E n (g.val.hom.app (relativeKernelCover E n) q) =
      kernelFiberEquiv E n q := by
  have h := pointedMap_apply
    (pointedProjection (b (F := F)) E.X.hom (o E) (Over.w η[E.X]))
    g.val (kernelCover E n) (kernelFiberEquiv E n q)
  have hg : projectionHom (b (F := F)) E.X.hom (o E) (Over.w η[E.X]) g.val = 1 :=
    g.property
  change (projectionHom _ _ _ _ g.val).hom.app (kernelCover E n) (kernelFiberEquiv E n q) = _ at h
  rw [hg] at h
  change kernelFiberEquiv E n q = kernelFiberEquiv E n
    (g.val.hom.app (relativeKernelCover E n)
      ((kernelFiberEquiv E n).symm (kernelFiberEquiv E n q))) at h
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

def rho (g : FiberAutGroup (x0 E)) (t : finiteTorsionPoints E n) : finiteTorsionPoints E n :=
  (fiberEquiv E n).symm (g.hom.app (multiplicationCover E n) (fiberEquiv E n t))

theorem fiberEquiv_rho (g : FiberAutGroup (x0 E)) (t : finiteTorsionPoints E n) :
    fiberEquiv E n (rho E n g t) = g.hom.app (multiplicationCover E n) (fiberEquiv E n t) :=
  (fiberEquiv E n).apply_symm_apply _

theorem pairPoint_evaluation (g : FiberAutGroup (x0 E)) (t s : finiteTorsionPoints E n) :
    g.hom.app (pairCover E n) (pairPoint E n t s) =
      pairPoint E n (rho E n g t) (rho E n g s) := by
  apply CartesianMonoidalCategory.hom_ext
  · have h := FiberTorsorActions.evaluation_naturality (x0 E) g
      (Z := pairCover E n) (W := multiplicationCover E n)
      (fst (multiplicationCover E n).obj (multiplicationCover E n).obj) (pairPoint E n t s)
    rw [pairPoint_fst] at h ⊢
    exact h.symm.trans (fiberEquiv_rho E n g t).symm
  · have h := FiberTorsorActions.evaluation_naturality (x0 E) g
      (Z := pairCover E n) (W := multiplicationCover E n)
      (snd (multiplicationCover E n).obj (multiplicationCover E n).obj) (pairPoint E n t s)
    rw [pairPoint_snd] at h ⊢
    exact h.symm.trans (fiberEquiv_rho E n g s).symm

theorem rho_sub (g : N E) (t s : finiteTorsionPoints E n) :
    rho E n g.val t - rho E n g.val s = t - s := by
  have h := FiberTorsorActions.evaluation_naturality (x0 E) g.val
    (differenceCoverMap E n).hom (pairPoint E n t s)
  have hh := congrArg (kernelFiberEquiv E n) h
  rw [kernelFiberEquiv_evaluation, pairPoint_evaluation, difference_pairPoint,
    difference_pairPoint] at hh
  exact (kernelPointEquiv E n).injective hh.symm

theorem rho_kernel (g : N E) (t : finiteTorsionPoints E n) :
    rho E n g.val t = quotientMap E n g + t := by
  have h := rho_sub E n g t 0
  change rho E n g.val t - quotientMap E n g = t - 0 at h
  rw [sub_zero] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

theorem rho_mul (g h : FiberAutGroup (x0 E)) (t : finiteTorsionPoints E n) :
    rho E n (g * h) t = rho E n g (rho E n h t) := by
  unfold rho
  rw [Equiv.apply_symm_apply]
  rfl

/-- The geometric-kernel evaluation is a group homomorphism by naturality of difference. -/
theorem quotientMap_mul (g h : N E) :
    quotientMap E n (g * h) = quotientMap E n g + quotientMap E n h := by
  change rho E n (g.val * h.val) 0 = _
  rw [rho_mul, rho_kernel]
  rfl

def quotientHom : N E →* Multiplicative (finiteTorsionPoints E n) where
  toFun g := Multiplicative.ofAdd (quotientMap E n g)
  map_one' := quotientMap_one E n
  map_mul' := quotientMap_mul E n

def additiveQuotient : Additive (N E) →+ finiteTorsionPoints E n where
  toFun g := quotientMap E n g.toMul
  map_zero' := quotientMap_one E n
  map_add' g h := quotientMap_mul E n g.toMul h.toMul

/-- Origin pullback of multiplication is the original scheme-theoretic kernel. -/
def originFiberEquiv : Fiber (x0 E) (multiplicationCover E n) ≃
    Fiber (b (F := F)) (kernelCover E n) :=
  pointedFiberEquiv (pointedOrigin (b (F := F)) (o E)) (multiplicationCover E n)

theorem originFiberEquiv_fiberEquiv (t : finiteTorsionPoints E n) :
    originFiberEquiv E n (fiberEquiv E n t) = kernelPointEquiv E n t := by
  apply Over.OverMorphism.ext
  exact pointFiberIso_hom_left (o E) (b (F := F)) (x0 E) rfl
    (multiplicationCover E n) (fiberEquiv E n t)

/-- The arithmetic section gives precisely the already existing native field action. -/
theorem rho_section (σ : Field.absoluteGaloisGroup F) (t : finiteTorsionPoints E n) :
    rho E n (originHom (b (F := F)) (o E) (FieldGalois.toFundamentalGroup F σ)) t =
      torsionGalois E n σ t := by
  apply (fiberEquiv E n).injective
  rw [fiberEquiv_rho]
  change (pointedMap (pointedOrigin (b (F := F)) (o E))
    (FieldGalois.toFundamentalGroup F σ)).hom.app _ _ = _
  rw [pointedMap_apply]
  change (originFiberEquiv E n).symm
    ((FieldGalois.toFundamentalGroup F σ).hom.app (kernelCover E n)
      (originFiberEquiv E n (fiberEquiv E n t))) = _
  apply (originFiberEquiv E n).injective
  rw [Equiv.apply_symm_apply, originFiberEquiv_fiberEquiv, originFiberEquiv_fiberEquiv]
  exact (kernelPointEquiv_galois E n σ t).symm

/-- Section conjugation becomes the native Galois action on E[n]. -/
theorem quotientMap_galois (σ : Field.absoluteGaloisGroup F) (g : N E) :
    quotientMap E n (_root_.TopologicalGroup.SplitExtension.kernelConjugate
      (projectionHom (b (F := F)) E.X.hom (o E) (Over.w η[E.X]))
      (originHom (b (F := F)) (o E)) (FieldGalois.toFundamentalGroup F σ) g) =
    torsionGalois E n σ (quotientMap E n g) := by
  change rho E n ((originHom (b (F := F)) (o E) (FieldGalois.toFundamentalGroup F σ)) *
    g.val * (originHom (b (F := F)) (o E) (FieldGalois.toFundamentalGroup F σ))⁻¹) 0 = _
  rw [rho_mul, rho_mul, ← map_inv, ← map_inv, rho_section, rho_section, map_zero]
  rfl

open scoped FintypeCatDiscrete in
/-- Continuity is finite-coordinate evaluation of the actual fibre automorphism. -/
theorem quotientMap_continuous [TopologicalSpace (finiteTorsionPoints E n)]
    [DiscreteTopology (finiteTorsionPoints E n)] : Continuous (quotientMap E n) := by
  have he : Continuous (fun g : FiberAutGroup (x0 E) =>
      PreGaloisCategory.autEmbedding (fiberToFinite (x0 E)) g (multiplicationCover E n)) :=
    (continuous_apply (multiplicationCover E n)).comp continuous_induced_dom
  let ev : Aut ((fiberToFinite (x0 E)).obj (multiplicationCover E n)) → finiteTorsionPoints E n :=
    fun a => (fiberEquiv E n).symm (a.hom (fiberEquiv E n 0))
  have hev : Continuous ev := continuous_of_discreteTopology
  exact (hev.comp he).comp continuous_subtype_val

end AlgebraicGeometry.Scheme.Group.MultiplicationKernel.MonodromyQuotient
