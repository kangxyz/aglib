/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.IsogenyPairing
public import Aglib.AlgebraicGeometry.Group.BaseChange.MarkedKernel
public import Aglib.AlgebraicGeometry.Group.BaseChange.PointTransport

/-!
# The actual Galois-equivariant isogeny kernel pairing

The original geometric kernel points are compared by the actual pullback
adjunction. Literal field-point precomposition, semilinear family maps,
point ideals and positive frame transport prove the cyclotomic equation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Group.IsogenyPairing.Galois

attribute [local instance] Over.cartesianMonoidalCategory

open Scheme.FiniteEtale.FieldGalois

variable {F : Type u} [Field F]

/-- The original group scheme after actual extension to the chosen algebraic closure. -/
abbrev fieldGroup (G : Grp (FScheme F)) : Grp (FScheme (AlgebraicClosure F)) :=
  BaseChange.baseChangedGroup (geometricPoint F) G

/-- The actual base change of the original group morphism. -/
abbrev fieldMap {G H : Grp (FScheme F)} (f : G ⟶ H) : fieldGroup G ⟶ fieldGroup H :=
  (BaseChange.groupSchemeBaseChange (geometricPoint F)).functor.map f

/-- Literal geometric points and rational points after closure extension. -/
def pointEquiv (G : Grp (FScheme F)) :
    (Over.mk (geometricPoint F) ⟶ G.X) ≃*
      (𝟙_ (FScheme (AlgebraicClosure F)) ⟶ (fieldGroup G).X) :=
  BaseChange.PointTransport.pointedGroupPointEquiv (geometricPoint F)
    (𝟙 (Base (AlgebraicClosure F))) (geometricPoint F) (Category.id_comp _) G

@[reassoc] theorem pointEquiv_fst (G : Grp (FScheme F))
    (x : Over.mk (geometricPoint F) ⟶ G.X) :
    (pointEquiv G x).left ≫ pullback.fst G.X.hom (geometricPoint F) = x.left := by
  have h := BaseChange.PointTransport.pointedGroupPointEquiv_left (geometricPoint F)
    (𝟙 (Base (AlgebraicClosure F))) (geometricPoint F) (Category.id_comp _) G x
  exact (congrArg (fun q => q ≫ pullback.fst G.X.hom (geometricPoint F)) h).trans
    (pullback.lift_fst _ _ _)

@[reassoc] theorem pointEquiv_snd (G : Grp (FScheme F))
    (x : Over.mk (geometricPoint F) ⟶ G.X) :
    (pointEquiv G x).left ≫ pullback.snd G.X.hom (geometricPoint F) =
      𝟙 (Base (AlgebraicClosure F)) := by
  have h := BaseChange.PointTransport.pointedGroupPointEquiv_left (geometricPoint F)
    (𝟙 (Base (AlgebraicClosure F))) (geometricPoint F) (Category.id_comp _) G x
  exact (congrArg (fun q => q ≫ pullback.snd G.X.hom (geometricPoint F)) h).trans
    (pullback.lift_snd _ _ _)

/-- Naturality is the original pullback adjunction on actual points. -/
theorem pointEquiv_naturality {G H : Grp (FScheme F)} (f : G ⟶ H)
    (x : Over.mk (geometricPoint F) ⟶ G.X) :
    pointEquiv H (x ≫ f.hom.hom) = pointEquiv G x ≫ (fieldMap f).hom.hom :=
  BaseChange.PointTransport.pointedGroupPointEquiv_naturality (geometricPoint F)
    (𝟙 (Base (AlgebraicClosure F))) (geometricPoint F) (Category.id_comp _) f x

/-- The source's literal precomposition action, transported to closure-base points. -/
def pointAction (G : Grp (FScheme F)) (σ : Field.absoluteGaloisGroup F) :
    (𝟙_ (FScheme (AlgebraicClosure F)) ⟶ (fieldGroup G).X) →*
      (𝟙_ (FScheme (AlgebraicClosure F)) ⟶ (fieldGroup G).X) where
  toFun x := pointEquiv G (pointEnd F σ ≫ (pointEquiv G).symm x)
  map_one' := by rw [map_one, MonObj.comp_one, map_one]
  map_mul' x y := by rw [map_mul, MonObj.comp_mul, map_mul]

theorem pointAction_pointEquiv (G : Grp (FScheme F))
    (σ : Field.absoluteGaloisGroup F) (x : Over.mk (geometricPoint F) ⟶ G.X) :
    pointAction G σ (pointEquiv G x) = pointEquiv G (pointEnd F σ ≫ x) := by
  change pointEquiv G (pointEnd F σ ≫ (pointEquiv G).symm (pointEquiv G x)) = _
  rw [MulEquiv.symm_apply_apply]

/-- Closure-point action commutes with the actual base-changed group map. -/
theorem pointAction_naturality {G H : Grp (FScheme F)} (f : G ⟶ H)
    (σ : Field.absoluteGaloisGroup F)
    (x : 𝟙_ (FScheme (AlgebraicClosure F)) ⟶ (fieldGroup G).X) :
    pointAction H σ (x ≫ (fieldMap f).hom.hom) =
      pointAction G σ x ≫ (fieldMap f).hom.hom := by
  obtain ⟨z, rfl⟩ := (pointEquiv G).surjective x
  rw [← pointEquiv_naturality, pointAction_pointEquiv, pointAction_pointEquiv,
    ← pointEquiv_naturality, Category.assoc]

/-- The actual scheme automorphism of the chosen algebraic-closure point. -/
def pointIso (σ : Field.absoluteGaloisGroup F) : Aut (Over.mk (geometricPoint F)) where
  hom := pointEnd F σ
  inv := pointEnd F σ⁻¹
  hom_inv_id := by rw [← pointEnd_mul, mul_inv_cancel, pointEnd_one]
  inv_hom_id := by rw [← pointEnd_mul, inv_mul_cancel, pointEnd_one]

/-- The literal semilinear automorphism of a base-changed group scheme. -/
def familyIso (G : Grp (FScheme F)) (σ : Field.absoluteGaloisGroup F) :
    (fieldGroup G).X.left ≅ (fieldGroup G).X.left :=
  (Over.forget (Base F)).mapIso ((tensorLeft G.X).mapIso (pointIso σ))

@[reassoc] theorem familyIso_fst (G : Grp (FScheme F)) (σ : Field.absoluteGaloisGroup F) :
    (familyIso G σ).hom ≫ pullback.fst G.X.hom (geometricPoint F) =
      pullback.fst G.X.hom (geometricPoint F) := by
  exact congrArg Over.Hom.left (whiskerLeft_fst G.X (pointEnd F σ))

@[reassoc] theorem familyIso_snd (G : Grp (FScheme F)) (σ : Field.absoluteGaloisGroup F) :
    (familyIso G σ).hom ≫ pullback.snd G.X.hom (geometricPoint F) =
      pullback.snd G.X.hom (geometricPoint F) ≫ (pointEnd F σ).left := by
  exact congrArg Over.Hom.left (whiskerLeft_snd G.X (pointEnd F σ))

/-- The actual point-precomposition action and the semilinear family map
satisfy their literal scheme square. -/
theorem pointSquare (G : Grp (FScheme F)) (σ : Field.absoluteGaloisGroup F)
    (x : 𝟙_ (FScheme (AlgebraicClosure F)) ⟶ (fieldGroup G).X) :
    (pointEnd F σ).left ≫ x.left = (pointAction G σ x).left ≫ (familyIso G σ).hom := by
  obtain ⟨z, rfl⟩ := (pointEquiv G).surjective x
  rw [pointAction_pointEquiv]
  apply pullback.hom_ext
  · simp only [Category.assoc, familyIso_fst, pointEquiv_fst, Over.comp_left]
  · simp only [Category.assoc, familyIso_snd, pointEquiv_snd_assoc, pointEquiv_snd]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The semilinear family map carries the original identity square. -/
theorem originSquare (G : Grp (FScheme F)) (σ : Field.absoluteGaloisGroup F) :
    (pointEnd F σ).left ≫ η[(fieldGroup G).X].left =
      η[(fieldGroup G).X].left ≫ (familyIso G σ).hom := by
  have h := pointSquare G σ (1 : 𝟙_ (FScheme (AlgebraicClosure F)) ⟶ (fieldGroup G).X)
  rw [(pointAction G σ).map_one] at h
  simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using h

/-- The actual base-changed group morphism commutes with the semilinear maps. -/
theorem mapSquare {G H : Grp (FScheme F)} (f : G ⟶ H)
    (σ : Field.absoluteGaloisGroup F) :
    (familyIso G σ).hom ≫ (fieldMap f).hom.hom.left =
      (fieldMap f).hom.hom.left ≫ (familyIso H σ).hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, BaseChange.groupSchemeBaseChange_map_left_fst,
      familyIso_fst, familyIso_fst_assoc]
  · simp only [Category.assoc, BaseChange.groupSchemeBaseChange_map_left_snd,
      familyIso_snd, BaseChange.groupSchemeBaseChange_map_left_snd_assoc]

/-- The actual point action is invertible, by inverse field precomposition. -/
theorem pointAction_surjective (G : Grp (FScheme F)) (σ : Field.absoluteGaloisGroup F) :
    Function.Surjective (pointAction G σ) := by
  intro x
  obtain ⟨z, rfl⟩ := (pointEquiv G).surjective x
  refine ⟨pointEquiv G (pointEnd F σ⁻¹ ≫ z), ?_⟩
  rw [pointAction_pointEquiv, ← Category.assoc, ← pointEnd_mul,
    mul_inv_cancel, pointEnd_one, Category.id_comp]

/-- The semilinear family map has the original structural field map. -/
theorem familyIso_over (G : Grp (FScheme F)) (σ : Field.absoluteGaloisGroup F) :
    (familyIso G σ).hom ≫ (fieldGroup G).X.hom =
      (fieldGroup G).X.hom ≫ (pointEnd F σ).left := familyIso_snd G σ

/-- Literal translation conjugacy on rational point tests. -/
theorem translationSquare_on_points (G : Grp (FScheme F))
    (σ : Field.absoluteGaloisGroup F)
    (x z : 𝟙_ (FScheme (AlgebraicClosure F)) ⟶ (fieldGroup G).X) :
    z.left ≫ (Translation.translation (pointAction G σ x)).left ≫ (familyIso G σ).hom =
      z.left ≫ (familyIso G σ).hom ≫ (Translation.translation x).left := by
  obtain ⟨t, rfl⟩ := pointAction_surjective G σ z
  calc
    _ = (pointAction G σ (x * t)).left ≫ (familyIso G σ).hom := by
      rw [← Category.assoc, ← Over.comp_left, Translation.comp_translation,
        toUnit_unit, Category.id_comp, ← map_mul]
    _ = (pointEnd F σ).left ≫ (x * t).left := (pointSquare G σ (x * t)).symm
    _ = (pointEnd F σ).left ≫ (t ≫ Translation.translation x).left := by
      rw [Translation.comp_translation, toUnit_unit, Category.id_comp]
    _ = _ := by rw [Over.comp_left, ← Category.assoc, pointSquare, Category.assoc]

/-- Literal translation conjugacy as scheme morphisms, obtained from the
actual point equations and reduced finite-type curve geometry. -/
theorem translationSquare (G : Grp (FScheme F)) (hG : Curve.Properties (fieldGroup G).X)
    (σ : Field.absoluteGaloisGroup F)
    (x : 𝟙_ (FScheme (AlgebraicClosure F)) ⟶ (fieldGroup G).X) :
    (Translation.translation (pointAction G σ x)).left ≫ (familyIso G σ).hom =
      (familyIso G σ).hom ≫ (Translation.translation x).left := by
  let : IsIntegral (fieldGroup G).X.left := hG.isIntegral
  let : IsProper (fieldGroup G).X.hom := hG.proper
  let : LocallyOfFiniteType (fieldGroup G).X.hom := Curve.curveProperties_locallyOfFiniteType hG
  let : IsIso (pointEnd F σ).left := (Over.forget (Base F)).map_isIso (pointIso σ).hom
  have hleft : ((Translation.translation (pointAction G σ x)).left ≫ (familyIso G σ).hom) ≫
      (fieldGroup G).X.hom = (fieldGroup G).X.hom ≫ (pointEnd F σ).left := by
    rw [Category.assoc, familyIso_over, ← Category.assoc, Over.w]
  have hright : ((familyIso G σ).hom ≫ (Translation.translation x).left) ≫
      (fieldGroup G).X.hom = (fieldGroup G).X.hom ≫ (pointEnd F σ).left := by
    rw [Category.assoc, Over.w, familyIso_over]
  let : LocallyOfFiniteType
      (((Translation.translation (pointAction G σ x)).left ≫ (familyIso G σ).hom) ≫
        (fieldGroup G).X.hom) := by rw [hleft]; infer_instance
  apply AlgebraicGeometry.ext_of_apply_eq (fieldGroup G).X.hom Set.univ
    (isOpen_univ : IsOpen (Set.univ : Set (fieldGroup G).X.left)).isLocallyClosed
    dense_univ _ (hleft.trans hright.symm)
  intro p _ hp
  let z : 𝟙_ (FScheme (AlgebraicClosure F)) ⟶ (fieldGroup G).X :=
    Over.homMk (pointOfClosedPoint (fieldGroup G).X.hom p hp)
      (pointOfClosedPoint_comp (fieldGroup G).X.hom p hp)
  have h := congrArg (fun q : Base (AlgebraicClosure F) ⟶ (fieldGroup G).X.left =>
    q (IsLocalRing.closedPoint (AlgebraicClosure F))) (translationSquare_on_points G σ x z)
  have hz : z.left (IsLocalRing.closedPoint (AlgebraicClosure F)) = p :=
    pointOfClosedPoint_apply (fieldGroup G).X.hom p hp _
  exact (congrArg (fun q => (familyIso G σ).hom
    ((Translation.translation (pointAction G σ x)).left q)) hz).symm.trans
      (h.trans (congrArg (fun q => (Translation.translation x).left
        ((familyIso G σ).hom q)) hz))

/-- Original geometric points of the actual categorical kernel. -/
abbrev GeometricKernelPoints {G H : Grp (FScheme F)} (f : G ⟶ H) :=
  Over.mk (geometricPoint F) ⟶ (Kernel.group f).X

/-- The literal geometric kernel and the kernel after closure extension
are canonically identified by the actual point adjunction and kernel lifts. -/
def kernelEquiv {G H : Grp (FScheme F)} (f : G ⟶ H) :
    GeometricKernelPoints f ≃* KernelPoints (fieldMap f) := by
  let q : {x : Over.mk (geometricPoint F) ⟶ G.X // x ≫ f.hom.hom = 1} ≃
      {x : 𝟙_ (FScheme (AlgebraicClosure F)) ⟶ (fieldGroup G).X //
        x ≫ (fieldMap f).hom.hom = 1} := {
    toFun x := ⟨pointEquiv G x.val, by
      rw [← pointEquiv_naturality, x.property, map_one]⟩
    invFun x := ⟨(pointEquiv G).symm x.val, by
      apply (pointEquiv H).injective
      rw [pointEquiv_naturality, MulEquiv.apply_symm_apply, x.property, map_one]⟩
    left_inv x := by apply Subtype.ext; exact (pointEquiv G).symm_apply_apply x.val
    right_inv x := by apply Subtype.ext; exact (pointEquiv G).apply_symm_apply x.val }
  let e := (Kernel.pointsEquiv f (Over.mk (geometricPoint F))).trans
    (q.trans ((Kernel.pointsEquiv (fieldMap f) (𝟙_ (FScheme (AlgebraicClosure F)))).symm))
  have he (x : GeometricKernelPoints f) :
      kernelPoint (fieldMap f) (e x) = pointEquiv G (x ≫ (Kernel.inclusion f).hom.hom) := by
    exact (Kernel.square (fieldMap f)).lift_fst _ _ _
  refine { toEquiv := e, map_mul' := ?_ }
  intro x y
  apply Kernel.DeckTranslation.inclusion_points_injective (fieldMap f)
    (𝟙_ (FScheme (AlgebraicClosure F)))
  change kernelPoint (fieldMap f) (e (x * y)) =
    kernelPoint (fieldMap f) (e x * e y)
  rw [he]
  change pointEquiv G ((x * y) ≫ (Kernel.inclusion f).hom.hom) =
    (e x * e y) ≫ (Kernel.inclusion (fieldMap f)).hom.hom
  rw [MonObj.mul_comp, MonObj.mul_comp, map_mul]
  exact congrArg₂ (fun a b => a * b) (he x).symm (he y).symm

@[simp] theorem kernelEquiv_point {G H : Grp (FScheme F)} (f : G ⟶ H)
    (x : GeometricKernelPoints f) :
    kernelPoint (fieldMap f) (kernelEquiv f x) =
      pointEquiv G (x ≫ (Kernel.inclusion f).hom.hom) :=
  (Kernel.square (fieldMap f)).lift_fst _ _ _

/-- Actual source point precomposition is transported to the literal
closure-base point action, including the given kernel inclusion. -/
theorem kernelEquiv_action_point {G H : Grp (FScheme F)} (f : G ⟶ H)
    (σ : Field.absoluteGaloisGroup F) (x : GeometricKernelPoints f) :
    kernelPoint (fieldMap f) (kernelEquiv f (pointEnd F σ ≫ x)) =
      pointAction G σ (kernelPoint (fieldMap f) (kernelEquiv f x)) := by
  rw [kernelEquiv_point, kernelEquiv_point, pointAction_pointEquiv, Category.assoc]

/-- The actual base-changed curve retains its native geometric properties. -/
theorem fieldProperties (G : Grp (FScheme F)) (hG : Curve.Properties G.X) :
    Curve.Properties (fieldGroup G).X where
  smooth := MorphismProperty.pullback_snd G.X.hom (geometricPoint F) hG.smooth
  proper := MorphismProperty.pullback_snd G.X.hom (geometricPoint F) hG.proper
  connected := MorphismProperty.pullback_snd G.X.hom (geometricPoint F) hG.connected

/-- Native coherent genus is preserved by the actual closure extension. -/
theorem fieldGenus (G : Grp (FScheme F)) (hG : Curve.Properties G.X)
    (hg : Curve.coherentGenus F G.X = 1) :
    Curve.coherentGenus (AlgebraicClosure F) (fieldGroup G).X = 1 :=
  (Curve.coherentGenus_fieldBaseChange (AlgebraicClosure F)
    Cohomology.properStructureCohomologyBaseChange G.X hG).trans hg

/-- The given geometric degree survives the actual closure base change. -/
theorem fieldDegree {G H : Grp (FScheme F)} (f : G ⟶ H) (n : ℕ)
    (hn : HasGeometricDegree f.hom.hom n) : HasGeometricDegree (fieldMap f).hom.hom n := by
  intro K _ _ t y
  obtain ⟨z, rfl⟩ := (BaseChange.pullbackFiberMulEquiv (geometricPoint F) t H).surjective y
  exact (Nat.card_congr (BaseChange.mapFiberEquiv (geometricPoint F) t f z).symm).trans
    (hn K (t ≫ geometricPoint F) z)

/-- The source multiplication triangle is preserved by the actual monoidal base change. -/
theorem fieldTriangle {G H : Grp (FScheme F)} (f : G ⟶ H) (d : H ⟶ G) (n : ℕ)
    (hfd : f.hom.hom ≫ d.hom.hom = (𝟙 G.X) ^ n) :
    (fieldMap f).hom.hom ≫ (fieldMap d).hom.hom = (𝟙 (fieldGroup G).X) ^ n := by
  let P := Over.pullback (geometricPoint F)
  let : GrpObj (P.obj G.X) := (fieldGroup G).grp
  change P.map f.hom.hom ≫ P.map d.hom.hom = _
  rw [← P.map_comp, hfd]
  calc
    _ = (P.map (𝟙 G.X)) ^ n := (P.homMonoidHom (X := G.X) (M := G.X)).map_pow _ _
    _ = _ := by
      rw [P.map_id]
      rfl

variable {E D : Grp (FScheme F)} (f : E ⟶ D)
variable (hE : Curve.Properties E.X) (hD : Curve.Properties D.X)
variable [IsFinite f.hom.hom.left] [Etale f.hom.hom.left] [Surjective f.hom.hom.left]
variable (n : ℕ) (hn : HasGeometricDegree f.hom.hom n)
variable (hgE : Curve.coherentGenus F E.X = 1) (hgD : Curve.coherentGenus F D.X = 1)
variable (d : D ⟶ E) (hfd : f.hom.hom ≫ d.hom.hom = (𝟙 E.X) ^ n)

/-- The constructed perfectness candidate on the actual closure-base kernels. -/
def closurePairing : Additive (KernelPoints (fieldMap d)) →+
    (Additive (KernelPoints (fieldMap f)) →+
      Additive (rootsOfUnity n (AlgebraicClosure F))) := by
  let hE' := fieldProperties E hE
  let hD' := fieldProperties D hD
  let : SmoothOfRelativeDimension 1 (fieldGroup E).X.hom := hE'.smooth
  let : IsProper (fieldGroup E).X.hom := hE'.proper
  let : SmoothOfRelativeDimension 1 (fieldGroup D).X.hom := hD'.smooth
  let : IsProper (fieldGroup D).X.hom := hD'.proper
  let : IsFinite (fieldMap f).hom.hom.left :=
    BaseChange.map_finite (geometricPoint F) f inferInstance
  let : Etale (fieldMap f).hom.hom.left := BaseChange.map_etale (geometricPoint F) f inferInstance
  let : Surjective (fieldMap f).hom.hom.left :=
    BaseChange.map_surjective (geometricPoint F) f inferInstance
  exact kernelPairing (fieldMap f) hE' hD' n (fieldDegree f n hn)
    (fieldGenus E hE hgE) (fieldMap d) (fieldTriangle f d n hfd) (fieldGenus D hD hgD)

/-- The actual additive pairing on original geometric kernel-scheme points. -/
def geometricPairing : Additive (GeometricKernelPoints d) →+
    (Additive (GeometricKernelPoints f) →+
      Field.absoluteGaloisGroup.RootsOfUnity.Mu F n) :=
  ((AddMonoidHom.compHom' (kernelEquiv f).toAdditive.toAddMonoidHom).comp
    (closurePairing f hE hD n hn hgE hgD d hfd)).comp
      (kernelEquiv d).toAdditive.toAddMonoidHom

/-- Perfectness survives the actual closure extension and kernel-point comparisons. -/
theorem closurePairing_bijective (hu : IsUnit (n : F)) :
    Function.Bijective (closurePairing f hE hD n hn hgE hgD d hfd) := by
  let hE' := fieldProperties E hE
  let hD' := fieldProperties D hD
  let : SmoothOfRelativeDimension 1 (fieldGroup E).X.hom := hE'.smooth
  let : IsProper (fieldGroup E).X.hom := hE'.proper
  let : SmoothOfRelativeDimension 1 (fieldGroup D).X.hom := hD'.smooth
  let : IsProper (fieldGroup D).X.hom := hD'.proper
  let : IsFinite (fieldMap f).hom.hom.left :=
    BaseChange.map_finite (geometricPoint F) f inferInstance
  let : Etale (fieldMap f).hom.hom.left := BaseChange.map_etale (geometricPoint F) f inferInstance
  let : Surjective (fieldMap f).hom.hom.left :=
    BaseChange.map_surjective (geometricPoint F) f inferInstance
  exact kernelPairing_bijective (fieldMap f) hE' hD' n (fieldDegree f n hn)
    (fieldGenus E hE hgE) (fieldMap d) (fieldTriangle f d n hfd) (fieldGenus D hD hgD)
    (by simpa only [map_natCast] using hu.map (algebraMap F (AlgebraicClosure F)))

/-- The pairing on the original geometric kernels is bijective at levels
invertible in the original ground field. -/
theorem geometricPairing_bijective (hu : IsUnit (n : F)) :
    Function.Bijective (geometricPairing f hE hD n hn hgE hgD d hfd) := by
  let e := (kernelEquiv f).toAdditive
  have hp : Function.Bijective (AddMonoidHom.compHom' e.toAddMonoidHom :
      (Additive (KernelPoints (fieldMap f)) →+ Field.absoluteGaloisGroup.RootsOfUnity.Mu F n) →+
      (Additive (GeometricKernelPoints f) →+ Field.absoluteGaloisGroup.RootsOfUnity.Mu F n)) := by
    constructor
    · intro g h hh
      apply AddMonoidHom.ext
      intro x
      obtain ⟨y, rfl⟩ := e.surjective x
      exact congrArg (fun q => q y) hh
    · intro χ
      refine ⟨χ.comp e.symm.toAddMonoidHom, ?_⟩
      apply AddMonoidHom.ext
      intro x
      exact congrArg χ (e.symm_apply_apply x)
  exact hp.comp ((closurePairing_bijective f hE hD n hn hgE hgD d hfd hu).comp
    (kernelEquiv d).toAdditive.bijective)

/-- The actual pairing is equivariant for literal absolute-Galois
precomposition on geometric kernel points and the native action on roots. -/
theorem geometricPairing_galois (σ : Field.absoluteGaloisGroup F)
    (y : GeometricKernelPoints d) (x : GeometricKernelPoints f) :
    geometricPairing f hE hD n hn hgE hgD d hfd
        (Additive.ofMul (pointEnd F σ ≫ y)) (Additive.ofMul (pointEnd F σ ≫ x)) =
      σ • geometricPairing f hE hD n hn hgE hgD d hfd (Additive.ofMul y) (Additive.ofMul x) := by
  let hE' := fieldProperties E hE
  let hD' := fieldProperties D hD
  let : SmoothOfRelativeDimension 1 (fieldGroup E).X.hom := hE'.smooth
  let : IsProper (fieldGroup E).X.hom := hE'.proper
  let : SmoothOfRelativeDimension 1 (fieldGroup D).X.hom := hD'.smooth
  let : IsProper (fieldGroup D).X.hom := hD'.proper
  let : IsFinite (fieldMap f).hom.hom.left :=
    BaseChange.map_finite (geometricPoint F) f inferInstance
  let : Etale (fieldMap f).hom.hom.left := BaseChange.map_etale (geometricPoint F) f inferInstance
  let : Surjective (fieldMap f).hom.hom.left :=
    BaseChange.map_surjective (geometricPoint F) f inferInstance
  let c := (Over.forget (Base F)).mapIso (pointIso σ)
  have hy : c.hom ≫ (kernelPoint (fieldMap d) (kernelEquiv d y)).left =
      (kernelPoint (fieldMap d) (kernelEquiv d (pointEnd F σ ≫ y))).left ≫
        (familyIso D σ).hom := by
    rw [kernelEquiv_action_point]
    exact pointSquare D σ _
  have hx : (kernelTranslationHom (fieldMap f) (kernelEquiv f (pointEnd F σ ≫ x))).left ≫
      (familyIso E σ).hom = (familyIso E σ).hom ≫
        (kernelTranslationHom (fieldMap f) (kernelEquiv f x)).left := by
    change (Translation.translation
      (kernelPoint (fieldMap f) (kernelEquiv f (pointEnd F σ ≫ x)))).left ≫ _ =
      _ ≫ (Translation.translation (kernelPoint (fieldMap f) (kernelEquiv f x))).left
    rw [kernelEquiv_action_point]
    exact translationSquare E hE' σ _
  have he := evaluationCharacter_semilinear (fieldMap f) hE' hD' n (fieldDegree f n hn)
    (fieldGenus E hE hgE) (fieldMap d) (fieldTriangle f d n hfd)
    (familyIso D σ) (familyIso E σ) c (asAutomorphism F σ).toRingHom
    (mapSquare f σ) (familyIso_over E σ) (originSquare D σ)
    (kernelEquiv d y) (kernelEquiv d (pointEnd F σ ≫ y)) hy
    (kernelEquiv f x) (kernelEquiv f (pointEnd F σ ≫ x)) hx
  apply Additive.toMul.injective
  apply Subtype.ext
  exact he


/-- In characteristic zero, the same actual equation for the field fundamental
group through its proved continuous equivalence with the absolute Galois group. -/
theorem geometricPairing_fundamentalGroup [CharZero F] (g : FieldFundamentalGroup F)
    (y : GeometricKernelPoints d) (x : GeometricKernelPoints f) :
    geometricPairing f hE hD n hn hgE hgD d hfd
        (Additive.ofMul (pointEnd F ((fundamentalGroupContinuousEquiv F).symm g) ≫ y))
        (Additive.ofMul (pointEnd F ((fundamentalGroupContinuousEquiv F).symm g) ≫ x)) =
      ((fundamentalGroupContinuousEquiv F).symm g) •
        geometricPairing f hE hD n hn hgE hgD d hfd (Additive.ofMul y) (Additive.ofMul x) :=
  geometricPairing_galois f hE hD n hn hgE hgD d hfd
    ((fundamentalGroupContinuousEquiv F).symm g) y x

/-- Constructed perfect pairing on the actual two geometric kernel groups,
with the native simultaneous absolute-Galois action. -/
structure PerfectPairing {E D : Grp (FScheme F)} (f : E ⟶ D) (d : D ⟶ E) (n : ℕ) where
  /-- The biadditive map from the kernel of `d`, then the kernel of `f`, to n-th roots of unity. -/
  pairing : Additive (GeometricKernelPoints d) →+
    (Additive (GeometricKernelPoints f) →+ Field.absoluteGaloisGroup.RootsOfUnity.Mu F n)
  perfect : Function.Bijective pairing
  equivariant : ∀ (σ : Field.absoluteGaloisGroup F)
    (y : GeometricKernelPoints d) (x : GeometricKernelPoints f),
    pairing (Additive.ofMul (pointEnd F σ ≫ y)) (Additive.ofMul (pointEnd F σ ≫ x)) =
      σ • pairing (Additive.ofMul y) (Additive.ofMul x)

/-- The native finite-isogeny Cartier evaluation pairing. All geometry,
perfectness and arithmetic equivariance refer to the constructed map. -/
def perfectPairing (hu : IsUnit (n : F)) : PerfectPairing f d n where
  pairing := geometricPairing f hE hD n hn hgE hgD d hfd
  perfect := geometricPairing_bijective f hE hD n hn hgE hgD d hfd hu
  equivariant := geometricPairing_galois f hE hD n hn hgE hgD d hfd

end AlgebraicGeometry.Scheme.Group.IsogenyPairing.Galois
