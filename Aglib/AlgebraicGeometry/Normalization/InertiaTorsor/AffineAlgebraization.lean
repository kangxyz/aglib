/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.OverRing
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.Fullness

/-!
# Algebraization of an actual affine torsor action

An actual categorical torsor action of the Hopf group on Spec(A) produces
the literal algebraic coaction A → A ⊗ C. Counit, coassociativity and
bijectivity of its transporter are derived on every affine test algebra.
The relabelling construction retains independent object and Hom universes.
An actual finite étale cover is presented using its global-section algebra.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.MonObj
open _root_.CategoryTheory
open AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor Algebra.FiniteEtale.TorsorExtension
open Algebra.FiniteEtale.GenericMaps

namespace AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor.AffineAlgebraization
universe u v w
attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

/-- Transfer an actual torsor action across actual coefficient-group and carrier
isomorphisms. This is used for the derived coefficient marking and affine presentation. -/
def relabelTorsor {Cat : Type v} [Category.{w} Cat] [CartesianMonoidalCategory Cat]
    {G H : Grp Cat} {X Y : Cat} (τ : TorsorAction G (toUnit X))
    (eG : G ≅ H) (eX : X ≅ Y) : TorsorAction H (toUnit Y) := by
  have hGH : eG.hom.hom.hom ≫ eG.inv.hom.hom = 𝟙 G.X := by
    have h := congrArg (fun f : G ⟶ G => f.hom.hom) eG.hom_inv_id
    exact h
  have hHG : eG.inv.hom.hom ≫ eG.hom.hom.hom = 𝟙 H.X := by
    have h := congrArg (fun f : H ⟶ H => f.hom.hom) eG.inv_hom_id
    exact h
  refine {
    act := fun a x => τ.act (a ≫ eG.inv.hom.hom) (x ≫ eX.inv) ≫ eX.hom
    naturality := ?_
    one_act := ?_
    mul_act := ?_
    over := fun _ _ => toUnit_unique _ _
    transport := ?_ }
  · intro T U f a x
    rw [← Category.assoc, τ.naturality]
    simp only [Category.assoc]
  · intro T x
    rw [MonObj.one_comp, τ.one_act, Category.assoc, eX.inv_hom_id, Category.comp_id]
  · intro T a b x
    rw [MonObj.mul_comp, τ.mul_act]
    simp only [Category.assoc, eX.hom_inv_id, Category.comp_id]
  · intro T x y _
    obtain ⟨a, ha, hu⟩ := τ.transport (x ≫ eX.inv) (y ≫ eX.inv) (toUnit_unique _ _)
    refine ⟨a ≫ eG.hom.hom.hom, ?_, ?_⟩
    · change τ.act ((a ≫ eG.hom.hom.hom) ≫ eG.inv.hom.hom) (x ≫ eX.inv) ≫ eX.hom = y
      rw [Category.assoc, hGH, Category.comp_id, ha,
        Category.assoc, eX.inv_hom_id, Category.comp_id]
    · intro b hb
      have hb' : τ.act (b ≫ eG.inv.hom.hom) (x ≫ eX.inv) = y ≫ eX.inv := by
        have h := congrArg (fun z : T ⟶ Y => z ≫ eX.inv) hb
        simpa only [Category.assoc, eX.hom_inv_id, Category.comp_id] using h
      have h := congrArg (fun a : T ⟶ G.X => a ≫ eG.hom.hom.hom) (hu _ hb')
      simpa only [Category.assoc, hHG, Category.comp_id] using h

@[simp] theorem relabelTorsor_act {Cat : Type v} [Category.{w} Cat] [CartesianMonoidalCategory Cat]
    {G H : Grp Cat} {X Y T : Cat} (τ : TorsorAction G (toUnit X))
    (eG : G ≅ H) (eX : X ≅ Y) (a : T ⟶ H.X) (x : T ⟶ Y) :
    (relabelTorsor τ eG eX).act a x =
      τ.act (a ≫ eG.inv.hom.hom) (x ≫ eX.inv) ≫ eX.hom := rfl

section AffinePoints
variable (K B C D : Type u) [CommRing K] [CommRing B] [Algebra K B]
  [CommRing C] [Algebra K C] [CommRing D] [Algebra K D]

@[simp] theorem algebraPoint_comp (f : B →ₐ[K] C) (g : C →ₐ[K] D) :
    algebraPoint K C D g ≫ algebraPoint K B C f = algebraPoint K B D (g.comp f) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

end AffinePoints

private def tensorHomEquiv (K A B D : Type u) [CommRing K]
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    [CommRing D] [Algebra K D] :
    ((A ⊗[K] B) →ₐ[K] D) ≃ (A →ₐ[K] D) × (B →ₐ[K] D) where
  toFun f := (f.comp Algebra.TensorProduct.includeLeft, f.comp Algebra.TensorProduct.includeRight)
  invFun p := Algebra.TensorProduct.lift p.1 p.2 (fun _ _ => .all _ _)
  left_inv f := by
    apply Algebra.TensorProduct.ext'
    intro a b
    change f (a ⊗ₜ[K] (1 : B)) * f ((1 : A) ⊗ₜ[K] b) = f (a ⊗ₜ[K] b)
    rw [← _root_.map_mul, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
  right_inv p := Prod.ext (Algebra.TensorProduct.lift_comp_includeLeft _ _ _)
    (Algebra.TensorProduct.lift_comp_includeRight' _ _ _)

variable (K A C : Type u) [Field K] [CommRing A] [Algebra K A]
  [CommRing C] [HopfAlgebra K C] [hCocomm : Coalgebra.IsCocomm K C]
  (τ : TorsorAction (coefficientGroup K C) (toUnit (affine K A)))

/-- The genuine algebra map underlying the action, evaluated on its universal
pair of coefficient/torsor affine points. -/
def actionCoact : A →ₐ[K] A ⊗[K] C :=
  affinePointEquiv K A (A ⊗[K] C)
    (τ.act (algebraPoint K C (A ⊗[K] C) Algebra.TensorProduct.includeRight)
      (algebraPoint K A (A ⊗[K] C) Algebra.TensorProduct.includeLeft))

omit hCocomm in
theorem actionCoact_point [_hCocomm : Coalgebra.IsCocomm K C] :
    algebraPoint K A (A ⊗[K] C) (actionCoact K A C τ) =
      τ.act (algebraPoint K C (A ⊗[K] C) Algebra.TensorProduct.includeRight)
        (algebraPoint K A (A ⊗[K] C) Algebra.TensorProduct.includeLeft) :=
  (affinePointEquiv K A (A ⊗[K] C)).symm_apply_apply _

local instance : GrpObj (affine K C) := (coefficientGroup K C).grp

variable (D : Type u) [CommRing D] [Algebra K D]

/-- Naturality proves the exact pointwise Spec/algebra action dictionary on
EVERY affine test algebra, not only geometric points. -/
theorem actionCoact_eval (a : C →ₐ[K] D) (x : A →ₐ[K] D) :
    algebraPoint K A D (evaluateCoaction K A C (actionCoact K A C τ) a x) =
      τ.act (algebraPoint K C D a) (algebraPoint K A D x) := by
  change algebraPoint K A D
    ((Algebra.TensorProduct.lift x a (fun _ _ => .all _ _)).comp (actionCoact K A C τ)) = _
  rw [← algebraPoint_comp, actionCoact_point, τ.naturality,
    algebraPoint_comp, algebraPoint_comp,
    Algebra.TensorProduct.lift_comp_includeRight', Algebra.TensorProduct.lift_comp_includeLeft]

omit τ in
/-- The original Hopf counit is the unit coefficient point. -/
theorem algebraPoint_coefficient_one :
    algebraPoint K C D ((Algebra.ofId K D).comp (Bialgebra.counitAlgHom K C)) =
      (1 : affine K D ⟶ (coefficientGroup K C).X) := by
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

omit τ hCocomm in
/-- The original Hopf comultiplication gives multiplication of affine coefficient points. -/
theorem algebraPoint_coefficient_mul [_hCocomm : Coalgebra.IsCocomm K C]
    (a b : C →ₐ[K] D) :
    (algebraPoint K C D a : affine K D ⟶ (coefficientGroup K C).X) *
      (algebraPoint K C D b : affine K D ⟶ (coefficientGroup K C).X) =
      algebraPoint K C D
        ((Algebra.TensorProduct.lift a b (fun _ _ => .all _ _)).comp
          (Bialgebra.comulAlgHom K C)) := by
  change action K C C (Bialgebra.comulAlgHom K C)
    (algebraPoint K C D b) (algebraPoint K C D a) = _
  rw [action_algebraPoint]
  rfl

/-- The extracted algebra action has the genuine counit law on all affine points. -/
theorem actionCoact_eval_one (x : A →ₐ[K] D) :
    evaluateCoaction K A C (actionCoact K A C τ)
      ((Algebra.ofId K D).comp (Bialgebra.counitAlgHom K C)) x = x := by
  apply (affinePointEquiv K A D).symm.injective
  change algebraPoint K A D _ = algebraPoint K A D x
  rw [actionCoact_eval, algebraPoint_coefficient_one, τ.one_act]

/-- Commutativity of the coefficient group converts the actual left torsor
action into the right coaction convention used by OriginalTorsorData. -/
theorem actionCoact_eval_mul (a b : C →ₐ[K] D) (x : A →ₐ[K] D) :
    evaluateCoaction K A C (actionCoact K A C τ)
      ((Algebra.TensorProduct.lift a b (fun _ _ => .all _ _)).comp (Bialgebra.comulAlgHom K C)) x =
      evaluateCoaction K A C (actionCoact K A C τ) b
        (evaluateCoaction K A C (actionCoact K A C τ) a x) := by
  apply (affinePointEquiv K A D).symm.injective
  change algebraPoint K A D _ = algebraPoint K A D _
  rw [actionCoact_eval, ← algebraPoint_coefficient_mul,
    coefficient_points_comm K C (algebraPoint K C D a) (algebraPoint K C D b), τ.mul_act,
    ← actionCoact_eval, ← actionCoact_eval]

/-- Unique transport on every affine test algebra is derived from the actual
scheme torsor's transport, with no algebraic transporter premise. -/
theorem actionCoact_eval_transport (x y : A →ₐ[K] D) :
    ∃! a : C →ₐ[K] D, evaluateCoaction K A C (actionCoact K A C τ) a x = y := by
  obtain ⟨a, ha, hu⟩ := τ.transport (algebraPoint K A D x) (algebraPoint K A D y)
    (toUnit_unique _ _)
  let a' : C →ₐ[K] D := affinePointEquiv K C D a
  have hp : algebraPoint K C D a' = a := (affinePointEquiv K C D).symm_apply_apply a
  refine ⟨a', ?_, ?_⟩
  · apply (affinePointEquiv K A D).symm.injective
    change algebraPoint K A D _ = algebraPoint K A D y
    rw [actionCoact_eval, hp]
    exact ha
  · intro b hb
    apply (affinePointEquiv K C D).symm.injective
    change algebraPoint K C D b = algebraPoint K C D a'
    rw [hp]
    apply hu
    rw [← actionCoact_eval, hb]

/-- The actual counit algebra diagram follows by testing the unit action on A. -/
theorem actionCoact_counit :
    (coactionCounit K A C (Bialgebra.counitAlgHom K C)).comp (actionCoact K A C τ) =
      AlgHom.id K A := by
  have h := actionCoact_eval_one K A C τ A (AlgHom.id K A)
  have hc : Algebra.TensorProduct.lift (AlgHom.id K A)
      ((Algebra.ofId K A).comp (Bialgebra.counitAlgHom K C)) (fun _ _ => .all _ _) =
      coactionCounit K A C (Bialgebra.counitAlgHom K C) := by
    apply Algebra.TensorProduct.ext'
    intro a c
    simp [coactionCounit, Algebra.smul_def, _root_.mul_comm]
  change (Algebra.TensorProduct.lift (AlgHom.id K A)
    ((Algebra.ofId K A).comp (Bialgebra.counitAlgHom K C)) (fun _ _ => .all _ _)).comp
      (actionCoact K A C τ) = AlgHom.id K A at h
  rwa [hc] at h

/-- The actual coassociativity algebra diagram follows on the universal triple
affine test algebra, preserving the original right-coaction convention. -/
theorem actionCoact_coassoc :
    (Algebra.TensorProduct.map (AlgHom.id K A) (Bialgebra.comulAlgHom K C)).comp
      (actionCoact K A C τ) =
    (Algebra.TensorProduct.assoc K K K A C C).toAlgHom.comp
      ((Algebra.TensorProduct.map (actionCoact K A C τ) (AlgHom.id K C)).comp
        (actionCoact K A C τ)) := by
  let T := A ⊗[K] (C ⊗[K] C)
  let x : A →ₐ[K] T := Algebra.TensorProduct.includeLeft
  let a : C →ₐ[K] T :=
    Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft
  let b : C →ₐ[K] T :=
    Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight
  have hab : Algebra.TensorProduct.lift a b (fun _ _ => .all _ _) =
      (Algebra.TensorProduct.includeRight : (C ⊗[K] C) →ₐ[K] T) := by
    apply Algebra.TensorProduct.ext'
    intro c d
    change ((1 : A) ⊗ₜ[K] (c ⊗ₜ[K] (1 : C))) *
      ((1 : A) ⊗ₜ[K] ((1 : C) ⊗ₜ[K] d)) = (1 : A) ⊗ₜ[K] (c ⊗ₜ[K] d)
    simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, _root_.mul_one]
  have hl : Algebra.TensorProduct.lift x
      ((Algebra.TensorProduct.lift a b (fun _ _ => .all _ _)).comp (Bialgebra.comulAlgHom K C))
      (fun _ _ => .all _ _) =
      Algebra.TensorProduct.map (AlgHom.id K A) (Bialgebra.comulAlgHom K C) := by
    rw [hab]
    apply Algebra.TensorProduct.ext'
    intro u v
    change (u ⊗ₜ[K] (1 : C ⊗[K] C)) *
      ((1 : A) ⊗ₜ[K] Bialgebra.comulAlgHom K C v) = u ⊗ₜ[K] Bialgebra.comulAlgHom K C v
    simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, _root_.mul_one]
  have hr : Algebra.TensorProduct.lift
      (evaluateCoaction K A C (actionCoact K A C τ) a x) b (fun _ _ => .all _ _) =
      (Algebra.TensorProduct.assoc K K K A C C).toAlgHom.comp
        (Algebra.TensorProduct.map (actionCoact K A C τ) (AlgHom.id K C)) := by
    apply Algebra.TensorProduct.ext'
    intro u v
    change (Algebra.TensorProduct.lift x a (fun _ _ => .all _ _) (actionCoact K A C τ u)) * b v =
      (Algebra.TensorProduct.assoc K K K A C C) ((actionCoact K A C τ u) ⊗ₜ[K] v)
    generalize actionCoact K A C τ u = z
    induction z using TensorProduct.inductionOn with
    | tmul u c =>
      change (u ⊗ₜ[K] (1 : C ⊗[K] C)) * ((1 : A) ⊗ₜ[K] (c ⊗ₜ[K] (1 : C))) *
        ((1 : A) ⊗ₜ[K] ((1 : C) ⊗ₜ[K] v)) = u ⊗ₜ[K] (c ⊗ₜ[K] v)
      simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, _root_.mul_one]
    | add z w hz hw => simp only [map_add, TensorProduct.add_tmul, add_mul, hz, hw]
  have h := actionCoact_eval_mul K A C τ T a b x
  change (Algebra.TensorProduct.lift x
    ((Algebra.TensorProduct.lift a b (fun _ _ => .all _ _)).comp (Bialgebra.comulAlgHom K C))
    (fun _ _ => .all _ _)).comp (actionCoact K A C τ) =
    (Algebra.TensorProduct.lift (evaluateCoaction K A C (actionCoact K A C τ) a x) b
      (fun _ _ => .all _ _)).comp (actionCoact K A C τ) at h
  simpa only [hl, hr, AlgHom.comp_assoc] using h

/-- The full algebraic coaction, whose laws were derived from the actual scheme action. -/
def algebraCoactionOfTorsor :
    AlgebraCoaction K A C (Bialgebra.counitAlgHom K C) (Bialgebra.comulAlgHom K C) where
  coact := actionCoact K A C τ
  counit := actionCoact_counit K A C τ
  coassoc := actionCoact_coassoc K A C τ

/-- Actual unique scheme transport makes the algebraic transporter bijective
on Hom(-,D) for every affine test algebra D. -/
theorem transporter_precomp_bijective :
    Function.Bijective (fun f : (A ⊗[K] C) →ₐ[K] D =>
      f.comp (transporter K A C (actionCoact K A C τ))) := by
  let E₁ := tensorHomEquiv K A C D
  let E₂ := tensorHomEquiv K A A D
  let F : (A →ₐ[K] D) × (C →ₐ[K] D) → (A →ₐ[K] D) × (A →ₐ[K] D) :=
    fun p => (p.1, evaluateCoaction K A C (actionCoact K A C τ) p.2 p.1)
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨x, a⟩ ⟨y, b⟩ h
      have hxy : x = y := congrArg Prod.fst h
      subst y
      have hab : evaluateCoaction K A C (actionCoact K A C τ) a x =
          evaluateCoaction K A C (actionCoact K A C τ) b x := congrArg Prod.snd h
      obtain ⟨z, hz, hu⟩ := actionCoact_eval_transport K A C τ D x
        (evaluateCoaction K A C (actionCoact K A C τ) a x)
      exact Prod.ext rfl ((hu a rfl).trans (hu b hab.symm).symm)
    · rintro ⟨x, y⟩
      obtain ⟨a, ha, _⟩ := actionCoact_eval_transport K A C τ D x y
      exact ⟨(x, a), Prod.ext rfl ha⟩
  have hcomm (f : (A ⊗[K] C) →ₐ[K] D) :
      E₂ (f.comp (transporter K A C (actionCoact K A C τ))) = F (E₁ f) := by
    apply Prod.ext
    · change (f.comp (transporter K A C (actionCoact K A C τ))).comp
        Algebra.TensorProduct.includeLeft = f.comp Algebra.TensorProduct.includeLeft
      rw [AlgHom.comp_assoc, transporter, Algebra.TensorProduct.lift_comp_includeLeft]
    · have hlift : Algebra.TensorProduct.lift
          (f.comp Algebra.TensorProduct.includeLeft) (f.comp Algebra.TensorProduct.includeRight)
          (fun _ _ => .all _ _) = f := (tensorHomEquiv K A C D).symm_apply_apply f
      change (f.comp (transporter K A C (actionCoact K A C τ))).comp
        Algebra.TensorProduct.includeRight =
        (Algebra.TensorProduct.lift (f.comp Algebra.TensorProduct.includeLeft)
          (f.comp Algebra.TensorProduct.includeRight) (fun _ _ => .all _ _)).comp
          (actionCoact K A C τ)
      rw [hlift, AlgHom.comp_assoc, transporter, Algebra.TensorProduct.lift_comp_includeRight']
  constructor
  · intro f g hfg
    apply E₁.injective
    apply hF.injective
    rw [← hcomm f, ← hcomm g]
    exact congrArg E₂ hfg
  · intro g
    obtain ⟨p, hp⟩ := hF.surjective (E₂ g)
    refine ⟨E₁.symm p, E₂.injective ?_⟩
    rw [hcomm, E₁.apply_symm_apply]
    exact hp

/-- The actual algebraic transporter is bijective. The inverse is extracted
from unique affine transport; neither a final transporter nor its inverse is supplied. -/
theorem actionCoact_transporter_bijective :
    Function.Bijective (transporter K A C (actionCoact K A C τ)) := by
  let t := transporter K A C (actionCoact K A C τ)
  obtain ⟨g, hg⟩ := (transporter_precomp_bijective K A C τ (A ⊗[K] A)).surjective
    (AlgHom.id K (A ⊗[K] A))
  have hleft : g.comp t = AlgHom.id K (A ⊗[K] A) := hg
  have hright : t.comp g = AlgHom.id K (A ⊗[K] C) := by
    apply (transporter_precomp_bijective K A C τ (A ⊗[K] C)).injective
    change (t.comp g).comp t = (AlgHom.id K (A ⊗[K] C)).comp t
    rw [AlgHom.comp_assoc, hleft]
    rfl
  constructor
  · intro x y hxy
    exact (DFunLike.congr_fun hleft x).symm.trans
      ((congrArg g hxy).trans (DFunLike.congr_fun hleft y))
  · intro y
    exact ⟨g y, DFunLike.congr_fun hright y⟩

section CoverPresentation
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber)
open AlgebraicGeometry.Scheme.FiniteEtale.Adic
open AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.OverRing

/-- The already proved finite-etale affine coordinate construction presents
an actual field cover as the spectrum of its actual global-section algebra. -/
def affineCoverPresentation (K : Type u) [Field K] (Y : Scheme.FiniteEtale (Spec (.of K))) :
    letI := sectionsAlgebra K Y
    Y.obj ≅ affine K (sections K Y) := by
  letI := sectionsAlgebra K Y
  exact ((_root_.AlgebraicGeometry.Scheme.FiniteEtale.forget (Spec (.of K))).mapIso
    (specCoverIso K Y)).symm

/-- The actual Ω-point gives an actual K-algebra map from the coordinate algebra. -/
def affineCoverPoint (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    (Y : Scheme.FiniteEtale (Spec (.of K))) (p : Fiber (basePoint K Ω) Y) :
    letI := sectionsAlgebra K Y
    sections K Y →ₐ[K] Ω := by
  letI := sectionsAlgebra K Y
  exact affinePointEquiv K (sections K Y) Ω (p ≫ (affineCoverPresentation K Y).hom)

/-- The affine algebra point is literally the transported scheme point. -/
theorem algebraPoint_affineCoverPoint (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    (Y : Scheme.FiniteEtale (Spec (.of K))) (p : Fiber (basePoint K Ω) Y) :
    letI := sectionsAlgebra K Y
    algebraPoint K (sections K Y) Ω (affineCoverPoint K Ω Y p) =
      p ≫ (affineCoverPresentation K Y).hom := by
  let := sectionsAlgebra K Y
  exact (affinePointEquiv K (sections K Y) Ω).symm_apply_apply _

/-- An actual Ω-point derives nontriviality of the coordinate algebra. -/
theorem sections_nontrivial_of_point (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    (Y : Scheme.FiniteEtale (Spec (.of K))) (p : Fiber (basePoint K Ω) Y) :
    Nontrivial (sections K Y) := by
  let := sectionsAlgebra K Y
  exact (affineCoverPoint K Ω Y p).toRingHom.domain_nontrivial

end CoverPresentation

end AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor.AffineAlgebraization
