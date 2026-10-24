/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Tangent.Cech.DualNumbers

/-!
# Linearity of the Čech tangent kernel under `ε ↦ a ε`

For `a ∈ k`, the `k`-algebra map `µ_a : k[ε] → k[ε]`, `x + y ε ↦ x + a y ε`
(`DualNumbers.scaleRingHom`), induces `dualScale a : X[ε] ⟶ X[ε]` over `X`, fixing the closed
fibre (`inclusion_dualScale`). On sections it fixes `p^♯ b` and sends `ε` to `a ε`, so it
pulls the transition units `1 + ε b` back to `1 + ε a b`
(`pullbackHom_dualScale_cocycleClass`).

* `DualNumbers.dualScaleKer a`: pullback along `dualScale a` on `ker(i^* : Pic X[ε] → Pic X)`.
* `DualNumbers.picardKerEquivCech_dualScale`: for a field `k`,
  `picardKerEquivCech (dualScale a)^* c = a • picardKerEquivCech c`.

This is the `Pic` form of Kleiman's `k`-linearity step for `v` (arXiv:math/0504020v1, proof of
Thm 5.11, pp. 42–43). There the `k`-structure on `P(k_ε)` comes from `µ_a`, which acts on the
top row of Square (5.11.4) through `ε ↦ aε`.
-/

@[expose] public section

noncomputable section


open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.SplitThickening
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local
open TrivSqZeroExt

universe u

namespace AlgebraicGeometry.Scheme.DualNumbers

section Ring

variable (k : Type u) [CommRing k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- `µ_a : k[ε] → k[ε]`, `x + y ε ↦ x + a y ε`. -/
def scaleRingHom (a : k) : DualNumber k →+* DualNumber k :=
  liftRingHom (inlHom k k) (inl a * DualNumber.eps) (by
    rw [mul_mul_mul_comm, DualNumber.eps_mul_eps, mul_zero])

theorem scaleRingHom_inl (a r : k) : scaleRingHom k a (inl r) = inl r :=
  liftRingHom_inl _ _ _ r

theorem scaleRingHom_eps (a : k) : scaleRingHom k a DualNumber.eps = inl a * DualNumber.eps :=
  liftRingHom_eps _ _ _

theorem fst_scaleRingHom (a : k) (x : DualNumber k) : (scaleRingHom k a x).fst = x.fst := by
  rw [scaleRingHom, liftRingHom_apply, fst_add, fst_mul, inlHom_apply, inlHom_apply, fst_inl,
    fst_inl, fst_mul, fst_inl, DualNumber.fst_eps, mul_zero, zero_mul, add_zero]

/-- `Spec µ_a`. -/
abbrev scaleMap (a : k) : Spec (.of (DualNumber k)) ⟶ Spec (.of (DualNumber k)) :=
  Spec.map (CommRingCat.ofHom (scaleRingHom k a))

theorem scaleMap_dualMap (a : k) : scaleMap k a ≫ dualMap k = dualMap k := by
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun r => scaleRingHom_inl k a r)

theorem closedPoint_scaleMap (a : k) : closedPoint k ≫ scaleMap k a = closedPoint k := by
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun x => fst_scaleRingHom k a x)

/-- The scaling `ε ↦ a ε` on `X[ε]`, over `X`. -/
def dualScale (a : k) : dualScheme k sX ⟶ dualScheme k sX :=
  pullback.lift (projection k sX) (pullback.snd sX (dualMap k) ≫ scaleMap k a) (by
    rw [Category.assoc, scaleMap_dualMap, pullback.condition])

@[reassoc (attr := simp)]
theorem dualScale_projection (a : k) : dualScale k sX a ≫ projection k sX = projection k sX :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem dualScale_snd (a : k) :
    dualScale k sX a ≫ pullback.snd sX (dualMap k) = pullback.snd sX (dualMap k) ≫ scaleMap k a :=
  pullback.lift_snd _ _ _

/-- The scaling fixes the closed fibre. -/
@[reassoc (attr := simp)]
theorem inclusion_dualScale (a : k) : inclusion k sX ≫ dualScale k sX a = inclusion k sX := by
  apply pullback.hom_ext
  · rw [Category.assoc, dualScale_projection]
  · rw [Category.assoc, dualScale_snd, inclusion_snd_assoc, closedPoint_scaleMap, inclusion_snd]

/-- The scaling sends the global section `ε` to `a ε`. -/
theorem dualScale_appTop_eps (a : k) :
    (dualScale k sX a).appTop.hom (eps k sX) =
      (projection k sX).appTop.hom (sX.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom a)) *
        eps k sX := by
  have h₁ : (dualScale k sX a).appTop.hom (eps k sX) =
      (pullback.snd sX (dualMap k)).appTop.hom ((scaleMap k a).appTop.hom
        ((Scheme.ΓSpecIso (.of (DualNumber k))).inv.hom DualNumber.eps)) := by
    have e := congrArg (fun φ => φ.appTop.hom
      ((Scheme.ΓSpecIso (.of (DualNumber k))).inv.hom DualNumber.eps)) (dualScale_snd k sX a)
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at e
    exact e
  have h₂ : (scaleMap k a).appTop.hom
      ((Scheme.ΓSpecIso (.of (DualNumber k))).inv.hom DualNumber.eps) =
      (Scheme.ΓSpecIso (.of (DualNumber k))).inv.hom (inl a * DualNumber.eps) := by
    have e := congrArg (fun φ => φ.hom DualNumber.eps)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (scaleRingHom k a)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    rw [← e, scaleRingHom_eps]
  have h₃ : (pullback.snd sX (dualMap k)).appTop.hom
      ((Scheme.ΓSpecIso (.of (DualNumber k))).inv.hom (inl a)) =
      (projection k sX).appTop.hom (sX.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom a)) := by
    have e₁ := congrArg (fun φ => φ.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e₁
    have e₂ := congrArg (fun φ => φ.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom a))
      (pullback.condition (f := sX) (g := dualMap k))
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at e₂
    change (pullback.snd sX (dualMap k)).appTop.hom
      ((Scheme.ΓSpecIso (.of (DualNumber k))).inv.hom (algebraMap k (DualNumber k) a)) = _
    rw [e₁]
    exact e₂.symm
  rw [h₁, h₂, map_mul, map_mul, h₃]
  rfl

private theorem appLE_eq_of_eq {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (hfg : f = g) (V : Z.Opens)
    (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ V) : f.appLE V W e = g.appLE V W (hfg ▸ e) := by
  subst hfg
  rfl

variable (W : X.Opens)

-- The preimages under `dualScale a ≫ p` and under `p` agree only after unfolding.
set_option backward.isDefEq.respectTransparency false in
theorem dualScale_appLE_projection (a : k)
    (e : projection k sX ⁻¹ᵁ W ≤ dualScale k sX a ⁻¹ᵁ (projection k sX ⁻¹ᵁ W)) (b : Γ(X, W)) :
    ((dualScale k sX a).appLE _ _ e).hom (((projection k sX).app W).hom b) =
      ((projection k sX).app W).hom b := by
  have h := Scheme.Hom.comp_appLE (dualScale k sX a) (projection k sX) W (projection k sX ⁻¹ᵁ W) e
  rw [appLE_eq_of_eq (dualScale_projection k sX a), Scheme.Hom.appLE_eq_app] at h
  have h' := congrArg (fun φ => φ.hom b) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h'
  exact h'.symm

theorem dualScale_appLE_restrictTop (a : k)
    (e : projection k sX ⁻¹ᵁ W ≤ dualScale k sX a ⁻¹ᵁ (projection k sX ⁻¹ᵁ W))
    (s : Γ(dualScheme k sX, ⊤)) :
    ((dualScale k sX a).appLE _ _ e).hom (restrictTop (projection k sX) s W) =
      restrictTop (projection k sX) ((dualScale k sX a).appTop.hom s) W := by
  have h := (dualScale k sX a).map_appLE e (homOfLE le_top).op
  have h' := congrArg (fun φ => φ.hom s) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h'
  exact h'

/-- The scaling multiplies the multiples of `ε` by `a`. -/
theorem dualScale_appLE_mulApp (a : k)
    (e : projection k sX ⁻¹ᵁ W ≤ dualScale k sX a ⁻¹ᵁ (projection k sX ⁻¹ᵁ W)) (b : Γ(X, W)) :
    ((dualScale k sX a).appLE _ _ e).hom ((dualIdealGenerator k sX).mulApp W b) =
      (dualIdealGenerator k sX).mulApp W (structureMap sX W a * b) := by
  change ((dualScale k sX a).appLE _ _ e).hom
      (restrictTop (projection k sX) (eps k sX) W * ((projection k sX).app W).hom b) =
    restrictTop (projection k sX) (eps k sX) W *
      ((projection k sX).app W).hom (structureMap sX W a * b)
  have hm : ∀ s t : Γ(dualScheme k sX, ⊤), restrictTop (projection k sX) (s * t) W =
      restrictTop (projection k sX) s W * restrictTop (projection k sX) t W :=
    fun s t => map_mul _ s t
  rw [map_mul, dualScale_appLE_restrictTop, dualScale_appLE_projection, dualScale_appTop_eps, hm,
    map_mul]
  have hc : restrictTop (projection k sX)
      ((projection k sX).appTop.hom (sX.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom a))) W =
      ((projection k sX).app W).hom (structureMap sX W a) := by
    have e₁ := congrArg (fun φ => φ.hom (sX.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom a)))
      ((projection k sX).naturality (homOfLE (le_top : W ≤ ⊤)).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e₁
    exact e₁.symm
  rw [hc]
  ring

/-- Pullback along the scaling on the kernel of `i^*`. -/
def dualScaleKer (a : k) :
    (pullbackHom (inclusion k sX)).ker →+ (pullbackHom (inclusion k sX)).ker :=
  ((pullbackHom (dualScale k sX a)).comp (pullbackHom (inclusion k sX)).ker.subtype).codRestrict
    _ fun c => by
      have h : pullbackHom (inclusion k sX) (pullbackHom (dualScale k sX a) c) =
          pullbackHom (inclusion k sX) c := by
        rw [← AddMonoidHom.comp_apply, ← pullbackHom_comp, inclusion_dualScale]
      exact AddMonoidHom.mem_ker.mpr (h.trans (AddMonoidHom.mem_ker.mp c.2))

@[simp]
theorem dualScaleKer_coe (a : k) (c : (pullbackHom (inclusion k sX)).ker) :
    (dualScaleKer k sX a c : PicardGroup (dualScheme k sX)) = pullbackHom (dualScale k sX a) c :=
  rfl

end Ring

section Field

variable {k : Type u} [Field k] (X : FScheme k) {ι : Type u} (U : ι → X.left.Opens)
  (hU : iSup U = ⊤)

theorem structureMap_eq_constantSection (W : X.left.Opens) :
    structureMap X.hom W = constantSection X W :=
  rfl

-- Sections over `p⁻¹ (U ⊓ V)` and over `p⁻¹ U ⊓ p⁻¹ V` agree only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- The scaling pulls the transition units `1 + ε b` back to `1 + ε a b`. -/
theorem transitionPullback_dualScale (a : k) (b : pairCocycles U) :
    Modules.Invertible.UnitCocycle.TransitionPullback (dualScale k X.hom a)
      ((dualIdealGenerator k X.hom).oneAddCocycle U b)
      ((dualIdealGenerator k X.hom).oneAddCocycle U
        ⟨Cohomology.pairSMul X U a b, Cohomology.pairSMul_mem X U a b.2⟩) := by
  intro j l e
  apply Units.ext
  change ((dualScale k X.hom a).appLE (projection k X.hom ⁻¹ᵁ (U j ⊓ U l))
      (projection k X.hom ⁻¹ᵁ (U j ⊓ U l)) e).hom
      (1 + (dualIdealGenerator k X.hom).mulApp (U j ⊓ U l)
        ((b : ∀ j l : ι, Γ(X.left, U j ⊓ U l)) j l)) =
    1 + (dualIdealGenerator k X.hom).mulApp (U j ⊓ U l)
      (constantSection X (U j ⊓ U l) a * (b : ∀ j l : ι, Γ(X.left, U j ⊓ U l)) j l)
  rw [map_add, map_one, dualScale_appLE_mulApp, structureMap_eq_constantSection]

/-- Pullback along the scaling multiplies the pair cocycle by `a`. -/
theorem pullbackHom_dualScale_cocycleClass (a : k) (b : pairCocycles U) :
    pullbackHom (dualScale k X.hom a) ((dualIdealGenerator k X.hom).cocycleClass U hU b) =
      (dualIdealGenerator k X.hom).cocycleClass U hU
        ⟨Cohomology.pairSMul X U a b, Cohomology.pairSMul_mem X U a b.2⟩ := by
  have hpre : ∀ j, dualScale k X.hom a ⁻¹ᵁ (projection k X.hom ⁻¹ᵁ U j) =
      projection k X.hom ⁻¹ᵁ U j := fun j => by
    rw [← Scheme.Hom.comp_preimage, dualScale_projection]
  exact (class_eq_iff _ _ _).mpr ⟨((dualIdealGenerator k X.hom).oneAddCocycle U b).pullbackIso
    (dualScale k X.hom a) _ hpre (transitionPullback_dualScale X U a b)
    ((projection k X.hom).iSup_preimage_eq_top hU)⟩

variable [X.left.IsSeparated] (hU₁ : ∀ j, IsAffineOpen (U j))

/-- The Čech comparison is linear for the scaling `ε ↦ a ε`. -/
theorem picardKerEquivCech_dualScale (a : k) (c : (pullbackHom (inclusion k X.hom)).ker) :
    picardKerEquivCech X U hU hU₁ (dualScaleKer k X.hom a c) =
      a • picardKerEquivCech X U hU hU₁ c := by
  set E := picardKerEquivPairCohomology k X.hom U hU hU₁ fun j l => (hU₁ j).inf (hU₁ l)
  obtain ⟨b, hb⟩ := QuotientAddGroup.mk_surjective (E c)
  have hc : c = E.symm (QuotientAddGroup.mk b) := by
    rw [hb, AddEquiv.symm_apply_apply]
  have hD : dualScaleKer k X.hom a c = E.symm (QuotientAddGroup.mk
      ⟨Cohomology.pairSMul X U a b, Cohomology.pairSMul_mem X U a b.2⟩) := by
    apply Subtype.ext
    rw [dualScaleKer_coe, hc, picardKerEquivPairCohomology_symm_mk,
      picardKerEquivPairCohomology_symm_mk]
    exact pullbackHom_dualScale_cocycleClass X U hU a b
  change (Cohomology.structureCechCohomologyLinearEquiv X U hU
      (Cohomology.isAffineOpen_cechTuple U hU₁) (injectiveResolution _) 0)
      (Cohomology.pairCohomologyEquivCech X U (E (dualScaleKer k X.hom a c))) =
    a • (Cohomology.structureCechCohomologyLinearEquiv X U hU
      (Cohomology.isAffineOpen_cechTuple U hU₁) (injectiveResolution _) 0)
      (Cohomology.pairCohomologyEquivCech X U (E c))
  rw [hD, AddEquiv.apply_symm_apply, Cohomology.pairCohomologyEquivCech_smul, hc,
    AddEquiv.apply_symm_apply, LinearEquiv.map_smul]

end Field

end AlgebraicGeometry.Scheme.DualNumbers
