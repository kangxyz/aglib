/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.HomFunctor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorFaithful
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.LocalSplitting
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The actual two-section sequence of a line bundle

The first arrow is the signed original dual-evaluation pair, and the second
arrow is the original coproduct map. Native local lifting supplies an actual
right inverse on a line chart. The resulting local splittings prove short exactness
on every scheme, without a field, Noetherianity or flatness assumption.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.InternalHom

attribute [local instance] Abelian.hasFiniteBiproducts

universe u v w

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X : Scheme.{u}}

private instance overAdditive (U : X.Opens) :
    (SheafOfModules.overFunctor X.ringCatSheaf U).Additive where
  map_add := by intros; rfl

private theorem unitEnd_commute (U : X.Opens)
    (a b : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U)) : a ≫ b = b ≫ a := by
  apply SheafOfModules.hom_ext
  ext V : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change Γ(X, V.unop.left) at r
  let α : Γ(X, V.unop.left) →ₗ[Γ(X, V.unop.left)] Γ(X, V.unop.left) :=
    (a.val.app V).hom
  let β : Γ(X, V.unop.left) →ₗ[Γ(X, V.unop.left)] Γ(X, V.unop.left) :=
    (b.val.app V).hom
  have ha (z : Γ(X, V.unop.left)) : α z = z * α 1 := by
    simpa only [smul_eq_mul, mul_one] using α.map_smul z
      (1 : Γ(X, V.unop.left))
  have hb (z : Γ(X, V.unop.left)) : β z = z * β 1 := by
    simpa only [smul_eq_mul, mul_one] using β.map_smul z
      (1 : Γ(X, V.unop.left))
  change β (α r) = α (β r)
  rw [hb (α r), ha r, ha (β r), hb r]
  ring

private theorem dualSection_over_frame (L : LineBundle X) (U : X.Opens)
    (e : L.val.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (t : SheafOfModules.unit X.ringCatSheaf ⟶ L.val) :
    (SheafOfModules.overFunctor X.ringCatSheaf U).map (dualSection X t) =
      (dualLocalIso X L.val U e).hom ≫
        (SheafOfModules.overFunctor X.ringCatSheaf U).map t ≫ e.hom := by
  apply SheafOfModules.hom_ext
  ext V : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ell
  let a : Γ(X, V.unop.left) :=
    e.hom.val.app V (t.val.app (op V.unop.left) (1 : Γ(X, V.unop.left)))
  let m : L.val.val.obj (op V.unop.left) :=
    e.inv.val.app V (1 : Γ(X, V.unop.left))
  have hm : a • m = t.val.app (op V.unop.left) (1 : Γ(X, V.unop.left)) := by
    have h := (e.inv.val.app V).hom.map_smul a (1 : Γ(X, V.unop.left))
    change e.inv.val.app V (a * (1 : Γ(X, V.unop.left))) = a • m at h
    rw [mul_one] at h
    rw [← h]
    exact congrArg (fun q : L.val.over U ⟶ L.val.over U =>
      q.val.app V (t.val.app (op V.unop.left) (1 : Γ(X, V.unop.left)))) e.hom_inv_id
  let c : Γ(X, V.unop.left) :=
    ell.val.app (op (Over.mk (𝟙 V.unop.left))) m
  change ell.val.app (op (Over.mk (𝟙 V.unop.left)))
      (t.val.app (op V.unop.left) (1 : Γ(X, V.unop.left))) =
    e.hom.val.app V (t.val.app (op V.unop.left) c)
  have hell := ell.property (op (Over.mk (𝟙 V.unop.left))) a m
  change ell.val.app (op (Over.mk (𝟙 V.unop.left))) (a • m) = a * c at hell
  rw [hm] at hell
  rw [hell]
  have ht := (t.val.app (op V.unop.left)).hom.map_smul c
    (1 : Γ(X, V.unop.left))
  change t.val.app (op V.unop.left) (c * (1 : Γ(X, V.unop.left))) =
    c • t.val.app (op V.unop.left) (1 : Γ(X, V.unop.left)) at ht
  rw [mul_one] at ht
  rw [ht, (e.hom.val.app V).hom.map_smul]
  change a * c = c * a
  exact mul_comm a c

private theorem dualSection_exchange_over (L : LineBundle X) (U : X.Opens)
    (e : L.val.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ L.val) :
    (SheafOfModules.overFunctor X.ringCatSheaf U).map (dualSection X b) ≫
        (SheafOfModules.overFunctor X.ringCatSheaf U).map a =
      (SheafOfModules.overFunctor X.ringCatSheaf U).map (dualSection X a) ≫
        (SheafOfModules.overFunctor X.ringCatSheaf U).map b := by
  let F := SheafOfModules.overFunctor X.ringCatSheaf U
  have ha : F.map (dualSection X a) =
      (dualLocalIso X L.val U e).hom ≫ F.map a ≫ e.hom :=
    dualSection_over_frame L U e a
  have hb : F.map (dualSection X b) =
      (dualLocalIso X L.val U e).hom ≫ F.map b ≫ e.hom :=
    dualSection_over_frame L U e b
  apply (cancel_mono e.hom).mp
  calc
    (F.map (dualSection X b) ≫ F.map a) ≫ e.hom =
        (dualLocalIso X L.val U e).hom ≫ (F.map b ≫ e.hom) ≫
          (F.map a ≫ e.hom) := by
      rw [hb]
      simp only [Category.assoc]
    _ = (dualLocalIso X L.val U e).hom ≫ (F.map a ≫ e.hom) ≫
          (F.map b ≫ e.hom) := by
      rw [unitEnd_commute U (F.map b ≫ e.hom) (F.map a ≫ e.hom)]
    _ = (F.map (dualSection X a) ≫ F.map b) ≫ e.hom := by
      rw [ha]
      simp only [Category.assoc]

private theorem restrict_map_eq_zero_of_over {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) (h : (SheafOfModules.overFunctor X.ringCatSheaf U).map f = 0) :
    (restrictFunctor U.ι).map f = 0 := by
  apply (cancel_epi ((overFunctorEquiv U).hom.app M)).mp
  calc
    (overFunctorEquiv U).hom.app M ≫ (restrictFunctor U.ι).map f =
        (overEquiv U).functor.map
          ((SheafOfModules.overFunctor X.ringCatSheaf U).map f) ≫
            (overFunctorEquiv U).hom.app N := ((overFunctorEquiv U).hom.naturality f).symm
    _ = 0 := by rw [h, Functor.map_zero, zero_comp]
    _ = (overFunctorEquiv U).hom.app M ≫ 0 := by simp

private theorem dualSection_exchange (L : LineBundle X)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ L.val) :
    dualSection X b ≫ a = dualSection X a ≫ b := by
  apply sub_eq_zero.mp
  apply eq_zero_of_local_restrict X
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := (isLocallyRankOne_iff_local_unit X L.val).mp L.property x
  refine ⟨U, hx, restrict_map_eq_zero_of_over _ U ?_⟩
  rw [Functor.map_sub, Functor.map_comp, Functor.map_comp,
    dualSection_exchange_over L U e a b, sub_self]

/-- The canonical projection from the original two-summand coproduct. -/
def twoSectionProjection (X : Scheme.{u}) (i : ULift.{u} (Fin 2)) :
    (∐ fun _ : ULift.{u} (Fin 2) => SheafOfModules.unit X.ringCatSheaf) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  Sigma.desc (fun j => if j = i then 𝟙 _ else 0)

@[reassoc (attr := simp)]
theorem twoSectionInclusion_projection (i j : ULift.{u} (Fin 2)) :
    Sigma.ι (fun _ : ULift.{u} (Fin 2) => SheafOfModules.unit X.ringCatSheaf) i ≫
        twoSectionProjection X j = if i = j then 𝟙 _ else 0 := by
  rw [twoSectionProjection, Sigma.ι_comp_desc]

/-- The literal signed dual-evaluation pair into the original coproduct. -/
def twoSectionKernelMap (L : LineBundle X)
    (s : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶ L.val)) :
    (dualLineBundle X L).val ⟶
      ∐ fun _ : ULift.{u} (Fin 2) => SheafOfModules.unit X.ringCatSheaf :=
  (-dualSection X (s ⟨1⟩)) ≫
      Sigma.ι (fun _ : ULift.{u} (Fin 2) => SheafOfModules.unit X.ringCatSheaf) ⟨0⟩ +
    dualSection X (s ⟨0⟩) ≫
      Sigma.ι (fun _ : ULift.{u} (Fin 2) => SheafOfModules.unit X.ringCatSheaf) ⟨1⟩

@[reassoc (attr := simp)]
theorem twoSectionKernelMap_projection_zero (L : LineBundle X)
    (s : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶ L.val)) :
    twoSectionKernelMap L s ≫ twoSectionProjection X ⟨0⟩ = -dualSection X (s ⟨1⟩) := by
  simp [twoSectionKernelMap, Preadditive.add_comp, Category.assoc]

@[reassoc (attr := simp)]
theorem twoSectionKernelMap_projection_one (L : LineBundle X)
    (s : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶ L.val)) :
    twoSectionKernelMap L s ≫ twoSectionProjection X ⟨1⟩ = dualSection X (s ⟨0⟩) := by
  simp [twoSectionKernelMap, Preadditive.add_comp, Category.assoc]

/-- The first component is minus evaluation on the original second section. -/
theorem twoSectionKernelMap_projection_zero_apply (L : LineBundle X)
    (s : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶ L.val))
    (U : X.Opens) (ell : (dualSheaf X L.val).val.obj (op U)) :
    (twoSectionKernelMap L s ≫ twoSectionProjection X ⟨0⟩).val.app (op U) ell =
      -ell.val.app (op (Over.mk (𝟙 U)))
        ((s ⟨1⟩).val.app (op U) (1 : Γ(X, U))) := by
  rw [twoSectionKernelMap_projection_zero]
  change -((dualSection X (s ⟨1⟩)).val.app (op U) ell) = _
  rw [dualSection_apply]

/-- The second component is evaluation on the original first section. -/
theorem twoSectionKernelMap_projection_one_apply (L : LineBundle X)
    (s : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶ L.val))
    (U : X.Opens) (ell : (dualSheaf X L.val).val.obj (op U)) :
    (twoSectionKernelMap L s ≫ twoSectionProjection X ⟨1⟩).val.app (op U) ell =
      ell.val.app (op (Over.mk (𝟙 U)))
        ((s ⟨0⟩).val.app (op U) (1 : Γ(X, U))) := by
  rw [twoSectionKernelMap_projection_one]
  rfl

@[reassoc (attr := simp)]
theorem twoSectionKernelMap_comp (L : LineBundle X)
    (s : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶ L.val)) :
    twoSectionKernelMap L s ≫ Sigma.desc s = 0 := by
  simp only [twoSectionKernelMap, Preadditive.add_comp, Category.assoc,
    Sigma.ι_comp_desc, Preadditive.neg_comp]
  rw [dualSection_exchange L (s ⟨0⟩) (s ⟨1⟩), neg_add_cancel]

/-- The actual two-section complex, with the original epimorphic row as its second arrow. -/
def twoSectionSequence (L : LineBundle X)
    (s : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶ L.val)) :
    ShortComplex X.Modules :=
  ShortComplex.mk (twoSectionKernelMap L s) (Sigma.desc s) (twoSectionKernelMap_comp L s)

@[simp] theorem twoSectionSequence_f (L : LineBundle X)
    (s : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶ L.val)) :
    (twoSectionSequence L s).f = twoSectionKernelMap L s := rfl

@[simp] theorem twoSectionSequence_g (L : LineBundle X)
    (s : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶ L.val)) :
    (twoSectionSequence L s).g = Sigma.desc s := rfl

private theorem pair_eta :
    twoSectionProjection X ⟨0⟩ ≫
        Sigma.ι (fun _ : ULift.{u} (Fin 2) => SheafOfModules.unit X.ringCatSheaf) ⟨0⟩ +
      twoSectionProjection X ⟨1⟩ ≫
        Sigma.ι (fun _ : ULift.{u} (Fin 2) => SheafOfModules.unit X.ringCatSheaf) ⟨1⟩ =
      𝟙 _ := by
  apply Sigma.hom_ext
  rintro ⟨i⟩
  fin_cases i <;> simp [Preadditive.comp_add]

section MappedPair

variable {C : Type v} [Category.{w} C] [Preadditive C]
  (F : X.Modules ⥤ C) [F.Additive]

@[reassoc (attr := simp)]
private theorem mapped_inclusion_projection (i j : ULift.{u} (Fin 2)) :
    F.map (Sigma.ι (fun _ : ULift.{u} (Fin 2) =>
      SheafOfModules.unit X.ringCatSheaf) i) ≫ F.map (twoSectionProjection X j) =
        if i = j then 𝟙 _ else 0 := by
  rw [← F.map_comp, twoSectionInclusion_projection]
  split <;> simp_all

omit [Preadditive C] [F.Additive] in
@[reassoc (attr := simp)]
private theorem mapped_inclusion_row (L : LineBundle X)
    (s : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶ L.val))
    (i : ULift.{u} (Fin 2)) :
    F.map (Sigma.ι (fun _ : ULift.{u} (Fin 2) =>
      SheafOfModules.unit X.ringCatSheaf) i) ≫ F.map (Sigma.desc s) = F.map (s i) := by
  rw [← F.map_comp, Sigma.ι_comp_desc]

end MappedPair

section PairFrames

variable {C : Type v} [Category.{w} C] [Preadditive C]

private theorem pair_hom_ext {P M N : C} (i₀ i₁ : P ⟶ M) (p₀ p₁ : M ⟶ P)
    (hη : p₀ ≫ i₀ + p₁ ≫ i₁ = 𝟙 M) {a b : M ⟶ N}
    (h₀ : i₀ ≫ a = i₀ ≫ b) (h₁ : i₁ ≫ a = i₁ ≫ b) : a = b := by
  calc
    a = (p₀ ≫ i₀ + p₁ ≫ i₁) ≫ a := by rw [hη, Category.id_comp]
    _ = p₀ ≫ (i₀ ≫ a) + p₁ ≫ (i₁ ≫ a) := by
      simp only [Preadditive.add_comp, Category.assoc]
    _ = p₀ ≫ (i₀ ≫ b) + p₁ ≫ (i₁ ≫ b) := by rw [h₀, h₁]
    _ = (p₀ ≫ i₀ + p₁ ≫ i₁) ≫ b := by
      simp only [Preadditive.add_comp, Category.assoc]
    _ = b := by rw [hη, Category.id_comp]

/-- The signed two-by-two calculation is performed with abstract objects, so
its identities do not unfold the concrete sheaf and restriction constructions. -/
private def frameSplitting (S : ShortComplex C) {P : C}
    (d : S.X₁ ≅ P) (e : S.X₃ ≅ P)
    (i₀ i₁ : P ⟶ S.X₂) (p₀ p₁ : S.X₂ ⟶ P)
    (hη : p₀ ≫ i₀ + p₁ ≫ i₁ = 𝟙 S.X₂)
    (h₀₀ : i₀ ≫ p₀ = 𝟙 P) (h₀₁ : i₀ ≫ p₁ = 0)
    (h₁₀ : i₁ ≫ p₀ = 0) (h₁₁ : i₁ ≫ p₁ = 𝟙 P)
    (h : S.X₃ ⟶ S.X₂) (hh : h ≫ S.g = 𝟙 S.X₃)
    (hf : S.f = d.hom ≫
      ((-(i₁ ≫ S.g ≫ e.hom)) ≫ i₀ + (i₀ ≫ S.g ≫ e.hom) ≫ i₁))
    (hcomm : ∀ a b : P ⟶ P, a ≫ b = b ≫ a) : S.Splitting := by
  let u₀ : P ⟶ P := i₀ ≫ S.g ≫ e.hom
  let u₁ : P ⟶ P := i₁ ≫ S.g ≫ e.hom
  let a : P ⟶ P := e.inv ≫ h ≫ p₀
  let b : P ⟶ P := e.inv ≫ h ≫ p₁
  have hv : e.inv ≫ h = a ≫ i₀ + b ≫ i₁ := by
    calc
      e.inv ≫ h = (e.inv ≫ h) ≫ (p₀ ≫ i₀ + p₁ ≫ i₁) := by
        rw [hη, Category.comp_id]
      _ = a ≫ i₀ + b ≫ i₁ := by
        simp only [a, b, Preadditive.comp_add, Category.assoc]
  have hbez : a ≫ u₀ + b ≫ u₁ = 𝟙 P := by
    calc
      a ≫ u₀ + b ≫ u₁ = (a ≫ i₀ + b ≫ i₁) ≫ S.g ≫ e.hom := by
        simp only [u₀, u₁, Preadditive.add_comp, Category.assoc]
      _ = (e.inv ≫ h) ≫ S.g ≫ e.hom := by rw [hv]
      _ = 𝟙 P := by
        rw [Category.assoc, ← Category.assoc h, hh]
        simp
  have hff : S.f = d.hom ≫ ((-u₁) ≫ i₀ + u₀ ≫ i₁) := hf
  have hdiag : u₁ ≫ b + u₀ ≫ a = 𝟙 P := by
    rw [hcomm u₁ b, hcomm u₀ a, add_comm]
    exact hbez
  have hdiag₀ : b ≫ u₁ + u₀ ≫ a = 𝟙 P := by
    rw [hcomm u₀ a, add_comm]
    exact hbez
  have hdiag₁ : a ≫ u₀ + u₁ ≫ b = 𝟙 P := by
    rw [hcomm u₁ b]
    exact hbez
  have hcross₀ : (-b) ≫ u₀ + u₀ ≫ b = 0 := by
    rw [Preadditive.neg_comp, hcomm b u₀, neg_add_cancel]
  have hcross₁ : a ≫ (-u₁) + u₁ ≫ a = 0 := by
    rw [Preadditive.comp_neg, hcomm a u₁, neg_add_cancel]
  let r := (((-p₀) ≫ b) + p₁ ≫ a) ≫ d.inv
  have hi₀r : i₀ ≫ r = (-b) ≫ d.inv := by
    simp only [r, ← Category.assoc, Preadditive.comp_add, Preadditive.comp_neg,
      Preadditive.neg_comp, h₀₀, h₀₁, Category.id_comp, zero_comp, add_zero]
  have hi₁r : i₁ ≫ r = a ≫ d.inv := by
    simp only [r, ← Category.assoc, Preadditive.comp_add, Preadditive.comp_neg,
      Preadditive.neg_comp, h₁₀, h₁₁, Category.id_comp, zero_comp, zero_add, neg_zero]
  have hi₀g : i₀ ≫ S.g = u₀ ≫ e.inv := by
    simp only [u₀, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hi₁g : i₁ ≫ S.g = u₁ ≫ e.inv := by
    simp only [u₁, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine { r := r, s := h, f_r := ?_, s_g := hh, id := ?_ }
  · calc
      S.f ≫ r = d.hom ≫ ((-u₁) ≫ (i₀ ≫ r) + u₀ ≫ (i₁ ≫ r)) := by
        rw [hff]
        simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
      _ = d.hom ≫ (u₁ ≫ b + u₀ ≫ a) ≫ d.inv := by
        rw [hi₀r, hi₁r]
        simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_neg,
          Preadditive.neg_comp, neg_neg, Category.assoc]
      _ = 𝟙 S.X₁ := by rw [hdiag]; simp
  · apply pair_hom_ext i₀ i₁ p₀ p₁ hη
    · calc
        i₀ ≫ (r ≫ S.f + S.g ≫ h) = (i₀ ≫ r) ≫ S.f + (i₀ ≫ S.g) ≫ h := by
          simp only [Preadditive.comp_add, Category.assoc]
        _ = (-b) ≫ ((-u₁) ≫ i₀ + u₀ ≫ i₁) + u₀ ≫ (a ≫ i₀ + b ≫ i₁) := by
          rw [hi₀r, hi₀g, hff]
          simp only [Category.assoc, Iso.inv_hom_id_assoc]
          rw [hv]
        _ = (b ≫ u₁ + u₀ ≫ a) ≫ i₀ + ((-b) ≫ u₀ + u₀ ≫ b) ≫ i₁ := by
          simp only [Preadditive.comp_add, Preadditive.add_comp, Preadditive.neg_comp,
            Preadditive.comp_neg, Category.assoc]
          abel
        _ = i₀ ≫ 𝟙 S.X₂ := by rw [hdiag₀, hcross₀]; simp
    · calc
        i₁ ≫ (r ≫ S.f + S.g ≫ h) = (i₁ ≫ r) ≫ S.f + (i₁ ≫ S.g) ≫ h := by
          simp only [Preadditive.comp_add, Category.assoc]
        _ = a ≫ ((-u₁) ≫ i₀ + u₀ ≫ i₁) + u₁ ≫ (a ≫ i₀ + b ≫ i₁) := by
          rw [hi₁r, hi₁g, hff]
          simp only [Category.assoc, Iso.inv_hom_id_assoc]
          rw [hv]
        _ = (a ≫ (-u₁) + u₁ ≫ a) ≫ i₀ + (a ≫ u₀ + u₁ ≫ b) ≫ i₁ := by
          simp only [Preadditive.comp_add, Preadditive.add_comp, Preadditive.neg_comp,
            Preadditive.comp_neg, Category.assoc]
          abel
        _ = i₁ ≫ 𝟙 S.X₂ := by rw [hcross₁, hdiag₁]; simp

end PairFrames

private def localSplitting (L : LineBundle X)
    (s : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶ L.val))
    (U : X.Opens) (e : L.val.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (h : L.val.over U ⟶ (overRestriction U).obj (twoSectionSequence L s).X₂)
    (hh : h ≫ (Sigma.desc s).over U = 𝟙 _) :
    ((twoSectionSequence L s).map (overRestriction U)).Splitting := by
  let F := overRestriction U
  let d := dualLocalIso X L.val U e
  let i₀ := F.map (Sigma.ι (fun _ : ULift.{u} (Fin 2) =>
    SheafOfModules.unit X.ringCatSheaf) ⟨0⟩)
  let i₁ := F.map (Sigma.ι (fun _ : ULift.{u} (Fin 2) =>
    SheafOfModules.unit X.ringCatSheaf) ⟨1⟩)
  let p₀ := F.map (twoSectionProjection X ⟨0⟩)
  let p₁ := F.map (twoSectionProjection X ⟨1⟩)
  have hη : p₀ ≫ i₀ + p₁ ≫ i₁ = 𝟙 _ := by
    have hmap := congrArg F.map (pair_eta (X := X))
    rw [Functor.map_add, Functor.map_comp, Functor.map_comp] at hmap
    exact hmap.trans (F.map_id _)
  have h₀₀ : i₀ ≫ p₀ = 𝟙 _ := by
    simpa only [i₀, p₀, ↓reduceIte] using mapped_inclusion_projection F ⟨0⟩ ⟨0⟩
  have h₀₁ : i₀ ≫ p₁ = 0 := by
    have hne : (⟨0⟩ : ULift.{u} (Fin 2)) ≠ ⟨1⟩ := by decide
    simpa only [i₀, p₁, hne, ↓reduceIte] using mapped_inclusion_projection F ⟨0⟩ ⟨1⟩
  have h₁₀ : i₁ ≫ p₀ = 0 := by
    have hne : (⟨1⟩ : ULift.{u} (Fin 2)) ≠ ⟨0⟩ := by decide
    simpa only [i₁, p₀, hne, ↓reduceIte] using mapped_inclusion_projection F ⟨1⟩ ⟨0⟩
  have h₁₁ : i₁ ≫ p₁ = 𝟙 _ := by
    simpa only [i₁, p₁, ↓reduceIte] using mapped_inclusion_projection F ⟨1⟩ ⟨1⟩
  have hf : F.map (twoSectionKernelMap L s) = d.hom ≫
      ((-(i₁ ≫ F.map (Sigma.desc s) ≫ e.hom)) ≫ i₀ +
        (i₀ ≫ F.map (Sigma.desc s) ≫ e.hom) ≫ i₁) := by
    have hα₀ : F.map (dualSection X (s ⟨0⟩)) =
        d.hom ≫ F.map (s ⟨0⟩) ≫ e.hom := dualSection_over_frame L U e (s ⟨0⟩)
    have hα₁ : F.map (dualSection X (s ⟨1⟩)) =
        d.hom ≫ F.map (s ⟨1⟩) ≫ e.hom := dualSection_over_frame L U e (s ⟨1⟩)
    simp only [i₀, i₁, mapped_inclusion_row_assoc]
    dsimp only [twoSectionKernelMap]
    rw [Functor.map_add, Functor.map_comp, Functor.map_comp, Functor.map_neg, hα₁, hα₀]
    simp only [Preadditive.comp_add, Preadditive.comp_neg, Preadditive.neg_comp,
      Category.assoc]
  exact frameSplitting ((twoSectionSequence L s).map F) d e i₀ i₁ p₀ p₁ hη
    h₀₀ h₀₁ h₁₀ h₁₁ h hh hf (unitEnd_commute U)

private theorem exists_local_right_inverse_and_frame (L : LineBundle X)
    (s : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶ L.val))
    [Epi (Sigma.desc s)] (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧
      ∃ (_e : L.val.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
        (h : L.val.over U ⟶ (overRestriction U).obj (twoSectionSequence L s).X₂),
          h ≫ (Sigma.desc s).over U = 𝟙 _ := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := (isLocallyRankOne_iff_local_unit X L.val).mp L.property x
  let f : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit.{u + 1} ⟶ L.val.over U :=
    (coproductUniqueIso (fun _ : PUnit.{u + 1} =>
      SheafOfModules.unit (X.ringCatSheaf.over U))).hom ≫ e.inv
  let : IsIso f := by
    dsimp only [f]
    infer_instance
  let G := (SheafOfModules.free.generatingSections
    (R := X.ringCatSheaf.over U) PUnit.{u + 1}).ofEpi f
  let : G.IsFiniteType := { finite := inferInstanceAs (Finite PUnit.{u + 1}) }
  let : IsIso G.π := by
    dsimp only [G]
    rw [SheafOfModules.GeneratingSections.ofEpi_π,
      SheafOfModules.free.generatingSections_π]
    infer_instance
  obtain ⟨V, hVU, hxV, h, hh⟩ :=
    exists_local_section_of_finite_basis (Sigma.desc s) U G x hxU
  exact ⟨V, hxV, restrictOverUnitIso X L.val (homOfLE hVU) e, h, hh⟩

/-- An original generating pair of sections has the actual canonical short exact sequence.
No assumption is made on the scheme beyond its native structure sheaf. -/
theorem twoSectionSequence_shortExact (L : LineBundle X)
    (s : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶ L.val))
    [Epi (Sigma.desc s)] : (twoSectionSequence L s).ShortExact := by
  choose U hx e h hh using exists_local_right_inverse_and_frame L s
  apply shortExact_of_restrict_openCover (fun x : X => (U x).toScheme)
    (fun x => (U x).ι) (fun x => ⟨x, ⟨x, hx x⟩, rfl⟩) (twoSectionSequence L s)
  intro x
  have : (overEquiv (U x)).functor.Additive := by
    let := preservesBinaryBiproducts_of_preservesBinaryProducts (overEquiv (U x)).functor
    exact Functor.additive_of_preservesBinaryBiproducts _
  have : (SheafOfModules.overFunctor.{u} X.ringCatSheaf (U x)).Additive :=
    overRestriction_additive (U x)
  let sU : ((twoSectionSequence L s).map (restrictFunctor (U x).ι)).Splitting :=
    ((localSplitting L s (U x) (e x) (h x) (hh x)).map (overEquiv (U x)).functor).ofIso
      ((twoSectionSequence L s).mapNatIso (overFunctorEquiv (U x)))
  exact sU.shortExact

end AlgebraicGeometry.Scheme.Modules.Invertible
