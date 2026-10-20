/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Etale.MilnorPatching.FiniteFree
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Etale Milnor patching for finite split powers

The canonical component comparisons are constructed from the stable clutching
retraction. Conductor-based joint tensor conservativity proves formal
unramifiedness; finite projectivity supplies finite presentation over arbitrary
fibre bases. The universal `EtalePatching` proposition is not an input, and its
arbitrary-component scope is not asserted here.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace RingHom.Etale.MilnorPatching

universe u v w

private def reconstructionOfRetraction
    {K M F G H : Type*} [CommRing K]
    [AddCommGroup M] [Module K M] [AddCommGroup F] [Module K F]
    [AddCommGroup G] [Module K G] [AddCommGroup H] [Module K H]
    (i : M →ₗ[K] F) (r : F →ₗ[K] M) (hri : r.comp i = LinearMap.id)
    (E : F ≃ₗ[K] G) (γ : M →ₗ[K] H) (j : H →ₗ[K] G) (p : G →ₗ[K] H)
    (hi : E.toLinearMap.comp i = j.comp γ)
    (hr : γ.comp r = p.comp E.toLinearMap) (hpj : p.comp j = LinearMap.id) :
    M ≃ₗ[K] H := by
  refine LinearEquiv.ofLinearMap γ (r.comp (E.symm.toLinearMap.comp j)) ?_ ?_
  · apply LinearMap.ext
    intro x
    change γ (r (E.symm (j x))) = x
    calc
      _ = p (j x) := by
        simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, E.apply_symm_apply]
          using LinearMap.congr_fun hr (E.symm (j x))
      _ = x := LinearMap.congr_fun hpj x
  · apply LinearMap.ext
    intro x
    have h : E (i x) = j (γ x) := LinearMap.congr_fun hi x
    change r (E.symm (j (γ x))) = x
    rw [← h, E.symm_apply_apply]
    exact LinearMap.congr_fun hri x

namespace FiniteFree

section Modules

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  {ι : Type v} (f : R →+* T) (g : S →+* T)

local notation "P" => fiberRing f g

attribute [local instance] fstAlgebra sndAlgebra

variable (e : (ι → T) ≃ₗ[T] (ι → T))
local notation "Q" => clutch f g e
local notation "W" => clutch f g (LinearEquiv.refl T (ι → T))

private def fstLinear : Q →ₗ[P] (ι → R) :=
  (LinearMap.fst P (ι → R) (ι → S)).comp (clutch f g e).subtype

private def sndLinear : Q →ₗ[P] (ι → S) :=
  (LinearMap.snd P (ι → R) (ι → S)).comp (clutch f g e).subtype

private def fstBaseChange : R ⊗[P] Q →ₗ[R] (ι → R) :=
  (fstLinear f g e).liftBaseChange R

private def sndBaseChange : S ⊗[P] Q →ₗ[S] (ι → S) :=
  (sndLinear f g e).liftBaseChange S

variable [Fintype ι] [DecidableEq ι]

private def freeTensorEquiv (K : Type w) [CommRing K] [Algebra P K] :
    K ⊗[P] (W × W) ≃ₗ[K] (ι → K) × (ι → K) :=
  ((trivialEquiv f g).prodCongr (trivialEquiv f g)).baseChange P K _ _ ≪≫ₗ
    TensorProduct.prodRight P K K (ι → P) (ι → P) ≪≫ₗ
    (TensorProduct.piScalarRight P K K ι).prodCongr (TensorProduct.piScalarRight P K K ι)

private theorem freeTensorEquiv_fst_tmul (r : R) (x : W × W) :
    freeTensorEquiv f g R (r ⊗ₜ[P] x) = r • (x.1.val.1, x.2.val.1) := by
  ext i <;> simp [freeTensorEquiv, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, trivialEquiv, Algebra.smul_def, mul_comm] <;> rfl

private theorem freeTensorEquiv_snd_tmul (s : S) (x : W × W) :
    freeTensorEquiv f g S (s ⊗ₜ[P] x) = s • (x.1.val.2, x.2.val.2) := by
  ext i <;> simp [freeTensorEquiv, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, trivialEquiv, Algebra.smul_def, mul_comm] <;> rfl

variable (A B : (ι → R) →ₗ[R] (ι → R))
  (hA : ∀ x, f.compLeft ι (A x) = e (f.compLeft ι x))
  (hB : ∀ x, f.compLeft ι (B x) = e.symm (f.compLeft ι x))

private def fstEmbedding : (ι → R) →ₗ[R] (ι → R) × (ι → R) :=
  B.prod (A.comp B - LinearMap.id)

private def fstProjection : ((ι → R) × (ι → R)) →ₗ[R] (ι → R) :=
  let d := A.comp (LinearMap.fst R (ι → R) (ι → R)) - LinearMap.snd R (ι → R) (ι → R)
  d + A.comp (LinearMap.fst R (ι → R) (ι → R) - B.comp d)

omit [Fintype ι] [DecidableEq ι] in
private theorem fstProjection_embedding :
    (fstProjection A B).comp (fstEmbedding A B) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change A (B x) - (A (B x) - x) +
    A (B x - B (A (B x) - (A (B x) - x))) = x
  have h : A (B x) - (A (B x) - x) = x := by abel
  rw [h, sub_self, map_zero, add_zero]

private theorem fst_embed_baseChange :
    (freeTensorEquiv f g R).toLinearMap.comp ((embed f g e A B hA hB).baseChange R) =
      (fstEmbedding A B).comp (fstBaseChange f g e) := by
  apply LinearMap.restrictScalars_injective P
  apply TensorProduct.ext'
  intro r q
  change freeTensorEquiv f g R (r ⊗ₜ[P] embed f g e A B hA hB q) =
    fstEmbedding A B (r • q.val.1)
  rw [freeTensorEquiv_fst_tmul, map_smul]
  rfl

private theorem fst_retract_baseChange :
    (fstBaseChange f g e).comp ((retract f g e A B hA hB).baseChange R) =
      (fstProjection A B).comp (freeTensorEquiv f g R).toLinearMap := by
  apply LinearMap.restrictScalars_injective P
  apply TensorProduct.ext'
  intro r x
  change r • (retract f g e A B hA hB x).val.1 =
    fstProjection A B (freeTensorEquiv f g R (r ⊗ₜ[P] x))
  rw [freeTensorEquiv_fst_tmul, map_smul]
  rfl

private theorem snd_embed_baseChange :
    (freeTensorEquiv f g S).toLinearMap.comp ((embed f g e A B hA hB).baseChange S) =
      (LinearMap.inl S (ι → S) (ι → S)).comp (sndBaseChange f g e) := by
  apply LinearMap.restrictScalars_injective P
  apply TensorProduct.ext'
  intro s q
  change freeTensorEquiv f g S (s ⊗ₜ[P] embed f g e A B hA hB q) =
    LinearMap.inl S (ι → S) (ι → S) (s • q.val.2)
  rw [freeTensorEquiv_snd_tmul, map_smul]
  rfl

private theorem snd_retract_baseChange :
    (sndBaseChange f g e).comp ((retract f g e A B hA hB).baseChange S) =
      (LinearMap.fst S (ι → S) (ι → S)).comp (freeTensorEquiv f g S).toLinearMap := by
  apply LinearMap.restrictScalars_injective P
  apply TensorProduct.ext'
  intro s x
  change s • (retract f g e A B hA hB x).val.2 =
    LinearMap.fst S (ι → S) (ι → S) (freeTensorEquiv f g S (s ⊗ₜ[P] x))
  rw [freeTensorEquiv_snd_tmul, map_smul]
  rfl

private def fstTensorLinearEquiv : R ⊗[P] Q ≃ₗ[R] (ι → R) :=
  reconstructionOfRetraction ((embed f g e A B hA hB).baseChange R)
    ((retract f g e A B hA hB).baseChange R)
    (by simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_id] using
      congrArg (LinearMap.baseChange R) (retract_comp_embed f g e A B hA hB))
    (freeTensorEquiv f g R) (fstBaseChange f g e) (fstEmbedding A B) (fstProjection A B)
    (fst_embed_baseChange f g e A B hA hB) (fst_retract_baseChange f g e A B hA hB)
    (fstProjection_embedding A B)

private def sndTensorLinearEquiv : S ⊗[P] Q ≃ₗ[S] (ι → S) :=
  reconstructionOfRetraction ((embed f g e A B hA hB).baseChange S)
    ((retract f g e A B hA hB).baseChange S)
    (by simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_id] using
      congrArg (LinearMap.baseChange S) (retract_comp_embed f g e A B hA hB))
    (freeTensorEquiv f g S) (sndBaseChange f g e)
    (LinearMap.inl S (ι → S) (ι → S)) (LinearMap.fst S (ι → S) (ι → S))
    (snd_embed_baseChange f g e A B hA hB) (snd_retract_baseChange f g e A B hA hB)
    (by ext x; rfl)

include A B hA hB in
omit [Fintype ι] [DecidableEq ι] in
private theorem fst_bijective [_root_.Finite ι] : Function.Bijective (fstBaseChange f g e) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  exact (fstTensorLinearEquiv f g e A B hA hB).bijective

include A B hA hB in
omit [Fintype ι] [DecidableEq ι] in
private theorem snd_bijective [_root_.Finite ι] : Function.Bijective (sndBaseChange f g e) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  exact (sndTensorLinearEquiv f g e A B hA hB).bijective

end Modules

section ModuleReconstructions

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  {ι : Type v} (f : R →+* T) (g : S →+* T)
  (e : (ι → T) ≃ₗ[T] (ι → T)) [_root_.Finite ι]

local notation "P" => fiberRing f g
attribute [local instance] fstAlgebra sndAlgebra

/-- The canonical normalization tensor map on the clutched module is bijective. -/
theorem fstTensorModule_bijective (hf : Function.Surjective f) :
    Function.Bijective
      (((LinearMap.fst P (ι → R) (ι → S)).comp (clutch f g e).subtype).liftBaseChange R) := by
  obtain ⟨A, hA⟩ := exists_coefficient_lift f hf e.toLinearMap
  obtain ⟨B, hB⟩ := exists_coefficient_lift f hf e.symm.toLinearMap
  exact fst_bijective f g e A B hA hB

/-- Canonical normalization-side reconstruction of the finite-free clutched
module, with the coefficient lifts constructed from the original surjection. -/
def fstTensorModuleEquiv (hf : Function.Surjective f) :
    R ⊗[P] clutch f g e ≃ₗ[R] (ι → R) :=
  LinearEquiv.ofBijective
    (((LinearMap.fst P (ι → R) (ι → S)).comp (clutch f g e).subtype).liftBaseChange R)
    (fstTensorModule_bijective f g e hf)

@[simp]
theorem fstTensorModuleEquiv_tmul (hf : Function.Surjective f) (r : R)
    (q : clutch f g e) :
    fstTensorModuleEquiv f g e hf (r ⊗ₜ[P] q) = r • q.val.1 := rfl

/-- The canonical node tensor map on the clutched module is bijective. -/
theorem sndTensorModule_bijective (hf : Function.Surjective f) :
    Function.Bijective
      (((LinearMap.snd P (ι → R) (ι → S)).comp (clutch f g e).subtype).liftBaseChange S) := by
  obtain ⟨A, hA⟩ := exists_coefficient_lift f hf e.toLinearMap
  obtain ⟨B, hB⟩ := exists_coefficient_lift f hf e.symm.toLinearMap
  exact snd_bijective f g e A B hA hB

/-- Canonical node-side reconstruction of the finite-free clutched module. -/
def sndTensorModuleEquiv (hf : Function.Surjective f) :
    S ⊗[P] clutch f g e ≃ₗ[S] (ι → S) :=
  LinearEquiv.ofBijective
    (((LinearMap.snd P (ι → R) (ι → S)).comp (clutch f g e).subtype).liftBaseChange S)
    (sndTensorModule_bijective f g e hf)

@[simp]
theorem sndTensorModuleEquiv_tmul (hf : Function.Surjective f) (s : S)
    (q : clutch f g e) :
    sndTensorModuleEquiv f g e hf (s ⊗ₜ[P] q) = s • q.val.2 := rfl

end ModuleReconstructions

section RingReconstructions

variable {R S T : Type (max u v)} [CommRing R] [CommRing S] [CommRing T]
  {ι : Type v} (f : R →+* T) (g : S →+* T)
  (e : (ι → T) ≃ₐ[T] (ι → T))

local notation "P" => fiberRing f g
local notation "Q" => fiberRing (f.compLeft ι)
  (RingHom.comp (e : (ι → T) →+* (ι → T)) (g.compLeft ι))

attribute [local instance] fstAlgebra sndAlgebra
/-- The glued algebra structure induced by the canonical map from the base fibre ring. -/
local instance algebraOfMap : Algebra P Q := (map f g e).toAlgebra

/-- The actual normalization projection, with its fibre-base algebra map. -/
def fstAlgHom : Q →ₐ[P] (ι → R) where
  __ := RingHom.pullbackFst (f.compLeft ι) (RingHom.comp (e : (ι → T) →+* (ι → T)) (g.compLeft ι))
  commutes' _ := rfl

/-- The actual node projection, with its fibre-base algebra map. -/
def sndAlgHom : Q →ₐ[P] (ι → S) where
  __ := RingHom.pullbackSnd (f.compLeft ι) (RingHom.comp (e : (ι → T) →+* (ι → T)) (g.compLeft ι))
  commutes' _ := rfl

/-- The canonical normalization tensor map is multiplication after the actual
normalization projection. -/
def fstTensorHom : R ⊗[P] Q →ₐ[R] (ι → R) :=
  AlgHom.liftEquiv P R Q (ι → R) (fstAlgHom f g e)

/-- The canonical node tensor map uses the actual node projection. -/
def sndTensorHom : S ⊗[P] Q →ₐ[S] (ι → S) :=
  AlgHom.liftEquiv P S Q (ι → S) (sndAlgHom f g e)

@[simp]
theorem fstTensorHom_tmul (r : R) (q : Q) :
    fstTensorHom f g e (r ⊗ₜ[P] q) = r • q.val.1 := rfl

@[simp]
theorem sndTensorHom_tmul (s : S) (q : Q) :
    sndTensorHom f g e (s ⊗ₜ[P] q) = s • q.val.2 := rfl

/-- The canonical normalization tensor algebra map is bijective. -/
theorem fstTensorHom_bijective [_root_.Finite ι] (hf : Function.Surjective f) :
    Function.Bijective (fstTensorHom f g e) := by
  let : Algebra P (fiberRing (f.compLeft ι) (e.toRingHom.comp (g.compLeft ι))) :=
    (map f g e).toAlgebra
  let E : R ⊗[P] Q ≃ₗ[R] (ι → R) :=
    (mapClutchEquiv f g e).baseChange P R _ _ ≪≫ₗ
    fstTensorModuleEquiv f g e.toLinearEquiv hf
  have h : (fstTensorHom f g e).toLinearMap = E.toLinearMap := by
    apply LinearMap.restrictScalars_injective P
    apply TensorProduct.ext'
    intro r q
    change fstTensorHom f g e (r ⊗ₜ[P] q) =
      fstTensorModuleEquiv f g e.toLinearEquiv hf (r ⊗ₜ[P] mapClutchEquiv f g e q)
    rw [fstTensorHom_tmul, fstTensorModuleEquiv_tmul]
    rfl
  change Function.Bijective (fstTensorHom f g e).toLinearMap
  rw [h]
  exact E.bijective

/-- The canonical node tensor algebra map is bijective. -/
theorem sndTensorHom_bijective [_root_.Finite ι] (hf : Function.Surjective f) :
    Function.Bijective (sndTensorHom f g e) := by
  let : Algebra P (fiberRing (f.compLeft ι) (e.toRingHom.comp (g.compLeft ι))) :=
    (map f g e).toAlgebra
  let E : S ⊗[P] Q ≃ₗ[S] (ι → S) :=
    (mapClutchEquiv f g e).baseChange P S _ _ ≪≫ₗ
    sndTensorModuleEquiv f g e.toLinearEquiv hf
  have h : (sndTensorHom f g e).toLinearMap = E.toLinearMap := by
    apply LinearMap.restrictScalars_injective P
    apply TensorProduct.ext'
    intro s q
    change sndTensorHom f g e (s ⊗ₜ[P] q) =
      sndTensorModuleEquiv f g e.toLinearEquiv hf (s ⊗ₜ[P] mapClutchEquiv f g e q)
    rw [sndTensorHom_tmul, sndTensorModuleEquiv_tmul]
    rfl
  change Function.Bijective (sndTensorHom f g e).toLinearMap
  rw [h]
  exact E.bijective

/-- The actual normalization tensor map is an algebra isomorphism. Its inverse
comes from the stable clutching retraction, not a reconstruction hypothesis. -/
def fstTensorEquiv [_root_.Finite ι] (hf : Function.Surjective f) :
    R ⊗[P] Q ≃ₐ[R] (ι → R) :=
  AlgEquiv.ofBijective (fstTensorHom f g e) (fstTensorHom_bijective f g e hf)

/-- The actual node tensor map is an algebra isomorphism. -/
def sndTensorEquiv [_root_.Finite ι] (hf : Function.Surjective f) :
    S ⊗[P] Q ≃ₐ[S] (ι → S) :=
  AlgEquiv.ofBijective (sndTensorHom f g e) (sndTensorHom_bijective f g e hf)

@[simp]
theorem fstTensorEquiv_tmul [_root_.Finite ι] (hf : Function.Surjective f) (r : R) (q : Q) :
    fstTensorEquiv f g e hf (r ⊗ₜ[P] q) = r • q.val.1 := rfl

@[simp]
theorem sndTensorEquiv_tmul [_root_.Finite ι] (hf : Function.Surjective f) (s : S) (q : Q) :
    sndTensorEquiv f g e hf (s ⊗ₜ[P] q) = s • q.val.2 := rfl

/-- The normalization inverse recovers the actual pure tensor on every
scalar multiple of a projected glued element. -/
@[simp]
theorem fstTensorEquiv_symm_smul [_root_.Finite ι] (hf : Function.Surjective f) (r : R) (q : Q) :
    (fstTensorEquiv f g e hf).symm (r • q.val.1) = r ⊗ₜ[P] q := by
  change (fstTensorEquiv f g e hf).symm (fstTensorEquiv f g e hf (r ⊗ₜ[P] q)) = _
  exact (fstTensorEquiv f g e hf).symm_apply_apply _

/-- The node inverse recovers the actual pure tensor from the node projection. -/
@[simp]
theorem sndTensorEquiv_symm_smul [_root_.Finite ι] (hf : Function.Surjective f) (s : S) (q : Q) :
    (sndTensorEquiv f g e hf).symm (s • q.val.2) = s ⊗ₜ[P] q := by
  change (sndTensorEquiv f g e hf).symm (sndTensorEquiv f g e hf (s ⊗ₜ[P] q)) = _
  exact (sndTensorEquiv f g e hf).symm_apply_apply _

end RingReconstructions

end FiniteFree

section TensorConservativity

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  (f : R →+* T) (g : S →+* T)

local notation "P" => fiberRing f g
attribute [local instance] FiniteFree.fstAlgebra FiniteFree.sndAlgebra

/-- The two actual component tensor functors jointly detect a zero module.
The normalization map is not required to be flat or faithfully flat. -/
theorem subsingleton_of_tensor_components (hf : Function.Surjective f)
    (M : Type v) [AddCommGroup M] [Module P M]
    [Subsingleton (R ⊗[P] M)] [Subsingleton (S ⊗[P] M)] : Subsingleton M := by
  let π : P →ₗ[P] S := Algebra.linearMap P S
  let J := LinearMap.ker π
  let I := (RingHom.ker f).restrictScalars P
  let E : J ≃ₗ[P] I :=
    { toFun := fun j => ⟨j.val.val.1, by
        change f j.val.val.1 = 0
        have hj : j.val.val.2 = 0 := j.property
        have hfg : f j.val.val.1 = g j.val.val.2 := j.val.property
        rw [hj, map_zero] at hfg
        exact hfg⟩
      invFun := fun i => ⟨⟨(i.val, 0), by
        change f i.val = g 0
        have hi : f i.val = 0 := i.property
        simpa only [map_zero] using hi⟩, rfl⟩
      left_inv := fun j => by
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact (show j.val.val.2 = 0 from j.property).symm
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have : Subsingleton (I ⊗[P] M) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange P R R I M).symm.subsingleton
  have : Subsingleton (J ⊗[P] M) := (E.rTensor M).subsingleton
  have hπ : Function.Surjective π :=
    RingHom.surjective_pullbackSnd_of_surjective f g hf
  have hex := _root_.rTensor_exact M (LinearMap.exact_subtype_ker_map π) hπ
  have : Subsingleton (P ⊗[P] M) := by
    apply Subsingleton.intro
    intro x y
    obtain ⟨a, ha⟩ := (hex x).mp (Subsingleton.elim _ _)
    obtain ⟨b, hb⟩ := (hex y).mp (Subsingleton.elim _ _)
    rw [← ha, ← hb]
    exact congrArg _ (Subsingleton.elim a b)
  exact (TensorProduct.lid P M).symm.subsingleton

end TensorConservativity

namespace FiniteFree

section ProjectiveModules

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  {ι : Type v} (f : R →+* T) (g : S →+* T)
  (e : (ι → T) ≃ₗ[T] (ι → T)) [_root_.Finite ι]

local notation "P" => fiberRing f g
local notation "W" => clutch f g (LinearEquiv.refl T (ι → T))
attribute [local instance] fstAlgebra sndAlgebra

/-- The constructed stable retraction makes finite-free clutching projective. -/
theorem projective_of_surjective (hf : Function.Surjective f) :
    Module.Projective P (clutch f g e) := by
  obtain ⟨A, hA⟩ := exists_coefficient_lift f hf e.toLinearMap
  obtain ⟨B, hB⟩ := exists_coefficient_lift f hf e.symm.toLinearMap
  let : Module.Projective P (W × W) := Module.Projective.of_equiv'
    ((trivialEquiv f g).prodCongr (trivialEquiv f g)).symm
  exact Module.Projective.of_split (embed f g e A B hA hB) (retract f g e A B hA hB)
    (retract_comp_embed f g e A B hA hB)

end ProjectiveModules

section Etale

variable {R S T : Type (max u v)} [CommRing R] [CommRing S] [CommRing T]
  {ι : Type v} (f : R →+* T) (g : S →+* T)
  (e : (ι → T) ≃ₐ[T] (ι → T)) [_root_.Finite ι]

local notation "P" => fiberRing f g
local notation "Q" => fiberRing (f.compLeft ι)
  (RingHom.comp (e : (ι → T) →+* (ι → T)) (g.compLeft ι))
attribute [local instance] fstAlgebra sndAlgebra algebraOfMap

/-- Finite projectivity of the actual algebra module supplies finite
presentation over an arbitrary fibre base, using the native module-to-algebra theorem. -/
theorem finitePresentation_map_of_surjective (hf : Function.Surjective f) :
    (map f g e).FinitePresentation := by
  let : Module.Finite P Q := (finite_flat_map f g hf e).1
  let : Module.Projective P (clutch f g e.toLinearEquiv) :=
    projective_of_surjective f g e.toLinearEquiv hf
  let : Module.Projective P Q := Module.Projective.of_equiv' (mapClutchEquiv f g e).symm
  let : Module.FinitePresentation P Q := Module.finitePresentation_of_projective P Q
  exact Algebra.FinitePresentation.of_finitePresentation P Q

/-- Formal unramifiedness is proved from the two canonical split component
reconstructions and conductor-based joint tensor conservativity. -/
theorem formallyUnramified_map (hf : Function.Surjective f) :
    (map f g e).FormallyUnramified := by
  change Algebra.FormallyUnramified P Q
  constructor
  have hR : Subsingleton (R ⊗[P] Ω[Q⁄P]) := by
    let : Algebra.FormallyUnramified R (R ⊗[P] Q) :=
      Algebra.FormallyUnramified.of_equiv (fstTensorEquiv f g e hf).symm
    let : Algebra Q (R ⊗[P] Q) := Algebra.TensorProduct.rightAlgebra
    exact (KaehlerDifferential.tensorKaehlerEquivBase P R Q (R ⊗[P] Q)).subsingleton
  have hS : Subsingleton (S ⊗[P] Ω[Q⁄P]) := by
    let : Algebra.FormallyUnramified S (S ⊗[P] Q) :=
      Algebra.FormallyUnramified.of_equiv (sndTensorEquiv f g e hf).symm
    let : Algebra Q (S ⊗[P] Q) := Algebra.TensorProduct.rightAlgebra
    exact (KaehlerDifferential.tensorKaehlerEquivBase P S Q (S ⊗[P] Q)).subsingleton
  let := hR
  let := hS
  exact subsingleton_of_tensor_components f g hf Ω[Q⁄P]

/-- Genuine etale patching for the actual finite split-power conductor square,
including endpoint-dependent boundary automorphisms. -/
theorem etale_map (hf : Function.Surjective f) : (map f g e).Etale := by
  exact RingHom.Etale.iff_flat_and_formallyUnramified.mpr
    ⟨(finite_flat_map f g hf e).2, formallyUnramified_map f g e hf,
      finitePresentation_map_of_surjective f g e hf⟩

end Etale

end FiniteFree

end RingHom.Etale.MilnorPatching
