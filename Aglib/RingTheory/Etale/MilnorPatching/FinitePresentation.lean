/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, kangxyz
-/

module

public import Aglib.RingTheory.Etale.MilnorPatching.Flat
public import Mathlib.RingTheory.Finiteness.Descent

/-!
# Finite-presentation descent in a Milnor square

Finite generators are selected from the original tensor expressions.
The selection arguments adapt the finite-descent constructions in
`Mathlib.RingTheory.Finiteness.Descent`, retaining their attribution.
Joint tensor conservativity replaces a faithful-flatness assumption.
Additional copyright: Copyright (c) 2026 kangxyz. All rights reserved.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace RingHom.Etale.MilnorPatching

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private def tensorBaseChangeCancel
    (P A R M : Type*) [CommRing P] [CommRing A] [CommRing R]
    [Algebra P A] [Algebra P R] [AddCommGroup M]
    [Module P M] [Module A M] [IsScalarTower P A M] :
    (R ⊗[P] A) ⊗[A] M ≃ₗ[P] R ⊗[P] M :=
  (((Algebra.TensorProduct.commRight P A R).symm.toLinearEquiv.rTensor M).restrictScalars P) ≪≫ₗ
    (TensorProduct.comm A (A ⊗[P] R) M).restrictScalars P ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange P A A M R).restrictScalars P ≪≫ₗ
    TensorProduct.comm P M R

private theorem tensorBaseChangeCancel_tmul
    (P A R M : Type*) [CommRing P] [CommRing A] [CommRing R]
    [Algebra P A] [Algebra P R] [AddCommGroup M]
    [Module P M] [Module A M] [IsScalarTower P A M] (r : R) (a : A) (m : M) :
    tensorBaseChangeCancel P A R M ((r ⊗ₜ[P] a) ⊗ₜ[A] m) = r ⊗ₜ[P] (a • m) := rfl

private theorem lTensor_surjective_of_baseChange_surjective
    {P A R M N : Type*} [CommRing P] [CommRing A] [CommRing R]
    [Algebra P A] [Algebra P R] [AddCommGroup M] [AddCommGroup N]
    [Module P M] [Module A M] [IsScalarTower P A M]
    [Module P N] [Module A N] [IsScalarTower P A N]
    (h : M →ₗ[A] N) (hh : Function.Surjective (h.lTensor (R ⊗[P] A))) :
    Function.Surjective ((h.restrictScalars P).lTensor R) := by
  let eM := tensorBaseChangeCancel P A R M
  let eN := tensorBaseChangeCancel P A R N
  have hnat (x : (R ⊗[P] A) ⊗[A] M) :
      eN (h.lTensor (R ⊗[P] A) x) = (h.restrictScalars P).lTensor R (eM x) := by
    induction x using TensorProduct.inductionOn with
    | tmul z m =>
      induction z using TensorProduct.inductionOn with
      | tmul r a => simp [eM, eN, tensorBaseChangeCancel_tmul]
      | add x y ihx ihy => simp only [TensorProduct.add_tmul, map_add, ihx, ihy]
    | add x y ihx ihy => simp only [map_add, ihx, ihy]
  intro y
  obtain ⟨x, hx⟩ := hh (eN.symm y)
  exact ⟨eM x, (hnat x).symm.trans ((congrArg eN hx).trans (eN.apply_symm_apply y))⟩

private theorem exists_fg_submodule_baseChange_eq_top
    (A B M : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.Finite B (B ⊗[A] M)] :
    ∃ L : Submodule A M, L.FG ∧ L.baseChange B = ⊤ := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := B) (M := B ⊗[A] M)
  choose k t m h using fun i : Fin n => TensorProduct.exists_sum_tmul_eq (s i)
  let f : ((Σ i, Fin (k i)) → A) →ₗ[A] M :=
    (Pi.basisFun A _).constr A fun ⟨i, j⟩ => m i j
  have hsurj : Function.Surjective (f.baseChange B) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le,
      Set.range_subset_iff]
    intro i
    use ∑ j : Fin (k i), t i j ⊗ₜ[A] Pi.basisFun A _ ⟨i, j⟩
    simp [f, -Pi.basisFun_equivFun, -Pi.basisFun_apply, h i]
  refine ⟨LinearMap.range f, Submodule.fg_range f, ?_⟩
  apply LinearMap.range_eq_top.mpr
  intro x
  obtain ⟨y, rfl⟩ := hsurj x
  refine ⟨f.rangeRestrict.baseChange B y, ?_⟩
  have hcomp : (LinearMap.range f).subtype.comp f.rangeRestrict = f := rfl
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp]

universe u v

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  (f : R →+* T) (g : S →+* T)

local notation "P" => fiberRing f g
attribute [local instance] FiniteFree.fstAlgebra FiniteFree.sndAlgebra

/-- The two actual component tensor maps jointly detect surjectivity. -/
theorem surjective_of_tensor_components
    {M N : Type v} [AddCommGroup M] [AddCommGroup N]
    [Module P M] [Module P N] (hf : Function.Surjective f) (h : M →ₗ[P] N)
    (hR : Function.Surjective (h.lTensor R))
    (hS : Function.Surjective (h.lTensor S)) : Function.Surjective h := by
  let K := LinearMap.range h
  have hzero (W : Type u) [AddCommGroup W] [Module P W]
      (hW : Function.Surjective (h.lTensor W)) : Subsingleton (W ⊗[P] (N ⧸ K)) := by
    have hx (x : W ⊗[P] (N ⧸ K)) : x = 0 := by
      obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective W K.mkQ_surjective x
      obtain ⟨z, rfl⟩ := hW y
      exact (_root_.lTensor_exact W (LinearMap.exact_map_mkQ_range h)
        K.mkQ_surjective).apply_apply_eq_zero z
    exact ⟨fun x y => (hx x).trans (hx y).symm⟩
  let : Subsingleton (R ⊗[P] (N ⧸ K)) := hzero R hR
  let : Subsingleton (S ⊗[P] (N ⧸ K)) := hzero S hS
  have hq : Subsingleton (N ⧸ K) := subsingleton_of_tensor_components f g hf (N ⧸ K)
  exact LinearMap.range_eq_top.mp (Submodule.Quotient.subsingleton_iff.mp hq)

/-- Surjectivity is still detected after adjoining an arbitrary algebra to
the original Milnor base; all comparison maps are canonical tensor maps. -/
theorem surjective_of_tensor_components_over
    (A : Type u) [CommRing A] [Algebra P A]
    {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (hf : Function.Surjective f) (h : M →ₗ[A] N)
    (hR : Function.Surjective (h.lTensor (R ⊗[P] A)))
    (hS : Function.Surjective (h.lTensor (S ⊗[P] A))) : Function.Surjective h := by
  let : Module P M := Module.compHom M (algebraMap P A)
  let : Module P N := Module.compHom N (algebraMap P A)
  let : IsScalarTower P A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower P A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact surjective_of_tensor_components f g hf (h.restrictScalars P)
    (lTensor_surjective_of_baseChange_surjective h hR)
    (lTensor_surjective_of_baseChange_surjective h hS)

/-- Finite generation descends from the two components after an arbitrary
algebra extension of the Milnor base. No flatness of that extension or of
the module is assumed. -/
theorem finite_of_component_baseChanges_over
    (A : Type u) [CommRing A] [Algebra P A]
    (M : Type v) [AddCommGroup M] [Module A M]
    [Module.Finite (R ⊗[P] A) ((R ⊗[P] A) ⊗[A] M)]
    [Module.Finite (S ⊗[P] A) ((S ⊗[P] A) ⊗[A] M)]
    (hf : Function.Surjective f) : Module.Finite A M := by
  obtain ⟨LR, hLR, hR⟩ := exists_fg_submodule_baseChange_eq_top A (R ⊗[P] A) M
  obtain ⟨LS, hLS, hS⟩ := exists_fg_submodule_baseChange_eq_top A (S ⊗[P] A) M
  let L := LR ⊔ LS
  let : Module.Finite A L := Module.Finite.of_fg (hLR.sup hLS)
  have hR' : L.baseChange (R ⊗[P] A) = ⊤ := by
    apply top_unique
    rw [← hR]
    exact Submodule.baseChange_mono _ le_sup_left
  have hS' : L.baseChange (S ⊗[P] A) = ⊤ := by
    apply top_unique
    rw [← hS]
    exact Submodule.baseChange_mono _ le_sup_right
  have hsurj : Function.Surjective L.subtype :=
    surjective_of_tensor_components_over f g A hf L.subtype
      (by
        have h : Function.Surjective (L.subtype.baseChange (R ⊗[P] A)) :=
          LinearMap.range_eq_top.mp hR'
        simpa only [LinearMap.baseChange_eq_ltensor] using h)
      (by
        have h : Function.Surjective (L.subtype.baseChange (S ⊗[P] A)) :=
          LinearMap.range_eq_top.mp hS'
        simpa only [LinearMap.baseChange_eq_ltensor] using h)
  exact Module.Finite.of_surjective L.subtype hsurj

private theorem subalgebra_baseChange_mono
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (L K : Subalgebra A C) (hLK : L ≤ K) :
    L.baseChange B ≤ K.baseChange B := by
  rintro x ⟨y, rfl⟩
  induction y using TensorProduct.inductionOn with
  | tmul b l => exact Subalgebra.tmul_mem_baseChange (hLK l.property) b
  | add x y ihx ihy => simpa only [map_add] using (K.baseChange B).add_mem ihx ihy

private theorem exists_fg_subalgebra_baseChange_eq_top
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra.FiniteType B (B ⊗[A] C)] :
    ∃ L : Subalgebra A C, L.FG ∧ L.baseChange B = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := B) (A := B ⊗[A] C)
  choose k t m h using fun x : s => TensorProduct.exists_sum_tmul_eq x.val
  let p : MvPolynomial (Σ x : s, Fin (k x)) A →ₐ[A] C :=
    MvPolynomial.aeval fun ⟨x, i⟩ => m x i
  have hp : Function.Surjective (Algebra.TensorProduct.map (.id B B) p) := by
    rw [← AlgHom.range_eq_top, _root_.eq_top_iff, ← hs, Algebra.adjoin_le_iff]
    intro x hx
    let i : s := ⟨x, hx⟩
    use ∑ j : Fin (k i), t i j ⊗ₜ[A] MvPolynomial.X ⟨i, j⟩
    simp [p, ← h, i]
  have hfg : p.range.FG := by
    simpa using (Algebra.FiniteType.out
      (R := A) (A := MvPolynomial (Σ x : s, Fin (k x)) A)).map p
  refine ⟨p.range, hfg, ?_⟩
  change (Algebra.TensorProduct.map (.id B B) p.range.val).range = ⊤
  rw [AlgHom.range_eq_top]
  intro x
  obtain ⟨y, rfl⟩ := hp x
  refine ⟨Algebra.TensorProduct.map (.id B B) p.rangeRestrict y, ?_⟩
  have hcomp : (Algebra.TensorProduct.map (.id B B) p.range.val).comp
      (Algebra.TensorProduct.map (.id B B) p.rangeRestrict) =
      Algebra.TensorProduct.map (.id B B) p := by
    apply Algebra.TensorProduct.ext'
    intro b q
    rfl
  exact DFunLike.congr_fun hcomp y

/-- Algebra finite type descends from the two actual component tensors of
an arbitrary algebra over the Milnor base. -/
theorem finiteType_of_component_baseChanges
    (Q : Type u) [CommRing Q] [Algebra P Q]
    [Algebra.FiniteType R (R ⊗[P] Q)] [Algebra.FiniteType S (S ⊗[P] Q)]
    (hf : Function.Surjective f) : Algebra.FiniteType P Q := by
  obtain ⟨LR, hLR, hR⟩ := exists_fg_subalgebra_baseChange_eq_top P R Q
  obtain ⟨LS, hLS, hS⟩ := exists_fg_subalgebra_baseChange_eq_top P S Q
  let L := LR ⊔ LS
  let : Algebra.FiniteType P L := (Subalgebra.fg_iff_finiteType L).mp (hLR.sup hLS)
  have hR' : L.baseChange R = ⊤ := by
    apply top_unique
    rw [← hR]
    exact subalgebra_baseChange_mono P R Q LR L le_sup_left
  have hS' : L.baseChange S = ⊤ := by
    apply top_unique
    rw [← hS]
    exact subalgebra_baseChange_mono P S Q LS L le_sup_right
  have hmapR : Function.Surjective (L.val.toLinearMap.lTensor R) := by
    change Function.Surjective (Algebra.TensorProduct.map (.id R R) L.val)
    exact (AlgHom.range_eq_top _).mp hR'
  have hmapS : Function.Surjective (L.val.toLinearMap.lTensor S) := by
    change Function.Surjective (Algebra.TensorProduct.map (.id S S) L.val)
    exact (AlgHom.range_eq_top _).mp hS'
  exact Algebra.FiniteType.of_surjective L.val
    (surjective_of_tensor_components f g hf L.val.toLinearMap hmapR hmapS)

/-- A flat algebra over the literal Milnor base is finitely presented if
both actual component tensor algebras are finitely presented. The relation
ideal is obtained from an actual finite polynomial presentation. -/
theorem finitePresentation_of_flat_of_component_baseChanges
    (Q : Type u) [CommRing Q] [Algebra P Q] [Module.Flat P Q]
    [Algebra.FinitePresentation R (R ⊗[P] Q)]
    [Algebra.FinitePresentation S (S ⊗[P] Q)]
    (hf : Function.Surjective f) : Algebra.FinitePresentation P Q := by
  have hft : Algebra.FiniteType P Q := finiteType_of_component_baseChanges f g Q hf
  rw [Algebra.FiniteType.iff_quotient_mvPolynomial''] at hft
  obtain ⟨n, p, hp⟩ := hft
  let A := MvPolynomial (Fin n) P
  let : Algebra A Q := p.toRingHom.toAlgebra
  let : IsScalarTower P A Q := IsScalarTower.of_algebraMap_eq' p.comp_algebraMap.symm
  let K := RingHom.ker (algebraMap A Q)
  have hKfinite (W : Type u) [CommRing W] [Algebra P W]
      [Algebra.FinitePresentation W (W ⊗[P] Q)] :
      Module.Finite (W ⊗[P] A) ((W ⊗[P] A) ⊗[A] K) := by
    let φ : W ⊗[P] A →ₐ[W] W ⊗[P] Q :=
      Algebra.TensorProduct.map (.id W W) (IsScalarTower.toAlgHom P A Q)
    have hφ : Function.Surjective φ :=
      Algebra.TensorProduct.map_surjective (.id W W) (IsScalarTower.toAlgHom P A Q)
        Function.surjective_id hp
    have hfg := Algebra.FinitePresentation.ker_fG_of_surjective φ hφ
    let : Module.Finite (W ⊗[P] A) (RingHom.ker φ) := Module.Finite.of_fg hfg
    exact Module.Finite.equiv (Algebra.kerTensorProductMapIdToAlgHomEquiv P A Q W hp)
  let : Module.Finite (R ⊗[P] A) ((R ⊗[P] A) ⊗[A] K) := hKfinite R
  let : Module.Finite (S ⊗[P] A) ((S ⊗[P] A) ⊗[A] K) := hKfinite S
  have hK : Module.Finite A K := finite_of_component_baseChanges_over f g A K hf
  exact Algebra.FinitePresentation.of_surjective hp (Module.Finite.iff_fg.mp hK)

end RingHom.Etale.MilnorPatching

namespace RingHom.Etale.MilnorPatching

universe u

attribute [local instance] FiniteFree.fstAlgebra FiniteFree.sndAlgebra

section

variable {R S T C D U : Type u}
  [CommRing R] [CommRing S] [CommRing T]
  [CommRing C] [CommRing D] [CommRing U]

/-- Etale patching for the original seven-map Milnor square, with the
specified compatible tensor equivalences and only the original surjective
boundary and etale-component hypotheses. -/
theorem etale_fiberMap
    (f : R →+* T) (g : S →+* T) (r : R →+* C) (s : S →+* D)
    (t : T →+* U) (b : C →+* U) (v : D →+* U)
    (hc : b.comp r = t.comp f) (hd : v.comp s = t.comp g) :
    letI : Algebra R T := f.toAlgebra
    letI : Algebra S T := g.toAlgebra
    letI : Algebra R C := r.toAlgebra
    letI : Algebra S D := s.toAlgebra
    letI : Algebra T U := t.toAlgebra
    ∀ (eC : T ⊗[R] C ≃ₐ[T] U) (eD : T ⊗[S] D ≃ₐ[T] U),
      (∀ c, eC (1 ⊗ₜ[R] c) = b c) →
      (∀ d, eD (1 ⊗ₜ[S] d) = v d) →
      Function.Surjective f → r.Etale → s.Etale →
      (fiberMap f g r s t b v hc hd).Etale := by
  let : Algebra R T := f.toAlgebra
  let : Algebra S T := g.toAlgebra
  let : Algebra R C := r.toAlgebra
  let : Algebra S D := s.toAlgebra
  let : Algebra T U := t.toAlgebra
  intro eC eD heC heD hf hr hs
  let P := fiberRing f g
  let Q := fiberRing b v
  let : Algebra P Q := (fiberMap f g r s t b v hc hd).toAlgebra
  let : Algebra.Etale R C := hr
  let : Algebra.Etale S D := hs
  let : Fact (b.comp (algebraMap R C) = (algebraMap T U).comp (algebraMap R T)) := ⟨hc⟩
  let : Fact (v.comp (algebraMap S D) = (algebraMap T U).comp (algebraMap S T)) := ⟨hd⟩
  let : Algebra P C := (r.comp (RingHom.pullbackFst f g)).toAlgebra
  let : Algebra P D := (s.comp (RingHom.pullbackSnd f g)).toAlgebra
  let : IsScalarTower P R C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower P S D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hflat : Module.Flat P Q := flat_fiberMap f g r s t b v hc hd eC eD heC heD hf
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hr).1
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hs).1
  let := hflat
  let : Algebra.FinitePresentation R (R ⊗[P] Q) :=
    Algebra.FinitePresentation.equiv (General.fstTensorEquiv R S T b v hf eC eD heC heD).symm
  let : Algebra.FinitePresentation S (S ⊗[P] Q) :=
    Algebra.FinitePresentation.equiv (General.sndTensorEquiv R S T b v hf eC eD heC heD).symm
  have hfp : Algebra.FinitePresentation P Q :=
    finitePresentation_of_flat_of_component_baseChanges f g Q hf
  exact RingHom.Etale.iff_flat_and_formallyUnramified.mpr
    ⟨hflat, formallyUnramified_fiberMap f g r s t b v hc hd eC eD heC heD hf
      hr.formallyUnramified hs.formallyUnramified, hfp⟩

end

/-- The existing universal tensor-compatible etale patching proposition is
inhabited, with its original universe, rings, maps, and hypotheses. -/
theorem etalePatching : EtalePatching.{u} := by
  intro R S T C D U _ _ _ _ _ _ f g r s t b v hc hd
  exact etale_fiberMap f g r s t b v hc hd

end RingHom.Etale.MilnorPatching
