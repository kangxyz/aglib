/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselizationHenselian
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.FieldTheory.IsSepClosed

/-! # Generic maps from the actual henselization to a separably closed field

An injective map from a local domain to a separably closed field extends to
the actual henselization. This is a generic map: no localness of the original
map or of the extension is assumed. The proof uses a field quotient of the
nonzero generic fibre and the relative separable closure of its fraction base.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Henselization

universe u v

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The actual pointed-etale colimit is flat over its original local ring. -/
theorem flat_over_base : Module.Flat R (Henselization R) := by
  classical
  apply Module.Flat.of_forall_isTrivialRelation
  intro n r x hx
  obtain ⟨X, a, ha⟩ := exists_fin_rep R x
  have heq : ι R X (∑ i, r i • a i) = ι R X 0 := by
    simpa only [map_sum, map_smul, map_zero, ha] using hx
  obtain ⟨Y, f, g, hY⟩ := (rep_eq_iff R (∑ i, r i • a i) 0).mp heq
  have hrel : ∑ i, r i • f.val (a i) = 0 := by
    simpa only [map_sum, map_smul, map_zero] using hY
  let : Module.Flat R Y.algebra := Algebra.Smooth.flat R Y.algebra
  obtain ⟨k, b, y, hb, hby⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  refine ⟨k, b, fun j => ι R Y (y j), ?_, hby⟩
  intro i
  calc
    x i = ι R X (a i) := (ha i).symm
    _ = ι R Y (f.val (a i)) := (AlgHom.congr_fun (ι_naturality f) (a i)).symm
    _ = ∑ j, b i j • ι R Y (y j) := by
      simpa only [map_sum, map_smul] using congrArg (ι R Y) (hb i)

private theorem etale_image_isSeparable (F : Type u) (E : Type v)
    [Field F] [Field E] [Algebra F E]
    (C : Type u) [CommRing C] [Algebra F C] [Algebra.Etale F C]
    (f : C →ₐ[F] E) (c : C) : IsSeparable F (f c) := by
  let q : Ideal C := RingHom.ker f.toRingHom
  let : q.IsPrime := RingHom.ker_isPrime f.toRingHom
  let : Module.Finite F C := Algebra.FormallyUnramified.finite_of_free F C
  let : IsArtinianRing C := isArtinian_of_tower F inferInstance
  let : q.IsMaximal := inferInstance
  let : Field (C ⧸ q) := Ideal.Quotient.field q
  let : Algebra.IsSeparable F (C ⧸ q) := inferInstance
  let g : C ⧸ q →ₐ[F] E := Ideal.kerLiftAlg f
  exact (Algebra.IsSeparable.isSeparable F (Ideal.Quotient.mk q c)).map g g.injective

variable [IsDomain R]
  (K : Type v) [Field K] [IsSepClosed K] [Algebra R K]

/-- The original generic field-valued map extends to the henselization.
The local universal property is not used: the map into the field may send
nonunits of the original local ring to units. -/
theorem nonempty_algHom_of_injective
    (hinj : Function.Injective (algebraMap R K)) :
    Nonempty (Henselization R →ₐ[R] K) := by
  classical
  let F := FractionRing R
  let : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).mpr hinj
  let : Algebra F K := FractionRing.liftAlgebra R K
  let : IsScalarTower R F K := FractionRing.isScalarTower_liftAlgebra R K
  let : Module.Flat R (Henselization R) := flat_over_base R
  let : Nontrivial (Henselization R) := (residue R).toRingHom.domain_nontrivial
  let T := F ⊗[R] Henselization R
  let : Nontrivial T :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_right
      R F (Henselization R) (IsFractionRing.injective R F)
  obtain ⟨q, hq⟩ := Ideal.exists_maximal T
  let : q.IsMaximal := hq
  let E := T ⧸ q
  let : Field E := Ideal.Quotient.field q
  let i : Henselization R →ₐ[R] E :=
    ((Ideal.Quotient.mkₐ F q).restrictScalars R).comp Algebra.TensorProduct.includeRight
  have hi (a : Henselization R) : IsSeparable F (i a) := by
    obtain ⟨X, x, rfl⟩ := exists_rep R a
    let j : F ⊗[R] X.algebra →ₐ[R] E :=
      Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R F E) (i.comp (ι R X))
        (fun _ _ => Commute.all _ _)
    let f : F ⊗[R] X.algebra →ₐ[F] E :=
      { j.toRingHom with
        commutes' t := by
          change j (t ⊗ₜ[R] (1 : X.algebra)) = algebraMap F E t
          simp only [j, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
          rfl }
    have hf : f ((1 : F) ⊗ₜ[R] x) = i (ι R X x) := by
      change j ((1 : F) ⊗ₜ[R] x) = i (ι R X x)
      simp only [j, Algebra.TensorProduct.lift_tmul, map_one, one_mul,
        AlgHom.comp_apply]
    rw [← hf]
    exact etale_image_isSeparable F E (F ⊗[R] X.algebra) f _
  let S := separableClosure F E
  let iS : Henselization R →ₐ[R] S :=
    { toFun := fun a => ⟨i a, hi a⟩
      map_zero' := Subtype.ext (map_zero i)
      map_one' := Subtype.ext (map_one i)
      map_add' a b := Subtype.ext (map_add i a b)
      map_mul' a b := Subtype.ext (map_mul i a b)
      commutes' r := Subtype.ext (i.commutes r) }
  exact ⟨((IsSepClosed.lift : S →ₐ[F] K).restrictScalars R).comp iS⟩

end Henselization
