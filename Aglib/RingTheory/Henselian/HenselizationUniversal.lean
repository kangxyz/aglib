/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselizationHenselian
public import Aglib.RingTheory.Henselian.Etale
public import Aglib.RingTheory.Etale.LocalPoints

/-!
# The universal property of the actual henselization

Etale lifting constructs compatible maps from all actual neighborhoods into a
henselian local target. Native colimit representatives give their induced map
without restricting the target universe. The resulting local algebra map is
unique among local maps preserving the original base algebra structure.
-/

@[expose] public section

noncomputable section

open CategoryTheory IsLocalRing
open scoped TensorProduct

universe u v w

namespace HenselianLocalRing

/-- Etale residue lifting with an arbitrary henselian target, obtained by actual
tensor base change rather than a same-base hypothesis. -/
theorem residue_comp_bijective_of_etale_target (R : Type u) [CommRing R]
    (T : Type v) [CommRing T] [HenselianLocalRing T] [Algebra R T]
    (A : Type w) [CommRing A] [Algebra R A] [Algebra.Etale R A] :
    Function.Bijective (fun f : A →ₐ[R] T =>
      ((Algebra.ofId T (ResidueField T)).restrictScalars R).comp f) := by
  constructor
  · exact Algebra.Etale.residue_comp_injective R T A
  · intro p
    let q : T ⊗[R] A →ₐ[T] ResidueField T :=
      Algebra.TensorProduct.lift (Algebra.ofId T (ResidueField T)) p (fun _ _ => .all _ _)
    obtain ⟨g, hg⟩ := (residue_comp_bijective_of_etale T (T ⊗[R] A)).2 q
    refine ⟨(g.restrictScalars R).comp Algebra.TensorProduct.includeRight, ?_⟩
    apply AlgHom.ext
    intro a
    have h := AlgHom.congr_fun hg ((1 : T) ⊗ₜ[R] a)
    simpa [q, Algebra.TensorProduct.includeRight_apply] using h

end HenselianLocalRing

namespace Henselization

variable (R : Type u) [CommRing R] [IsLocalRing R]
section LocalTarget

variable (T : Type v) [CommRing T] [IsLocalRing T] [Algebra R T]
  [IsLocalHom (algebraMap R T)]

/-- Any local map preserving the original base algebra structure is compatible
with the actual residue-valued map of the constructed henselization. -/
lemma residue_comp_of_isLocalHom (f : Henselization R →ₐ[R] T)
    [IsLocalHom f.toRingHom] :
    ((Algebra.ofId T (ResidueField T)).restrictScalars R).comp f =
      (IsScalarTower.toAlgHom R (ResidueField R) (ResidueField T)).comp (residue R) := by
  apply AlgHom.ext
  intro x
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (R := R) (residue R x)
  have hm : x - algebraMap R (Henselization R) r ∈ maximalIdeal (Henselization R) := by
    rw [maximalIdeal_eq_ker_residue]
    change residue R (x - of R r) = 0
    rw [map_sub, show residue R (of R r) = IsLocalRing.residue R r from
      RingHom.congr_fun (residue_comp_of R) r, hr, sub_self]
  have hz := (IsLocalRing.residue_eq_zero_iff
    (f (x - algebraMap R (Henselization R) r))).mpr
      (map_nonunit f.toRingHom _ hm)
  have hfx : IsLocalRing.residue T (f x) =
      IsLocalRing.residue T (algebraMap R T r) := by
    simpa only [map_sub, f.commutes, sub_eq_zero] using hz
  change IsLocalRing.residue T (f x) =
    algebraMap (ResidueField R) (ResidueField T) (residue R x)
  rw [hfx, ← hr]
  rfl

end LocalTarget

variable (T : Type v) [CommRing T] [HenselianLocalRing T] [Algebra R T]
  [IsLocalHom (algebraMap R T)]

/-- The constructed henselization admits a unique local algebra map into any
henselian local algebra with a local original-base map. The target universe is
independent of the base universe. -/
theorem existsUnique_local_algHom :
    ∃! f : Henselization R →ₐ[R] T, IsLocalHom f.toRingHom := by
  let rT : T →ₐ[R] ResidueField T :=
    (Algebra.ofId T (ResidueField T)).restrictScalars R
  let rk : ResidueField R →ₐ[R] ResidueField T :=
    IsScalarTower.toAlgHom R (ResidueField R) (ResidueField T)
  have hstage (X : PointedEtaleNeighborhood R) :
      ∃ g : X.algebra →ₐ[R] T, rT.comp g = rk.comp X.point :=
    (HenselianLocalRing.residue_comp_bijective_of_etale_target R T X.algebra).2
      (rk.comp X.point)
  choose g hg using hstage
  have hcompat {X Y : PointedEtaleNeighborhood R} (f : X ⟶ Y) :
      (g Y).comp f.val = g X := by
    apply (HenselianLocalRing.residue_comp_bijective_of_etale_target R T X.algebra).1
    change rT.comp ((g Y).comp f.val) = rT.comp (g X)
    rw [← AlgHom.comp_assoc, hg, hg, AlgHom.comp_assoc, f.property]
  choose j a ha using fun x : Henselization R => exists_rep R x
  let d : Henselization R → T := fun x => g (j x) (a x)
  have hd (X : PointedEtaleNeighborhood R) (b : X.algebra) :
      d (ι R X b) = g X b := by
    obtain ⟨Z, f, k, heq⟩ := (rep_eq_iff R (a (ι R X b)) b).mp (ha (ι R X b))
    change g (j (ι R X b)) (a (ι R X b)) = g X b
    calc
      g (j (ι R X b)) (a (ι R X b)) = g Z (f.val (a (ι R X b))) :=
        (AlgHom.congr_fun (hcompat f) _).symm
      _ = g Z (k.val b) := congrArg (g Z) heq
      _ = g X b := AlgHom.congr_fun (hcompat k) b
  let φ : Henselization R →ₐ[R] T :=
    { toFun := d
      map_zero' := by
        let X : PointedEtaleNeighborhood R := Classical.choice inferInstance
        simpa only [map_zero] using hd X 0
      map_one' := by
        let X : PointedEtaleNeighborhood R := Classical.choice inferInstance
        simpa only [map_one] using hd X 1
      map_add' x y := by
        obtain ⟨X, b, hb⟩ := exists_fin_rep R (fun i : Fin 2 => if i = 0 then x else y)
        have h0 : ι R X (b 0) = x := by simpa using hb 0
        have h1 : ι R X (b 1) = y := by simpa using hb 1
        rw [← h0, ← h1, ← map_add, hd, hd, hd, map_add]
      map_mul' x y := by
        obtain ⟨X, b, hb⟩ := exists_fin_rep R (fun i : Fin 2 => if i = 0 then x else y)
        have h0 : ι R X (b 0) = x := by simpa using hb 0
        have h1 : ι R X (b 1) = y := by simpa using hb 1
        rw [← h0, ← h1, ← map_mul, hd, hd, hd, map_mul]
      commutes' r := by
        let X : PointedEtaleNeighborhood R := Classical.choice inferInstance
        have hx := RingHom.congr_fun (stageRingHom_comp_algebraMap R X) r
        change ι R X (algebraMap R X.algebra r) = algebraMap R (Henselization R) r at hx
        rw [← hx, hd, (g X).commutes] }
  have hφ (X : PointedEtaleNeighborhood R) : φ.comp (ι R X) = g X :=
    AlgHom.ext (hd X)
  have hφres (x : Henselization R) : rT (φ x) = rk (residue R x) := by
    obtain ⟨X, b, rfl⟩ := exists_rep R x
    calc
      rT (φ (ι R X b)) = rT (g X b) := congrArg rT (AlgHom.congr_fun (hφ X) b)
      _ = rk (X.point b) := AlgHom.congr_fun (hg X) b
      _ = rk (residue R (ι R X b)) :=
        congrArg rk (AlgHom.congr_fun (residue_comp_ι R X) b).symm
  have hlocal : IsLocalHom φ.toRingHom := by
    constructor
    intro x hx
    apply isUnit_of_residue_ne_zero R x
    intro hzero
    have hne : rT (φ x) ≠ 0 := isUnit_iff_ne_zero.mp (hx.map rT.toRingHom)
    apply hne
    rw [hφres, hzero, map_zero]
  refine ⟨φ, hlocal, ?_⟩
  intro ψ hψ
  let : IsLocalHom ψ.toRingHom := hψ
  have hψres := residue_comp_of_isLocalHom R T ψ
  have hstageeq (X : PointedEtaleNeighborhood R) : ψ.comp (ι R X) = g X := by
    apply (HenselianLocalRing.residue_comp_bijective_of_etale_target R T X.algebra).1
    change rT.comp (ψ.comp (ι R X)) = rT.comp (g X)
    rw [← AlgHom.comp_assoc, hg]
    change (((Algebra.ofId T (ResidueField T)).restrictScalars R).comp ψ).comp (ι R X) = _
    rw [hψres, AlgHom.comp_assoc, residue_comp_ι]
  apply AlgHom.ext
  intro x
  obtain ⟨X, b, rfl⟩ := exists_rep R x
  exact (AlgHom.congr_fun (hstageeq X) b).trans (AlgHom.congr_fun (hφ X) b).symm

end Henselization
