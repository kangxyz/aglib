/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.BaseChange
public import Aglib.Algebra.Homology.ShortComplex.BaseChange.Projective
public import Aglib.Algebra.Homology.Flat.UniversalTensor
public import Mathlib.RingTheory.LocalRing.Module

/-!
# A local criterion from the original residue-field base-change map

Over a local ring, the native residue-field homology comparison is
surjective exactly when the original outgoing cokernel is free. It is
then invertible after every ring map. Only finiteness of the middle term
and finite flatness of the last term are needed. The first term need not
be finite, and the ring need not be Noetherian.

The proof first obtains actual tensor exactness of the original cycle
sequence. Its map from opcycles is then residue-field injective, so the
native local module criterion applies to its original image quotient.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

universe u v

variable {R : Type u} [CommRing R] [IsLocalRing R]
    (S : ShortComplex (ModuleCat.{max u v} R))

/-- A surjective original residue-field homology mate makes the actual outgoing cokernel
free over the local ring. No finiteness of the first term or Noetherianity is assumed. -/
theorem free_cokernel_of_epi_residue_homologyBaseChangeMap
    [Module.Finite R S.X₂] [Module.Finite R S.X₃] [Module.Flat R S.X₃]
    [Epi (ModuleCat.homologyBaseChangeMap
      (algebraMap R (IsLocalRing.ResidueField R)) S)] :
    Module.Free R (cokernel S.g : ModuleCat.{max u v} R) := by
  let k := IsLocalRing.ResidueField R
  let T := S.cyclesShortComplex
  let : Module.Finite R T.X₂ := by
    change Module.Finite R S.X₂
    infer_instance
  let : Module.Finite R T.X₃ := by
    change Module.Finite R S.X₃
    infer_instance
  have h : Function.Exact (T.f.hom.lTensor k) (T.g.hom.lTensor k) :=
    S.lTensor_cycles_exact_of_epi_homologyBaseChangeMap (B := k)
  have hi : Function.Injective (T.fromOpcycles.hom.lTensor k) :=
    T.fromOpcycles_lTensor_injective_of_exact k h
  have hp : Function.Surjective T.pOpcycles :=
    (ModuleCat.epi_iff_surjective T.pOpcycles).mp inferInstance
  let : Module.Finite R T.opcycles := Module.Finite.of_surjective T.pOpcycles.hom hp
  let : Module.Free R S.X₃ := Module.free_of_flat_of_isLocalRing
  let : Module.Free R T.X₃ := by
    change Module.Free R S.X₃
    infer_instance
  have hfree : Module.Free R (S.X₃ ⧸ LinearMap.range T.fromOpcycles.hom) :=
    Module.free_of_lTensor_residueField_injective T.fromOpcycles.hom
      (Submodule.mkQ _) (Submodule.mkQ_surjective _)
      T.fromOpcycles.hom.exact_map_mkQ_range hi
  have he (x : S.X₂) : T.fromOpcycles (T.pOpcycles x) = S.g x :=
    congrArg (fun f => f x) T.p_fromOpcycles
  have hr : LinearMap.range T.fromOpcycles.hom = LinearMap.range S.g.hom := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨z, rfl⟩ := hp y
      exact ⟨z, (he z).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨T.pOpcycles z, he z⟩
  rw [hr] at hfree
  let : Module.Free R (S.X₃ ⧸ LinearMap.range S.g.hom) := hfree
  exact Module.Free.of_equiv (ModuleCat.cokernelIsoRangeQuotient S.g).symm.toLinearEquiv

/-- Surjectivity of the original residue-field homology mate is equivalent to freeness
of the original outgoing cokernel. The first term need not be finite. -/
theorem epi_residue_homologyBaseChangeMap_iff_free_cokernel
    [Module.Finite R S.X₂] [Module.Finite R S.X₃] [Module.Flat R S.X₃] :
    Epi (ModuleCat.homologyBaseChangeMap (algebraMap R (IsLocalRing.ResidueField R)) S) ↔
      Module.Free R (cokernel S.g : ModuleCat.{max u v} R) := by
  constructor
  · intro h
    let := h
    exact S.free_cokernel_of_epi_residue_homologyBaseChangeMap
  · intro h
    let : Module.Free R (cokernel S.g : ModuleCat.{max u v} R) := h
    let : Module.Free R S.X₃ := Module.free_of_flat_of_isLocalRing
    let : IsIso (ModuleCat.homologyBaseChangeMap
        (algebraMap R (IsLocalRing.ResidueField R)) S) :=
      ModuleCat.homologyBaseChangeMap_isIso_of_projective_cokernel _ S
    infer_instance

universe w

/-- A surjective original residue-field mate gives invertibility of the original mate
after every ring map, including nonflat maps and target rings in a larger universe. -/
theorem homologyBaseChangeMap_isIso_of_epi_residue
    {B : Type w} [CommRing B] (σ : R →+* B)
    (S : ShortComplex (ModuleCat.{max u v w} R))
    [Module.Finite R S.X₂] [Module.Finite R S.X₃] [Module.Flat R S.X₃]
    [Epi (ModuleCat.homologyBaseChangeMap.{u, max v w, u}
      (algebraMap R (IsLocalRing.ResidueField R)) S)] :
    IsIso (ModuleCat.homologyBaseChangeMap.{u, max u v, w} σ S) := by
  let : Module.Free R S.X₃ := Module.free_of_flat_of_isLocalRing
  let : Module.Free R (cokernel S.g : ModuleCat.{max u v w} R) :=
    free_cokernel_of_epi_residue_homologyBaseChangeMap.{u, max v w} S
  exact ModuleCat.homologyBaseChangeMap_isIso_of_projective_cokernel.{u, max u v, w} σ S

end CategoryTheory.ShortComplex
