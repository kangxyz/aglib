/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.DualExact
public import Aglib.AlgebraicGeometry.Modules.InternalHom.FreeDual
public import Aglib.AlgebraicGeometry.Modules.InternalHom.BidualLocallyFree
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Coherent
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.KernelPullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.QuasiAffine

/-! # Original finite-free co-resolutions on quasi-affine schemes

Two original finite-free epimorphisms, onto the dual and its actual kernel,
construct the co-resolution. Reversed exactness and canonical biduality
retain the original maps. Arbitrary pullback preserves the construction's
exactness by the proved local splitting of the two finite locally free
kernel sequences, not by an ambient flatness hypothesis.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- Every vector bundle on a quasi-affine scheme has an original finite-free
co-resolution which remains exact and injective after every change of base. -/
theorem exists_universallyExact_finiteFree_coresolution
    (X : Scheme.{u}) [X.IsQuasiAffine] (M : X.Modules) [IsFiniteLocallyFree X M] :
    ∃ (I J : Type u) (_ : Finite I) (_ : Finite J)
      (i : M ⟶ SheafOfModules.free (R := X.ringCatSheaf) I)
      (d : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
        SheafOfModules.free (R := X.ringCatSheaf) J) (w : i ≫ d = 0),
      (ShortComplex.mk i d w).Exact ∧ Mono i ∧
      ∀ (Y : Scheme.{u}) (a : Y ⟶ X),
        ((ShortComplex.mk i d w).map (pullback a)).Exact ∧ Mono ((pullback a).map i) := by
  let D := InternalHom.dualFunctor X
  let : D.Additive := InternalHom.dualFunctor_additive X
  let : IsFiniteLocallyFree X (dualSheaf X M) := InternalHom.finiteLocallyFree_dual M
  have hpdata := QuasiCoherent.quasiAffine_exists_finiteFree_epi X (dualSheaf X M)
    (coherent_of_finiteLocallyFree (dualSheaf X M))
  obtain ⟨I, hI, p, hp⟩ := hpdata
  let := hI
  let := hp
  let : IsFiniteLocallyFree X (ShortComplex.kernelSequence p).X₂ :=
    inferInstanceAs (IsFiniteLocallyFree X (SheafOfModules.free (R := X.ringCatSheaf) I))
  let : IsFiniteLocallyFree X (ShortComplex.kernelSequence p).X₃ :=
    inferInstanceAs (IsFiniteLocallyFree X (dualSheaf X M))
  have hpseq := shortExact_kernelSequence p
  let : IsFiniteLocallyFree X (kernel p) := finiteLocallyFree_X₁_of_shortExact hpseq
  let : IsFiniteLocallyFree X (ShortComplex.kernelSequence p).X₁ :=
    inferInstanceAs (IsFiniteLocallyFree X (kernel p))
  have hqdata := QuasiCoherent.quasiAffine_exists_finiteFree_epi X (kernel p)
    (coherent_of_finiteLocallyFree (kernel p))
  obtain ⟨J, hJ, q, hq⟩ := hqdata
  let := hJ
  let := hq
  let : IsFiniteLocallyFree X (ShortComplex.kernelSequence q).X₂ :=
    inferInstanceAs (IsFiniteLocallyFree X (SheafOfModules.free (R := X.ringCatSheaf) J))
  let : IsFiniteLocallyFree X (ShortComplex.kernelSequence q).X₃ :=
    inferInstanceAs (IsFiniteLocallyFree X (kernel p))
  have hqseq := shortExact_kernelSequence q
  let : IsFiniteLocallyFree X (kernel q) := finiteLocallyFree_X₁_of_shortExact hqseq
  let : IsFiniteLocallyFree X (ShortComplex.kernelSequence q).X₁ :=
    inferInstanceAs (IsFiniteLocallyFree X (kernel q))
  let : IsFiniteLocallyFree X (dualSheaf X (kernel p)) :=
    InternalHom.finiteLocallyFree_dual (kernel p)
  let : IsFiniteLocallyFree X (dualSheaf X (kernel q)) :=
    InternalHom.finiteLocallyFree_dual (kernel q)
  let S₀ := (ShortComplex.kernelSequence p).op.map D
  let S₁ := (ShortComplex.kernelSequence q).op.map D
  let : IsFiniteLocallyFree X S₀.X₃ :=
    inferInstanceAs (IsFiniteLocallyFree X (dualSheaf X (kernel p)))
  let : IsFiniteLocallyFree X S₁.X₃ :=
    inferInstanceAs (IsFiniteLocallyFree X (dualSheaf X (kernel q)))
  have h₀ : S₀.ShortExact := InternalHom.dual_shortExact _ hpseq
  have h₁ : S₁.ShortExact := InternalHom.dual_shortExact _ hqseq
  let t := S₁.f
  let : Mono t := h₁.mono_f
  let T₀ : ShortComplex X.Modules := ShortComplex.mk S₀.f (S₀.g ≫ t)
    (by rw [← Category.assoc, S₀.zero, zero_comp])
  have hT₀ : T₀.Exact :=
    T₀.exact_of_f_is_kernel (isKernelCompMono h₀.fIsKernel t rfl)
  let : Mono T₀.f := h₀.mono_f
  have hT₀base (Y : Scheme.{u}) (a : Y ⟶ X) :
      (T₀.map (pullback a)).Exact ∧ Mono ((pullback a).map T₀.f) := by
    have h₀a := shortExact_pullback a h₀
    have h₁a := shortExact_pullback a h₁
    let : Mono ((pullback a).map t) := h₁a.mono_f
    refine ⟨?_, h₀a.mono_f⟩
    apply (T₀.map (pullback a)).exact_of_f_is_kernel
    exact isKernelCompMono h₀a.fIsKernel ((pullback a).map t)
      ((pullback a).map_comp S₀.g t)
  let bM := finiteLocallyFreeBidualIso M
  let b₀ := InternalHom.dualFreeIso X I
  let b₁ := InternalHom.dualFreeIso X J
  let i := bM.hom ≫ T₀.f ≫ b₀.hom
  let d := b₀.inv ≫ T₀.g ≫ b₁.hom
  have w : i ≫ d = 0 := by
    calc
      i ≫ d = bM.hom ≫ (T₀.f ≫ T₀.g) ≫ b₁.hom := by
        simp only [i, d, Category.assoc, Iso.hom_inv_id_assoc]
      _ = 0 := by
        have hz := congrArg (fun k : T₀.X₁ ⟶ T₀.X₃ => bM.hom ≫ k ≫ b₁.hom) T₀.zero
        have hzero : (0 : T₀.X₁ ⟶ T₀.X₃) ≫ b₁.hom = 0 := zero_comp
        have hcomp : bM.hom ≫
            (0 : T₀.X₁ ⟶ SheafOfModules.free (R := X.ringCatSheaf) J) = 0 := comp_zero
        exact hz.trans ((congrArg (fun k : T₀.X₁ ⟶ _ => bM.hom ≫ k)
          hzero).trans hcomp)
  let T := ShortComplex.mk i d w
  let e : T₀ ≅ T := ShortComplex.isoMk bM.symm b₀ b₁
    (by simp only [T, i, Iso.symm_hom, Iso.inv_hom_id_assoc])
    (by simp only [T, d, Iso.hom_inv_id_assoc])
  refine ⟨I, J, hI, hJ, i, d, w, ShortComplex.exact_of_iso e hT₀, ?_, ?_⟩
  · dsimp only [i]
    infer_instance
  · intro Y a
    obtain ⟨hTa, hm⟩ := hT₀base Y a
    let := hm
    refine ⟨ShortComplex.exact_of_iso ((pullback a).mapShortComplex.mapIso e) hTa, ?_⟩
    dsimp only [i]
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance

end AlgebraicGeometry.Scheme.Modules
