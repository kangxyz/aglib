/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FullFaithful
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientCompletionUnit
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientFactorization

/-! # Proper completion detects annihilation through ordinary stage kernels

The original coherent monomorphism is factored through its quotient by the
bounding ideal. Full faithfulness lifts that factorization, forcing the original
epi quotient unit to be mono. No left exactness of ordinary reduction and no
faithful flatness of an affine chart completion is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}}
  [IsLocallyNoetherian X] (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]

/-- The original coherent subobject is killed if its completed inclusion lands
in ordinary stage kernels killed by the same ideal. -/
theorem killedByIdealSheaf_of_completion_kernel
    (K : X.IdealSheafData) {L G : X.CoherentSheaf} (s : L ⟶ G) [Mono s.hom]
    {T : AdicSystem X (idealThickeningIdealSheaf f I)}
    (α : (completionFunctor X (idealThickeningIdealSheaf f I)).obj G ⟶ T)
    (hzero : ∀ n : ℕ,
      ((completionFunctor X (idealThickeningIdealSheaf f I)).map s).hom.app (op n) ≫
        α.hom.app (op n) = 0)
    (hk : ∀ n : ℕ, killedByIdealSheaf K (kernel (α.hom.app (op n)))) :
    killedByIdealSheaf K L.obj := by
  let J := idealThickeningIdealSheaf f I
  let C := completionFunctor X J
  let Q := idealSheafCoherentQuotient X K L
  let q := idealSheafCoherentQuotientUnit X K L
  let δ := diagramQuotientDescOfKernel X K (C.map s).hom α.hom
    (fun n => hzero n.unop) (fun n => hk n.unop)
  let d : AdicSystem.quotient X J K (C.obj L) ⟶ C.obj G := ObjectProperty.homMk δ
  let e := idealSheafQuotientCompletionIso X J K L
  let γ : C.obj Q ⟶ C.obj G := e.hom ≫ d
  have hd : AdicSystem.quotientUnit X J K (C.obj L) ≫ d = C.map s := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext n
    exact diagramQuotientDescOfKernel_unit X K (C.map s).hom α.hom
      (fun n => hzero n.unop) (fun n => hk n.unop) n
  have hγ : C.map q ≫ γ = C.map s :=
    (Category.assoc (C.map q) e.hom d).symm.trans
      ((congrArg (fun z => z ≫ d)
        (completionQuotientUnit_interchange X J K L)).trans hd)
  let ff := completionFunctorFullyFaithful I f
  have hsq : q ≫ ff.preimage γ = s := by
    apply ff.map_injective
    rw [Functor.map_comp, ff.map_preimage]
    exact hγ
  have heq : q.hom ≫ (ff.preimage γ).hom = s.hom :=
    congrArg (fun z : L ⟶ G => z.hom) hsq
  let : Mono q.hom := mono_of_mono_fac heq
  let : Epi q.hom := inferInstanceAs
    (Epi ((pullbackPushforwardAdjunction K.subschemeι).unit.app L.obj))
  let : IsIso q.hom := isIso_of_mono_of_epi q.hom
  have hi : IsIso ((pullbackPushforwardAdjunction K.subschemeι).unit.app L.obj) :=
    inferInstanceAs (IsIso q.hom)
  simpa only [IdealSheafData.ker_subschemeι] using
    (pullbackPushforwardUnit_isIso_iff_killedByIdealSheaf K.subschemeι L.obj).mp hi

/-- Uniform ordinary reduced kernel bounds hold on the actual algebraic kernel.
This does not identify a reduced kernel with the kernel of a reduced map. -/
theorem killedByIdealSheaf_kernel_of_completion (K : X.IdealSheafData)
    {M N : X.CoherentSheaf} (φ : M ⟶ N)
    (h : ∀ n : ℕ, killedByIdealSheaf K
      (kernel ((idealSheafQuotientFunctor X (idealThickeningIdealSheaf f I ^ n)).map
        φ.hom))) :
    killedByIdealSheaf K (kernel φ.hom) := by
  let L : X.CoherentSheaf := ⟨kernel φ.hom,
    (QuasiCoherent.affineLocallyFiniteType X).prop_kernel φ.hom M.property N.property⟩
  let s : L ⟶ M := ObjectProperty.homMk (kernel.ι φ.hom)
  let : Mono s.hom := inferInstanceAs (Mono (kernel.ι φ.hom))
  apply killedByIdealSheaf_of_completion_kernel I f K s
    ((completionFunctor X (idealThickeningIdealSheaf f I)).map φ)
  · intro n
    change (idealSheafQuotientFunctor X (idealThickeningIdealSheaf f I ^ n)).map
      (kernel.ι φ.hom) ≫
      (idealSheafQuotientFunctor X (idealThickeningIdealSheaf f I ^ n)).map φ.hom = 0
    rw [← Functor.map_comp, kernel.condition]
    exact (idealSheafQuotientFunctor X (idealThickeningIdealSheaf f I ^ n)).map_zero _ _
  · exact h

end AlgebraicGeometry.Scheme.Cohomology
