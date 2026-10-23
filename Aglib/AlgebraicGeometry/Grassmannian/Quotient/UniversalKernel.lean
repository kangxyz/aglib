/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.Quotient.Representability
public import Aglib.AlgebraicGeometry.Grassmannian.Quotient.KernelRank

/-!
# The universal kernel on the Grassmannian

The universal kernel `universalKernel R k n` is the kernel of the representative
`universalQuotientRep R k n : O^n ⟶ Q_univ` of the universal rank-`k` quotient on
`schemeOver R k n`, with inclusion `universalKernelι R k n` into `O^n`. It is finite locally free
of rank `n - k` (`isFiniteLocallyFree_universalKernel`, `sheafHasRank_universalKernel`).

Let `g : T ⟶ schemeOver R k n` be a morphism of schemes over `Spec R` and `P` a representative of
the class `(quotFunctorRepresentableBy R k n).homEquiv g` that `g` classifies. Then the pullback of
the universal quotient along `g` is isomorphic to `P` under `O_T^n` (`isoUnderOfHomEquiv`), and
`g^*` of the universal kernel is the kernel of `P`: `pullbackUniversalKernelIso g P h`, compatible
with the inclusions into `O_T^n` through `pullbackFreeIso`
(`pullbackUniversalKernelIso_hom_kernelι`; in limit form, `pullbackUniversalKernelιIsKernel`). The
classifying map of a quotient `P` is
`classifyingMap P := (quotFunctorRepresentableBy R k n).homEquiv.symm ⟦P⟧`
(`pullbackUniversalKernelIsoOfClassifying`). It is natural, `classifyingMap (P.pullback φ.left) =
φ ≫ classifyingMap P` (`classifyingMap_pullback`), and two quotients have the same classifying
map exactly when they are isomorphic under `O_T^n` (`classifyingMap_eq_classifyingMap_iff`).

Source: Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 26: for
`G = Grass(W ⊗ Sym^r V, Φ(r))` with universal quotient `u : p_G^* E → U` and kernel
`v : K → p_G^* E`, the map `π_T^* π_{T*}(G(r)) → π_T^* π_{T*}(E_T(r))` is the pullback of `v`
along `T → G`; and `K_Y = ker(f_Y) = φ^* ker(f)` in property (F). Encoded subset: `E = O^n` over
`Spec R`, quotients of `O^n = SheafOfModules.free (ULift (Fin n))` of rank `k`, all `k` and `n`;
arbitrary `g` (no flatness). Convention: `k` is the rank of the quotient, so this is Nitsure's
`Grass(n, k)`.
Premise: `BaseChangeMkQFormula`, supplied by `Aglib.RingTheory.Grassmannian.BaseChangeFormula`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Grassmannian

open Scheme.Modules LocallyFreeQuotient

variable (R : CommRingCat.{u}) (k n : ℕ)
variable [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]

/-- The universal kernel on the Grassmannian: the kernel of the representative
`universalQuotientRep R k n : O^n ⟶ Q_univ` of the universal quotient. -/
def universalKernel : (schemeOver R k n).left.Modules :=
  (universalQuotientRep R k n).kernel

/-- The inclusion of the universal kernel into `O^n` on the Grassmannian. -/
def universalKernelι : universalKernel R k n ⟶ freeSheaf (schemeOver R k n).left n :=
  (universalQuotientRep R k n).kernelι

instance mono_universalKernelι : Mono (universalKernelι R k n) :=
  inferInstanceAs (Mono (universalQuotientRep R k n).kernelι)

/-- The universal kernel is finite locally free. -/
instance isFiniteLocallyFree_universalKernel :
    IsFiniteLocallyFree (schemeOver R k n).left (universalKernel R k n) :=
  (universalQuotientRep R k n).isFiniteLocallyFree_kernel

/-- The universal kernel has constant rank `n - k`. -/
theorem sheafHasRank_universalKernel : SheafHasRank (universalKernel R k n) (n - k) :=
  (universalQuotientRep R k n).sheafHasRank_kernel

variable {R k n}

/-- The pullback of the universal quotient along `g` represents the class classified by `g`. -/
theorem mk_pullback_universalQuotientRep {T : Over (Spec R)} (g : T ⟶ schemeOver R k n) :
    (Quotient.mk _ ((universalQuotientRep R k n).pullback g.left) :
        (quotFunctor R k n).obj (op T)) = (quotFunctorRepresentableBy R k n).homEquiv g := by
  rw [quotFunctorRepresentableBy_homEquiv, ← mk_universalQuotientRep, quotFunctor_map_mk]
  rfl

/-- If `P` represents the class classified by `g`, the pullback of the universal quotient along
`g` is isomorphic to `P` under `O_T^n` (uniquely, `IsoUnder.ext'`). -/
def isoUnderOfHomEquiv {T : Over (Spec R)} (g : T ⟶ schemeOver R k n)
    (P : LocallyFreeQuotient T.left k n)
    (h : (quotFunctorRepresentableBy R k n).homEquiv g = Quotient.mk _ P) :
    IsoUnder ((universalQuotientRep R k n).pullback g.left) P :=
  Classical.choice (Quotient.exact ((mk_pullback_universalQuotientRep g).trans h))

/-- **The universal kernel pulls back to the kernel of a representative.** If `P` represents the
class classified by `g : T ⟶ schemeOver R k n`, then `g^*` of the universal kernel is the kernel of
`P`. No flatness of `g` is needed. -/
def pullbackUniversalKernelIso {T : Over (Spec R)} (g : T ⟶ schemeOver R k n)
    (P : LocallyFreeQuotient T.left k n)
    (h : (quotFunctorRepresentableBy R k n).homEquiv g = Quotient.mk _ P) :
    (Scheme.Modules.pullback g.left).obj (universalKernel R k n) ≅ P.kernel :=
  LocallyFreeQuotient.pullbackKernelIso g.left (universalQuotientRep R k n) ≪≫
    (isoUnderOfHomEquiv g P h).kernelIso

/-- Under `pullbackUniversalKernelIso`, the inclusion of the kernel of `P` into `O_T^n` is the
pullback of the universal inclusion followed by `pullbackFreeIso g.left : g^* O^n ≅ O_T^n`. -/
@[reassoc (attr := simp)]
theorem pullbackUniversalKernelIso_hom_kernelι {T : Over (Spec R)} (g : T ⟶ schemeOver R k n)
    (P : LocallyFreeQuotient T.left k n)
    (h : (quotFunctorRepresentableBy R k n).homEquiv g = Quotient.mk _ P) :
    (pullbackUniversalKernelIso g P h).hom ≫ P.kernelι =
      (Scheme.Modules.pullback g.left).map (universalKernelι R k n) ≫
        (pullbackFreeIso g.left (ULift.{u} (Fin n))).hom := by
  simp only [pullbackUniversalKernelIso, CategoryTheory.Iso.trans_hom, Category.assoc,
    IsoUnder.kernelIso_hom_kernelι, LocallyFreeQuotient.pullbackKernelIso_hom_kernelι]
  rfl

/-- In limit form: if `P` represents the class classified by `g`, the pullback of the universal
inclusion, followed by `pullbackFreeIso g.left`, is a kernel of the quotient map of `P`. -/
def pullbackUniversalKernelιIsKernel {T : Over (Spec R)} (g : T ⟶ schemeOver R k n)
    (P : LocallyFreeQuotient T.left k n)
    (h : (quotFunctorRepresentableBy R k n).homEquiv g = Quotient.mk _ P) :
    IsLimit (KernelFork.ofι (f := P.π)
      ((Scheme.Modules.pullback g.left).map (universalKernelι R k n) ≫
        (pullbackFreeIso g.left (ULift.{u} (Fin n))).hom)
      (by rw [← pullbackUniversalKernelIso_hom_kernelι g P h, Category.assoc, kernelι_π,
        comp_zero])) :=
  IsLimit.ofIsoLimit P.kernelIsKernel
    (Fork.ext (pullbackUniversalKernelIso g P h).symm
      (by
        simp only [Fork.ofι_pt, CategoryTheory.Iso.symm_hom, Fork.ι_ofι]
        rw [CategoryTheory.Iso.inv_comp_eq, pullbackUniversalKernelIso_hom_kernelι]))

/-- The classifying map of a quotient `P` on `T`: the map to the Grassmannian corresponding to its
class under `quotFunctorRepresentableBy`. -/
def classifyingMap {T : Over (Spec R)} (P : LocallyFreeQuotient T.left k n) :
    T ⟶ schemeOver R k n :=
  (quotFunctorRepresentableBy R k n).homEquiv.symm (Quotient.mk _ P)

theorem homEquiv_classifyingMap {T : Over (Spec R)} (P : LocallyFreeQuotient T.left k n) :
    (quotFunctorRepresentableBy R k n).homEquiv (classifyingMap P) = Quotient.mk _ P :=
  Equiv.apply_symm_apply _ _

/-- The classifying map is natural: the classifying map of the pullback of `P` along `φ` is `φ`
followed by the classifying map of `P`. -/
theorem classifyingMap_pullback {T T' : Over (Spec R)} (φ : T' ⟶ T)
    (P : LocallyFreeQuotient T.left k n) :
    classifyingMap (P.pullback φ.left) = φ ≫ classifyingMap P :=
  ((quotFunctorRepresentableBy R k n).comp_homEquiv_symm
    (Quotient.mk _ P : (quotFunctor R k n).obj (op T)) φ).symm

/-- Isomorphic quotients under `O_T^n` have the same classifying map. -/
theorem classifyingMap_eq_of_isoUnder {T : Over (Spec R)} {P Q : LocallyFreeQuotient T.left k n}
    (e : IsoUnder P Q) : classifyingMap P = classifyingMap Q :=
  congrArg (quotFunctorRepresentableBy R k n).homEquiv.symm (Quotient.sound ⟨e⟩)

/-- Two quotients have the same classifying map exactly when they are isomorphic under `O_T^n`. -/
theorem classifyingMap_eq_classifyingMap_iff {T : Over (Spec R)}
    {P Q : LocallyFreeQuotient T.left k n} :
    classifyingMap P = classifyingMap Q ↔ Nonempty (IsoUnder P Q) :=
  ⟨fun h ↦ Quotient.exact ((quotFunctorRepresentableBy R k n).homEquiv.symm.injective h),
    fun ⟨e⟩ ↦ classifyingMap_eq_of_isoUnder e⟩

/-- The pullback of the universal kernel along the classifying map of `P` is the kernel of `P`. -/
def pullbackUniversalKernelIsoOfClassifying {T : Over (Spec R)}
    (P : LocallyFreeQuotient T.left k n) :
    (Scheme.Modules.pullback (classifyingMap P).left).obj (universalKernel R k n) ≅ P.kernel :=
  pullbackUniversalKernelIso (classifyingMap P) P (homEquiv_classifyingMap P)

end AlgebraicGeometry.Grassmannian
