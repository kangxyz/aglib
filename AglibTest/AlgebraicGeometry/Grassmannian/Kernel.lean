/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Grassmannian.BaseChangeFormula
public import Aglib.AlgebraicGeometry.Grassmannian.Quotient.Reindex
public import Aglib.AlgebraicGeometry.Grassmannian.Finiteness

/-!
# Kernels, reindexing and finiteness for the Grassmannian

The instance in `Aglib.RingTheory.Grassmannian.BaseChangeFormula` supplies the premise
`Module.Grassmannian.BaseChangeMkQFormula`. The declarations below restate, with no hypothesis, the
inputs of the Hilbert-scheme construction (Nitsure, arXiv:math/0504590v1, §5, p. 26): the
kernel of a rank-`k` locally free quotient of `O^n` is finite locally free of rank `n - k` and its
formation commutes with every pullback; the universal kernel pulls back to the kernel of a
representative; rank-`k` quotients of a free sheaf with a finite basis `I ≃ ULift (Fin n)` are
classified by the Grassmannian; and over a Noetherian ring the Grassmannian is Noetherian with
structure morphism of finite type.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite Limits AlgebraicGeometry

universe u

namespace AglibTest.GrassmannianKernel

open AlgebraicGeometry.Grassmannian AlgebraicGeometry.Scheme.Modules

/-- In a short exact sequence with finite locally free middle and last terms, the first term is
finite locally free. -/
theorem finiteLocallyFree_X₁_of_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [IsFiniteLocallyFree X S.X₂] [IsFiniteLocallyFree X S.X₃] :
    IsFiniteLocallyFree X S.X₁ :=
  AlgebraicGeometry.Scheme.Modules.finiteLocallyFree_X₁_of_shortExact hS

/-- Fibre ranks are additive along a short exact sequence of finite locally free sheaves. -/
theorem sheafRank_X₂_eq_add_of_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [IsFiniteLocallyFree X S.X₁] [IsFiniteLocallyFree X S.X₃] (x : X) :
    sheafRank S.X₂ x = sheafRank S.X₁ x + sheafRank S.X₃ x :=
  AlgebraicGeometry.Scheme.Modules.sheafRank_X₂_eq_add_of_shortExact hS x

/-- The kernel of a quotient of `O_X^n` is finite locally free of rank `n - k`. -/
theorem sheafHasRank_kernel {X : Scheme.{u}} {k n : ℕ} (q : LocallyFreeQuotient X k n) :
    IsFiniteLocallyFree X q.kernel ∧ SheafHasRank q.kernel (n - k) :=
  ⟨inferInstance, q.sheafHasRank_kernel⟩

/-- The sequence `0 → K → O_X^n → Q → 0` is short exact. -/
theorem shortExact {X : Scheme.{u}} {k n : ℕ} (q : LocallyFreeQuotient X k n) :
    q.shortComplex.ShortExact :=
  q.shortExact

/-- The pullback of the kernel is the kernel of the pulled back quotient, compatibly with the
inclusions into `O^n` (no flatness). -/
theorem pullbackKernelIso_hom_kernelι {X Y : Scheme.{u}} {k n : ℕ} (f : Y ⟶ X)
    (q : LocallyFreeQuotient X k n) :
    (LocallyFreeQuotient.pullbackKernelIso f q).hom ≫ (q.pullback f).kernelι =
      (Scheme.Modules.pullback f).map q.kernelι ≫ (pullbackFreeIso f (ULift.{u} (Fin n))).hom :=
  LocallyFreeQuotient.pullbackKernelIso_hom_kernelι f q

/-- The universal kernel pulls back along `g` to the kernel of any representative of the class
classified by `g`, compatibly with the inclusions into `O^n`. -/
theorem pullbackUniversalKernelIso_hom_kernelι (R : CommRingCat.{u}) (k n : ℕ)
    {T : Over (Spec R)} (g : T ⟶ schemeOver R k n) (P : LocallyFreeQuotient T.left k n)
    (h : (quotFunctorRepresentableBy R k n).homEquiv g = Quotient.mk _ P) :
    (pullbackUniversalKernelIso g P h).hom ≫ P.kernelι =
      (Scheme.Modules.pullback g.left).map (universalKernelι R k n) ≫
        (pullbackFreeIso g.left (ULift.{u} (Fin n))).hom :=
  AlgebraicGeometry.Grassmannian.pullbackUniversalKernelIso_hom_kernelι g P h

/-- The universal kernel is finite locally free of rank `n - k`. -/
theorem sheafHasRank_universalKernel (R : CommRingCat.{u}) (k n : ℕ) :
    SheafHasRank (universalKernel R k n) (n - k) :=
  AlgebraicGeometry.Grassmannian.sheafHasRank_universalKernel R k n

/-- Reindexing commutes with pullback. -/
theorem ofFree_pullback {X Y : Scheme.{u}} {I : Type u} {k n : ℕ} (f : X ⟶ Y)
    (e : I ≃ ULift.{u} (Fin n)) {Q : Y.Modules} (π : SheafOfModules.free I ⟶ Q) [Epi π]
    (hQ : SheafHasRank Q k) :
    (LocallyFreeQuotient.ofFree e π hQ).pullback f =
      @LocallyFreeQuotient.ofFree X I k n e _
        ((pullbackFreeIso f I).inv ≫ (Scheme.Modules.pullback f).map π)
        (LocallyFreeQuotient.epi_pullbackFreeIso_inv_comp f π) (sheafHasRank_pullback f hQ) :=
  LocallyFreeQuotient.ofFree_pullback f e π hQ

/-- The Grassmannian classifies rank-`k` locally free quotients of `free I`. -/
theorem existsUnique_isoUnder_ofFree (R : CommRingCat.{u}) {I : Type u} {k n : ℕ}
    (e : I ≃ ULift.{u} (Fin n)) {T : Over (Spec R)} {Q : T.left.Modules}
    (π : SheafOfModules.free I ⟶ Q) [Epi π] (hQ : SheafHasRank Q k) :
    ∃! g : T ⟶ schemeOver R k n, ∃ i : ((universalQuotientRep R k n).pullback g.left).obj ≅ Q,
      ((universalQuotientRep R k n).pullback g.left).toFree e ≫ i.hom = π :=
  AlgebraicGeometry.Grassmannian.existsUnique_isoUnder_ofFree e π hQ

/-- Over a Noetherian ring the Grassmannian is Noetherian. -/
theorem isNoetherian (R : CommRingCat.{u}) [IsNoetherianRing R] (k n : ℕ) :
    IsNoetherian (schemeOver R k n).left :=
  inferInstance

/-- The structure morphism of the Grassmannian is quasi-compact and locally of finite type. -/
theorem quasiCompact_locallyOfFiniteType (R : CommRingCat.{u}) (k n : ℕ) :
    QuasiCompact (schemeOver R k n).hom ∧ LocallyOfFiniteType (schemeOver R k n).hom :=
  ⟨inferInstance, inferInstance⟩

/-- info: 'AglibTest.GrassmannianKernel.finiteLocallyFree_X₁_of_shortExact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianKernel.finiteLocallyFree_X₁_of_shortExact

/-- info: 'AglibTest.GrassmannianKernel.sheafRank_X₂_eq_add_of_shortExact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianKernel.sheafRank_X₂_eq_add_of_shortExact

/-- info: 'AglibTest.GrassmannianKernel.sheafHasRank_kernel' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianKernel.sheafHasRank_kernel

/-- info: 'AglibTest.GrassmannianKernel.shortExact' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianKernel.shortExact

/-- info: 'AglibTest.GrassmannianKernel.pullbackKernelIso_hom_kernelι' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianKernel.pullbackKernelIso_hom_kernelι

/-- info: 'AglibTest.GrassmannianKernel.pullbackUniversalKernelIso_hom_kernelι' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianKernel.pullbackUniversalKernelIso_hom_kernelι

/-- info: 'AglibTest.GrassmannianKernel.sheafHasRank_universalKernel' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianKernel.sheafHasRank_universalKernel

/-- info: 'AglibTest.GrassmannianKernel.ofFree_pullback' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianKernel.ofFree_pullback

/-- info: 'AglibTest.GrassmannianKernel.existsUnique_isoUnder_ofFree' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianKernel.existsUnique_isoUnder_ofFree

/-- info: 'AglibTest.GrassmannianKernel.isNoetherian' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianKernel.isNoetherian

/-- info: 'AglibTest.GrassmannianKernel.quasiCompact_locallyOfFiniteType' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianKernel.quasiCompact_locallyOfFiniteType

/-- info: 'AlgebraicGeometry.Grassmannian.LocallyFreeQuotient.exists_local_splitting'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Grassmannian.LocallyFreeQuotient.exists_local_splitting

/-- info: 'AlgebraicGeometry.Grassmannian.LocallyFreeQuotient.rank_le_of_nonempty'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Grassmannian.LocallyFreeQuotient.rank_le_of_nonempty

/-- info: 'AlgebraicGeometry.Grassmannian.LocallyFreeQuotient.IsoUnder.kernelIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Grassmannian.LocallyFreeQuotient.IsoUnder.kernelIso

/-- info: 'AlgebraicGeometry.Grassmannian.LocallyFreeQuotient.isoUnderOfFree' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Grassmannian.LocallyFreeQuotient.isoUnderOfFree

/-- info: 'AlgebraicGeometry.Grassmannian.LocallyFreeQuotient.ofFreeKernelIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Grassmannian.LocallyFreeQuotient.ofFreeKernelIso

/-- info: 'AlgebraicGeometry.Grassmannian.classifyingMap' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Grassmannian.classifyingMap

/-- info: 'AlgebraicGeometry.Grassmannian.classifyingMap_pullback' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Grassmannian.classifyingMap_pullback

/-- info: 'AlgebraicGeometry.Grassmannian.classifyingMap_eq_classifyingMap_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Grassmannian.classifyingMap_eq_classifyingMap_iff

/-- info: 'AlgebraicGeometry.Grassmannian.pullbackUniversalKernelIsoOfFree' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Grassmannian.pullbackUniversalKernelIsoOfFree

/-- info: 'AlgebraicGeometry.Grassmannian.pullbackUniversalKernelIsoOfFree_hom_ι' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Grassmannian.pullbackUniversalKernelIsoOfFree_hom_ι

end AglibTest.GrassmannianKernel
