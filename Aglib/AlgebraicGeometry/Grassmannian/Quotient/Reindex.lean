/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.Quotient.UniversalKernel

/-!
# Quotients of a free sheaf with an arbitrary finite basis

Let `I : Type u` and `e : I ≃ ULift (Fin n)`. The free sheaf `SheafOfModules.free I` is identified
with `O_X^n = freeSheaf X n` by `freeReindexIso X e`, whose underlying map is Mathlib's
`SheafOfModules.freeMap e`. This identification commutes with pullback
(`pullback_map_freeReindexIso_hom`, from Mathlib's `pullbackObjFreeIso_hom_naturality`).

A rank-`k` locally free quotient `π : free I ⟶ Q` (an epimorphism with `SheafHasRank Q k`) becomes
a `LocallyFreeQuotient X k n` by precomposition with the inverse identification
(`LocallyFreeQuotient.ofFree e π hQ`). This is a bijection on quotients under the free sheaf:
`LocallyFreeQuotient.toFree` is its inverse (`ofFree_toFree`, `toFree_ofFree`), and isomorphisms
under `free I` are the same as isomorphisms under `O^n` (`isoUnderOfFree`). It commutes with
pullback on the nose: the pullback of `ofFree e π hQ` along `f` is `ofFree e` of the pullback
`(pullbackFreeIso f I).inv ≫ f^* π` (`ofFree_pullback`). Hence the Grassmannian
`schemeOver R k n` classifies rank-`k` locally free quotients of `free I` on schemes over `Spec R`:
for each such quotient there is exactly one map `g` to the Grassmannian along which the universal
quotient pulls back to it, under `free I` (`existsUnique_isoUnder_ofFree`), and the universal
kernel pulls back along `g` to the kernel of `ofFree e π hQ` in `O_T^n`
(`pullbackUniversalKernelIsoOfFree`). That kernel is the kernel of `π` in `free I`
(`ofFreeKernelιIsKernel`, `ofFreeKernelIso`); under these identifications its inclusion into
`free I` is the pullback of the universal kernel included into `free I`, `universalKernelιFree`
(`pullbackUniversalKernelIsoOfFree_hom_ι`).

Source: Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 26:
the quotient `π_{T*} E_T(r) → π_{T*} F(r)`, with `π_* E(r) = W ⊗ Sym^r V`, is a point of
`Grass(W ⊗ Sym^r V, Φ(r))`; here the free module of rank `n` is given with an arbitrary finite
basis `I`. Encoded subset: free sheaves `SheafOfModules.free I` with `I ≃ ULift (Fin n)`, on all
schemes (the classification over `Spec R`), all `k` and `n`. Convention: `k` is the rank of the
quotient. The classification uses `quotFunctorRepresentableBy` and so the premise
`BaseChangeMkQFormula`, supplied by `Aglib.RingTheory.Grassmannian.BaseChangeFormula`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Grassmannian

open Scheme.Modules

variable {X Y : Scheme.{u}} {I J : Type u}

/-- The isomorphism `free I ≅ free J` of free module sheaves induced by a bijection `I ≃ J`; its
underlying map is Mathlib's `SheafOfModules.freeMap e`. -/
def freeReindexIso (X : Scheme.{u}) (e : I ≃ J) :
    SheafOfModules.free (R := X.ringCatSheaf) I ≅ SheafOfModules.free J where
  hom := SheafOfModules.freeMap e
  inv := SheafOfModules.freeMap e.symm
  hom_inv_id := Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan I) _ _ (fun i ↦ by
    rw [SheafOfModules.freeCofan_inj, SheafOfModules.ιFree_freeMap_assoc,
      SheafOfModules.ιFree_freeMap, Equiv.symm_apply_apply]
    exact (Category.comp_id _).symm)
  inv_hom_id := Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan J) _ _ (fun j ↦ by
    rw [SheafOfModules.freeCofan_inj, SheafOfModules.ιFree_freeMap_assoc,
      SheafOfModules.ιFree_freeMap, Equiv.apply_symm_apply]
    exact (Category.comp_id _).symm)

theorem freeReindexIso_hom (X : Scheme.{u}) (e : I ≃ J) :
    (freeReindexIso X e).hom = SheafOfModules.freeMap (R := X.ringCatSheaf) e := rfl

theorem freeReindexIso_inv (X : Scheme.{u}) (e : I ≃ J) :
    (freeReindexIso X e).inv = SheafOfModules.freeMap (R := X.ringCatSheaf) e.symm := rfl

/-- Reindexing a free sheaf commutes with pullback. -/
@[reassoc]
theorem pullback_map_freeReindexIso_hom (f : X ⟶ Y) (e : I ≃ J) :
    (Scheme.Modules.pullback f).map (freeReindexIso Y e).hom ≫ (pullbackFreeIso f J).hom =
      (pullbackFreeIso f I).hom ≫ (freeReindexIso X e).hom := by
  rw [freeReindexIso_hom, freeReindexIso_hom]
  exact SheafOfModules.pullbackObjFreeIso_hom_naturality f.toRingCatSheafHom e

/-- Reindexing a free sheaf commutes with pullback (inverse form). -/
@[reassoc]
theorem pullbackFreeIso_inv_freeReindexIso_inv (f : X ⟶ Y) (e : I ≃ J) :
    (pullbackFreeIso f J).inv ≫ (Scheme.Modules.pullback f).map (freeReindexIso Y e).inv =
      (freeReindexIso X e).inv ≫ (pullbackFreeIso f I).inv := by
  rw [CategoryTheory.Iso.inv_comp_eq, ← Category.assoc, CategoryTheory.Iso.eq_comp_inv]
  exact pullback_map_freeReindexIso_hom f e.symm

/-- Reindexing a free sheaf commutes with pullback (form with the inverse reindexing). -/
@[reassoc]
theorem pullback_map_freeReindexIso_inv (f : X ⟶ Y) (e : I ≃ J) :
    (Scheme.Modules.pullback f).map (freeReindexIso Y e).inv ≫ (pullbackFreeIso f I).hom =
      (pullbackFreeIso f J).hom ≫ (freeReindexIso X e).inv :=
  pullback_map_freeReindexIso_hom f e.symm

namespace LocallyFreeQuotient

variable {k n : ℕ}

/-- A rank-`k` locally free quotient `π : free I ⟶ Q`, as a quotient of `O_X^n` through
`e : I ≃ ULift (Fin n)`: its quotient map is `(freeReindexIso X e).inv ≫ π`. -/
def ofFree (e : I ≃ ULift.{u} (Fin n)) {Q : X.Modules} (π : SheafOfModules.free I ⟶ Q) [Epi π]
    (hQ : SheafHasRank Q k) : LocallyFreeQuotient X k n where
  obj := Q
  π := (freeReindexIso X e).inv ≫ π
  epi_π := epi_comp _ _
  hasRank := hQ

theorem ofFree_obj (e : I ≃ ULift.{u} (Fin n)) {Q : X.Modules} (π : SheafOfModules.free I ⟶ Q)
    [Epi π] (hQ : SheafHasRank Q k) : (ofFree e π hQ).obj = Q := rfl

theorem ofFree_π (e : I ≃ ULift.{u} (Fin n)) {Q : X.Modules} (π : SheafOfModules.free I ⟶ Q)
    [Epi π] (hQ : SheafHasRank Q k) : (ofFree e π hQ).π = (freeReindexIso X e).inv ≫ π := rfl

/-- The quotient map of a quotient of `O_X^n` as a quotient of `free I`, through
`e : I ≃ ULift (Fin n)`. -/
def toFree (e : I ≃ ULift.{u} (Fin n)) (q : LocallyFreeQuotient X k n) :
    SheafOfModules.free I ⟶ q.obj :=
  (freeReindexIso X e).hom ≫ q.π

instance epi_toFree (e : I ≃ ULift.{u} (Fin n)) (q : LocallyFreeQuotient X k n) :
    Epi (q.toFree e) :=
  have := q.epi_π
  epi_comp _ _

/-- The pulled back quotient map `(pullbackFreeIso f I).inv ≫ f^* π` is an epimorphism. -/
theorem epi_pullbackFreeIso_inv_comp (f : X ⟶ Y) {Q : Y.Modules}
    (π : SheafOfModules.free I ⟶ Q) [Epi π] :
    Epi ((pullbackFreeIso f I).inv ≫ (Scheme.Modules.pullback f).map π) :=
  epi_comp _ _

theorem ofFree_toFree (e : I ≃ ULift.{u} (Fin n)) (q : LocallyFreeQuotient X k n) :
    ofFree e (q.toFree e) q.hasRank = q := by
  obtain ⟨Q, π, _, hQ⟩ := q
  simp only [ofFree, toFree, CategoryTheory.Iso.inv_hom_id_assoc]

theorem toFree_ofFree (e : I ≃ ULift.{u} (Fin n)) {Q : X.Modules} (π : SheafOfModules.free I ⟶ Q)
    [Epi π] (hQ : SheafHasRank Q k) : (ofFree e π hQ).toFree e = π := by
  simp only [toFree, ofFree, CategoryTheory.Iso.hom_inv_id_assoc]

/-- An isomorphism of quotients of `free I` (an isomorphism of the quotient sheaves compatible with
the quotient maps) is an isomorphism of the corresponding quotients of `O_X^n`. -/
def isoUnderOfFree (e : I ≃ ULift.{u} (Fin n)) {Q Q' : X.Modules}
    {π : SheafOfModules.free I ⟶ Q} {π' : SheafOfModules.free I ⟶ Q'} [Epi π] [Epi π']
    (hQ : SheafHasRank Q k) (hQ' : SheafHasRank Q' k) (i : Q ≅ Q') (hi : π ≫ i.hom = π') :
    IsoUnder (ofFree e π hQ) (ofFree e π' hQ') where
  iso := i
  comm := by rw [ofFree_π, ofFree_π, Category.assoc, hi]

/-- An isomorphism of the corresponding quotients of `O_X^n` is compatible with the quotient maps
from `free I`. -/
theorem IsoUnder.toFree_comm (e : I ≃ ULift.{u} (Fin n)) {P Q : LocallyFreeQuotient X k n}
    (i : IsoUnder P Q) : P.toFree e ≫ i.iso.hom = Q.toFree e := by
  rw [toFree, toFree, Category.assoc, i.comm]

/-- **Reindexing commutes with pullback.** The pullback of `ofFree e π hQ` along `f` is `ofFree e`
of the pulled back quotient `(pullbackFreeIso f I).inv ≫ f^* π`. -/
theorem ofFree_pullback (f : X ⟶ Y) (e : I ≃ ULift.{u} (Fin n)) {Q : Y.Modules}
    (π : SheafOfModules.free I ⟶ Q) [Epi π] (hQ : SheafHasRank Q k) :
    (ofFree e π hQ).pullback f =
      @ofFree X I k n e _ ((pullbackFreeIso f I).inv ≫ (Scheme.Modules.pullback f).map π)
        (epi_pullbackFreeIso_inv_comp f π) (sheafHasRank_pullback f hQ) := by
  have h : (pullbackFreeIso f (ULift.{u} (Fin n))).inv ≫
      (Scheme.Modules.pullback f).map ((freeReindexIso Y e).inv ≫ π) =
      (freeReindexIso X e).inv ≫ (pullbackFreeIso f I).inv ≫ (Scheme.Modules.pullback f).map π := by
    rw [CategoryTheory.Functor.map_comp, pullbackFreeIso_inv_freeReindexIso_inv_assoc]
  simp only [LocallyFreeQuotient.pullback, ofFree]
  congr 1

/-- **The kernel of `π` inside `free I`.** The inclusion of the kernel of `ofFree e π hQ` into
`O_X^n`, followed by `(freeReindexIso X e).inv : O_X^n ≅ free I`, is a kernel of `π`. -/
def ofFreeKernelιIsKernel (e : I ≃ ULift.{u} (Fin n)) {Q : X.Modules}
    (π : SheafOfModules.free I ⟶ Q) [Epi π] (hQ : SheafHasRank Q k) :
    IsLimit (KernelFork.ofι (f := π) ((ofFree e π hQ).kernelι ≫ (freeReindexIso X e).inv)
      (by rw [Category.assoc]; exact (ofFree e π hQ).kernelι_π)) :=
  KernelFork.isLimitOfIsLimitOfIff (ofFree e π hQ).kernelIsKernel π (freeReindexIso X e).symm
    (fun _ _ ↦ Iff.rfl)

/-- The kernel of `ofFree e π hQ` (in `O_X^n`) is the kernel of `π` (in `free I`). -/
def ofFreeKernelIso (e : I ≃ ULift.{u} (Fin n)) {Q : X.Modules}
    (π : SheafOfModules.free I ⟶ Q) [Epi π] (hQ : SheafHasRank Q k) :
    (ofFree e π hQ).kernel ≅ Limits.kernel π :=
  IsLimit.conePointUniqueUpToIso (ofFreeKernelιIsKernel e π hQ) (limit.isLimit _)

@[reassoc (attr := simp)]
theorem ofFreeKernelIso_hom_ι (e : I ≃ ULift.{u} (Fin n)) {Q : X.Modules}
    (π : SheafOfModules.free I ⟶ Q) [Epi π] (hQ : SheafHasRank Q k) :
    (ofFreeKernelIso e π hQ).hom ≫ Limits.kernel.ι π =
      (ofFree e π hQ).kernelι ≫ (freeReindexIso X e).inv :=
  IsLimit.conePointUniqueUpToIso_hom_comp (ofFreeKernelιIsKernel e π hQ) (limit.isLimit _)
    WalkingParallelPair.zero

end LocallyFreeQuotient

open LocallyFreeQuotient

variable {R : CommRingCat.{u}} {k n : ℕ}
variable [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]

/-- **The Grassmannian classifies quotients of `O^n`.** For a rank-`k` locally free quotient `P` of
`O_T^n`, the classifying map is the unique map to the Grassmannian along which the universal
quotient pulls back to `P` under `O_T^n`. -/
theorem existsUnique_isoUnder_pullback_universalQuotientRep {T : Over (Spec R)}
    (P : LocallyFreeQuotient T.left k n) :
    ∃! g : T ⟶ schemeOver R k n,
      Nonempty (IsoUnder ((universalQuotientRep R k n).pullback g.left) P) := by
  refine ⟨classifyingMap P, ⟨isoUnderOfHomEquiv _ P (homEquiv_classifyingMap P)⟩, ?_⟩
  rintro g ⟨i⟩
  apply (quotFunctorRepresentableBy R k n).homEquiv.injective
  rw [homEquiv_classifyingMap, ← mk_pullback_universalQuotientRep]
  exact Quotient.sound ⟨i⟩

/-- **The Grassmannian classifies quotients of `free I`.** For `e : I ≃ ULift (Fin n)` and a
rank-`k` locally free quotient `π : free I ⟶ Q` on a scheme `T` over `Spec R`, there is exactly one
map `g` to the Grassmannian along which the universal quotient, reindexed by `e`, pulls back to `π`
under `free I`: an isomorphism `g^* Q_univ ≅ Q` carrying `toFree e` of the pulled back universal
quotient to `π`. -/
theorem existsUnique_isoUnder_ofFree (e : I ≃ ULift.{u} (Fin n)) {T : Over (Spec R)}
    {Q : T.left.Modules} (π : SheafOfModules.free I ⟶ Q) [Epi π] (hQ : SheafHasRank Q k) :
    ∃! g : T ⟶ schemeOver R k n, ∃ i : ((universalQuotientRep R k n).pullback g.left).obj ≅ Q,
      ((universalQuotientRep R k n).pullback g.left).toFree e ≫ i.hom = π := by
  obtain ⟨g, ⟨i⟩, hg⟩ := existsUnique_isoUnder_pullback_universalQuotientRep (ofFree e π hQ)
  refine ⟨g, ⟨i.iso, ?_⟩, fun g' ⟨i', hi'⟩ ↦ hg g' ⟨⟨i', ?_⟩⟩⟩
  · rw [IsoUnder.toFree_comm e i, toFree_ofFree]
  · change ((universalQuotientRep R k n).pullback g'.left).π ≫ i'.hom =
      (freeReindexIso T.left e).inv ≫ π
    rw [← hi', toFree, Category.assoc, CategoryTheory.Iso.inv_hom_id_assoc]

/-- The pullback of the universal kernel along the classifying map of a quotient `π` of `free I`
is the kernel of the corresponding quotient of `O_T^n`. -/
def pullbackUniversalKernelIsoOfFree (e : I ≃ ULift.{u} (Fin n)) {T : Over (Spec R)}
    {Q : T.left.Modules} (π : SheafOfModules.free I ⟶ Q) [Epi π] (hQ : SheafHasRank Q k) :
    (Scheme.Modules.pullback (classifyingMap (ofFree e π hQ)).left).obj (universalKernel R k n) ≅
      (ofFree e π hQ).kernel :=
  pullbackUniversalKernelIsoOfClassifying (ofFree e π hQ)

variable (R k n) in
/-- The universal kernel included into `free I` through `e : I ≃ ULift (Fin n)`. -/
def universalKernelιFree (e : I ≃ ULift.{u} (Fin n)) :
    universalKernel R k n ⟶ SheafOfModules.free I :=
  universalKernelι R k n ≫ (freeReindexIso (schemeOver R k n).left e).inv

/-- **The universal kernel pulls back to the kernel of `π` inside `free I`.** Under
`pullbackUniversalKernelIsoOfFree` and `ofFreeKernelIso`, the inclusion of the kernel of `π` into
`free I` is the pullback of `universalKernelιFree` along the classifying map, followed by
`pullbackFreeIso`. -/
theorem pullbackUniversalKernelIsoOfFree_hom_ι (e : I ≃ ULift.{u} (Fin n)) {T : Over (Spec R)}
    {Q : T.left.Modules} (π : SheafOfModules.free I ⟶ Q) [Epi π] (hQ : SheafHasRank Q k) :
    (pullbackUniversalKernelIsoOfFree e π hQ ≪≫ ofFreeKernelIso e π hQ).hom ≫
        Limits.kernel.ι π =
      (Scheme.Modules.pullback (classifyingMap (ofFree e π hQ)).left).map
          (universalKernelιFree R k n e) ≫
        (pullbackFreeIso (classifyingMap (ofFree e π hQ)).left I).hom := by
  simp only [pullbackUniversalKernelIsoOfFree, pullbackUniversalKernelIsoOfClassifying,
    CategoryTheory.Iso.trans_hom, Category.assoc, ofFreeKernelIso_hom_ι,
    pullbackUniversalKernelIso_hom_kernelι_assoc, universalKernelιFree,
    CategoryTheory.Functor.map_comp, pullback_map_freeReindexIso_inv]

end AlgebraicGeometry.Grassmannian
