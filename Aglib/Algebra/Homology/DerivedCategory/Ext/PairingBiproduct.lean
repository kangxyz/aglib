/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.ZMod
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas

/-!
# Original trace pairings on finite coefficient biproducts

The original exact-functor Yoneda pairing is the sum of its component pairings
under the native covariant and contravariant Ext decompositions. The same
whole equation holds after the actual trace functional. Component perfectness
therefore gives perfectness of the original pairing, including the empty family.
Coefficient isomorphisms retain the same pairing and both original dual maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u v u' v' w w' t

/-- An additive functor takes the actual finite bilimit bicone to its
actual image bilimit bicone, without choosing another biproduct. -/
def CategoryTheory.Functor.mapFiniteBiconeIsBilimit
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (L : C ⥤ D) [L.Additive] {I : Type*} [Fintype I]
    {F : I → C} {b : Bicone F} (hb : b.IsBilimit) : (L.mapBicone b).IsBilimit := by
  refine isBilimitOfTotal _ ?_
  change (∑ i, L.map (b.π i) ≫ L.map (b.ι i)) = 𝟙 (L.obj b.pt)
  simp_rw [← L.map_comp]
  rw [← L.map_sum, IsBilimit.total hb, L.map_id]

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (A : D)

/-- The actual coefficient biproduct pairing is the sum of the original
component pairings, with covariant projections and contravariant inclusions. -/
theorem extPairing_biproduct {I : Type*} [Fintype I] {F : I → C} {b : Bicone F}
    (hb : b.IsBilimit) (G : C) {r s t : ℕ} (h : r + s = t)
    (x : Ext.{w'} A (L.obj b.pt) r) (y : Ext.{w} b.pt G s) :
    extPairing L A x y h = ∑ i,
      extPairing L A (x.comp (Ext.mk₀ (L.map (b.π i))) (add_zero r))
        ((Ext.mk₀ (b.ι i)).comp y (zero_add s)) h := by
  let E := Ext.addEquivBiproduct A (mapFiniteBiconeIsBilimit L hb) r
  have hx : (∑ i, (x.comp (Ext.mk₀ (L.map (b.π i))) (add_zero r)).comp
      (Ext.mk₀ (L.map (b.ι i))) (add_zero r)) = x := E.symm_apply_apply x
  calc
    _ = extPairing L A (∑ i,
        (x.comp (Ext.mk₀ (L.map (b.π i))) (add_zero r)).comp
          (Ext.mk₀ (L.map (b.ι i))) (add_zero r)) y h :=
      congrArg (fun z => extPairing L A z y h) hx.symm
    _ = ∑ i, extPairing L A
        ((x.comp (Ext.mk₀ (L.map (b.π i))) (add_zero r)).comp
          (Ext.mk₀ (L.map (b.ι i))) (add_zero r)) y h :=
      _root_.map_sum ((extPairingHom L A b.pt G r s t h).flip y) _ _
    _ = _ := Finset.sum_congr rfl (fun i _ => extPairing_naturality (b.ι i) _ y h)

/-- Whole biadditive-map decomposition of the original coefficient pairing. -/
theorem extPairingHom_biproduct {I : Type*} [Fintype I] {F : I → C} {b : Bicone F}
    (hb : b.IsBilimit) (G : C) (r s t : ℕ) (h : r + s = t) :
    extPairingHom L A b.pt G r s t h = ∑ i,
      ((extPairingHom L A (F i) G r s t h).comp
        ((Ext.mk₀ (L.map (b.π i))).postcomp A (add_zero r))).compl₂
          ((Ext.mk₀ (b.ι i)).precomp G (zero_add s)) := by
  ext x y
  simpa only [AddMonoidHom.finsetSum_apply, AddMonoidHom.compl₂_apply,
    AddMonoidHom.comp_apply, extPairingHom_apply_apply,
    Ext.postcomp, Ext.precomp, AddMonoidHom.flip_apply, Ext.bilinearComp_apply_apply] using
      extPairing_biproduct L A hb G h x y

/-- The same whole SUM law retains any actual additive trace functional. -/
theorem extPairingHom_compr₂_biproduct {I : Type*} [Fintype I]
    {F : I → C} {b : Bicone F} (hb : b.IsBilimit) (G : C)
    (r s t : ℕ) (h : r + s = t) {T : Type*} [AddCommMonoid T]
    (τ : Ext.{w'} A (L.obj G) t →+ T) :
    (extPairingHom L A b.pt G r s t h).compr₂ τ = ∑ i,
      (((extPairingHom L A (F i) G r s t h).compr₂ τ).comp
        ((Ext.mk₀ (L.map (b.π i))).postcomp A (add_zero r))).compl₂
          ((Ext.mk₀ (b.ι i)).precomp G (zero_add s)) := by
  ext x y
  simp only [AddMonoidHom.finsetSum_apply, AddMonoidHom.compl₂_apply,
    AddMonoidHom.comp_apply, AddMonoidHom.compr₂_apply, extPairingHom_apply_apply,
    Ext.postcomp, Ext.precomp, AddMonoidHom.flip_apply, Ext.bilinearComp_apply_apply]
  rw [extPairing_biproduct L A hb G h, _root_.map_sum]

end CategoryTheory.Functor

namespace LinearMap

variable {R : Type*} [CommSemiring R] {I : Type*} [Fintype I]
    {M N : I → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (N i)]
    [∀ i, Module R (M i)] [∀ i, Module R (N i)]

/-- The finite sum of component pairings on the original product modules. -/
def finitePiPairing (B : ∀ i, M i →ₗ[R] N i →ₗ[R] R) :
    (∀ i, M i) →ₗ[R] (∀ i, N i) →ₗ[R] R := by
  classical
  exact (LinearMap.lsum R N R).toLinearMap.comp
    (LinearMap.pi (fun i => (B i).comp (LinearMap.proj i)))

@[simp]
theorem finitePiPairing_apply (B : ∀ i, M i →ₗ[R] N i →ₗ[R] R)
    (x : ∀ i, M i) (y : ∀ i, N i) :
    finitePiPairing B x y = ∑ i, B i (x i) (y i) := by
  classical
  simp [finitePiPairing, LinearMap.lsum_apply]

/-- Flipping the whole finite-product pairing flips its original components. -/
theorem finitePiPairing_flip (B : ∀ i, M i →ₗ[R] N i →ₗ[R] R) :
    (finitePiPairing B).flip = finitePiPairing (fun i => (B i).flip) := by
  ext x y
  simp only [LinearMap.flip_apply, finitePiPairing_apply]

end LinearMap

/-- An original additive equivalence is linear for already selected ZMod actions. -/
def AddEquiv.toZModLinearEquiv (n : ℕ) {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod n) M] [Module (ZMod n) N] (e : M ≃+ N) : M ≃ₗ[ZMod n] N :=
  { e with map_smul' := fun a x => ZMod.map_smul e a x }

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The native contravariant finite-biproduct Ext decomposition, linear for
its already selected ZMod actions. No action is transported. -/
def biproductZModLinearEquiv (n : ℕ) {I : Type*} [Fintype I] {F : I → C}
    {b : Bicone F} (hb : b.IsBilimit) (G : C) (s : ℕ)
    [Module (ZMod n) (Ext.{w} b.pt G s)] [∀ i, Module (ZMod n) (Ext.{w} (F i) G s)] :
    Ext.{w} b.pt G s ≃ₗ[ZMod n] ∀ i, Ext.{w} (F i) G s :=
  AddEquiv.toZModLinearEquiv n (biproductAddEquiv hb G s)

@[simp]
theorem biproductZModLinearEquiv_apply (n : ℕ) {I : Type*} [Fintype I] {F : I → C}
    {b : Bicone F} (hb : b.IsBilimit) (G : C) (s : ℕ)
    [Module (ZMod n) (Ext.{w} b.pt G s)] [∀ i, Module (ZMod n) (Ext.{w} (F i) G s)]
    (y : Ext.{w} b.pt G s) (i : I) :
    biproductZModLinearEquiv n hb G s y i = (mk₀ (b.ι i)).comp y (zero_add s) := rfl

/-- An actual coefficient isomorphism gives the original contravariant Ext
linear equivalence without a linear-category instance. -/
def precompZModLinearEquiv (n : ℕ) {F F' : C} (e : F ≅ F') (G : C) (s : ℕ)
    [Module (ZMod n) (Ext.{w} F' G s)] [Module (ZMod n) (Ext.{w} F G s)] :
    Ext.{w} F' G s ≃ₗ[ZMod n] Ext.{w} F G s :=
  AddEquiv.toZModLinearEquiv n (((extFunctor s).mapIso e.op).app G).addCommGroupIsoToAddEquiv

@[simp]
theorem precompZModLinearEquiv_apply (n : ℕ) {F F' : C} (e : F ≅ F') (G : C) (s : ℕ)
    [Module (ZMod n) (Ext.{w} F' G s)] [Module (ZMod n) (Ext.{w} F G s)]
    (y : Ext.{w} F' G s) :
    precompZModLinearEquiv n e G s y = (mk₀ e.hom).comp y (zero_add s) := rfl

/-- An actual coefficient isomorphism gives the original covariant Ext
linear equivalence without a linear-category instance. -/
def postcompZModLinearEquiv (n : ℕ) {F F' : C} (e : F ≅ F') (A : C) (r : ℕ)
    [Module (ZMod n) (Ext.{w} A F r)] [Module (ZMod n) (Ext.{w} A F' r)] :
    Ext.{w} A F r ≃ₗ[ZMod n] Ext.{w} A F' r :=
  AddEquiv.toZModLinearEquiv n ((extFunctorObj A r).mapIso e).addCommGroupIsoToAddEquiv

@[simp]
theorem postcompZModLinearEquiv_apply (n : ℕ) {F F' : C} (e : F ≅ F') (A : C) (r : ℕ)
    [Module (ZMod n) (Ext.{w} A F r)] [Module (ZMod n) (Ext.{w} A F' r)]
    (x : Ext.{w} A F r) :
    postcompZModLinearEquiv n e A r x = x.comp (mk₀ e.hom) (add_zero r) := rfl

end CategoryTheory.Abelian.Ext

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (A : D) (n : ℕ)

/-- The native covariant Ext decomposition of the actual image bicone,
linear for the original ZMod actions. -/
def extPairingBiproductLeftEquiv {I : Type*} [Fintype I] {F : I → C} {b : Bicone F}
    (hb : b.IsBilimit) (r : ℕ)
    [Module (ZMod n) (Ext.{w'} A (L.obj b.pt) r)]
    [∀ i, Module (ZMod n) (Ext.{w'} A (L.obj (F i)) r)] :
    Ext.{w'} A (L.obj b.pt) r ≃ₗ[ZMod n] ∀ i, Ext.{w'} A (L.obj (F i)) r :=
  AddEquiv.toZModLinearEquiv n (Ext.addEquivBiproduct A (mapFiniteBiconeIsBilimit L hb) r)

omit [HasExt.{w} C] [PreservesFiniteLimits L] [PreservesFiniteColimits L] in
@[simp]
theorem extPairingBiproductLeftEquiv_apply {I : Type*} [Fintype I] {F : I → C}
    {b : Bicone F} (hb : b.IsBilimit) (r : ℕ)
    [Module (ZMod n) (Ext.{w'} A (L.obj b.pt) r)]
    [∀ i, Module (ZMod n) (Ext.{w'} A (L.obj (F i)) r)]
    (x : Ext.{w'} A (L.obj b.pt) r) (i : I) :
    extPairingBiproductLeftEquiv L A n hb r x i =
      x.comp (Ext.mk₀ (L.map (b.π i))) (add_zero r) := rfl

/-- The entire original trace-composed linear pairing is the finite SUM
pairing under the two original Ext equivalences. -/
theorem extPairingLinearMap_compr₂_biproduct {I : Type*} [Fintype I]
    {F : I → C} {b : Bicone F} (hb : b.IsBilimit) (G : C)
    (r s t : ℕ) (h : r + s = t)
    [Module (ZMod n) (Ext.{w'} A (L.obj b.pt) r)]
    [∀ i, Module (ZMod n) (Ext.{w'} A (L.obj (F i)) r)]
    [Module (ZMod n) (Ext.{w} b.pt G s)]
    [∀ i, Module (ZMod n) (Ext.{w} (F i) G s)]
    [Module (ZMod n) (Ext.{w'} A (L.obj G) t)]
    (τ : Ext.{w'} A (L.obj G) t →ₗ[ZMod n] ZMod n) :
    (extPairingLinearMap L A n b.pt G r s t h).compr₂ τ =
      (LinearMap.finitePiPairing (fun i =>
        (extPairingLinearMap L A n (F i) G r s t h).compr₂ τ)).compl₁₂
          (extPairingBiproductLeftEquiv L A n hb r)
          (Ext.biproductZModLinearEquiv n hb G s) := by
  ext x y
  simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
    LinearMap.finitePiPairing_apply, LinearEquiv.coe_coe, extPairingBiproductLeftEquiv_apply,
    Ext.biproductZModLinearEquiv_apply, extPairingLinearMap_apply_apply]
  rw [extPairing_biproduct L A hb G h, _root_.map_sum]

/-- Whole naturality of the same trace-composed bilinear map in the coefficient. -/
theorem extPairingLinearMap_compr₂_naturality {F F' G : C} (u : F ⟶ F')
    (r s t : ℕ) (h : r + s = t)
    [Module (ZMod n) (Ext.{w'} A (L.obj F) r)]
    [Module (ZMod n) (Ext.{w'} A (L.obj F') r)]
    [Module (ZMod n) (Ext.{w} F G s)] [Module (ZMod n) (Ext.{w} F' G s)]
    [Module (ZMod n) (Ext.{w'} A (L.obj G) t)]
    (τ : Ext.{w'} A (L.obj G) t →ₗ[ZMod n] ZMod n) :
    ((extPairingLinearMap L A n F' G r s t h).compr₂ τ).comp
        (AddMonoidHom.toZModLinearMap n ((Ext.mk₀ (L.map u)).postcomp A (add_zero r))) =
      ((extPairingLinearMap L A n F G r s t h).compr₂ τ).compl₂
        (AddMonoidHom.toZModLinearMap n ((Ext.mk₀ u).precomp G (zero_add s))) := by
  ext x y
  exact congrArg τ (extPairing_naturality u x y h)

end CategoryTheory.Functor

namespace CategoryTheory.Limits

/-- Component identity annihilation annihilates the identity of the actual
bilimit point, including the empty family. -/
theorem Bicone.IsBilimit.nsmul_id_eq_zero
    {C : Type*} [Category* C] [Preadditive C] {I : Type*}
    {F : I → C} {b : Bicone F} (hb : b.IsBilimit) (n : ℕ)
    (hF : ∀ i, n • 𝟙 (F i) = 0) : n • 𝟙 b.pt = 0 := by
  apply hb.isLimit.hom_ext
  rintro ⟨i⟩
  change (n • 𝟙 b.pt) ≫ b.π i = (0 : b.pt ⟶ b.pt) ≫ b.π i
  simp only [Preadditive.nsmul_comp, Category.id_comp, zero_comp]
  simpa only [Preadditive.comp_nsmul, Category.comp_id, comp_zero] using
    congrArg (fun f : F i ⟶ F i => b.π i ≫ f) (hF i)

end CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (A : D) (n : ℕ)

/-- The first original curried trace map intertwines coefficient transport
with the native dual of source precomposition. -/
theorem extPairingLinearMap_compr₂_dual_naturality {F F' G : C} (u : F ⟶ F')
    (r s t : ℕ) (h : r + s = t)
    [Module (ZMod n) (Ext.{w'} A (L.obj F) r)]
    [Module (ZMod n) (Ext.{w'} A (L.obj F') r)]
    [Module (ZMod n) (Ext.{w} F G s)] [Module (ZMod n) (Ext.{w} F' G s)]
    [Module (ZMod n) (Ext.{w'} A (L.obj G) t)]
    (τ : Ext.{w'} A (L.obj G) t →ₗ[ZMod n] ZMod n) :
    ((extPairingLinearMap L A n F' G r s t h).compr₂ τ).comp
        (AddMonoidHom.toZModLinearMap n ((Ext.mk₀ (L.map u)).postcomp A (add_zero r))) =
      (AddMonoidHom.toZModLinearMap n ((Ext.mk₀ u).precomp G (zero_add s))).dualMap.comp
        ((extPairingLinearMap L A n F G r s t h).compr₂ τ) := by
  have hh := extPairingLinearMap_compr₂_naturality L A n u r s t h τ
  ext x y
  exact LinearMap.congr_fun (LinearMap.congr_fun hh x) y

/-- The transposed original trace map intertwines source precomposition
with the native dual of covariant coefficient transport. -/
theorem extPairingLinearMap_compr₂_flip_naturality {F F' G : C} (u : F ⟶ F')
    (r s t : ℕ) (h : r + s = t)
    [Module (ZMod n) (Ext.{w'} A (L.obj F) r)]
    [Module (ZMod n) (Ext.{w'} A (L.obj F') r)]
    [Module (ZMod n) (Ext.{w} F G s)] [Module (ZMod n) (Ext.{w} F' G s)]
    [Module (ZMod n) (Ext.{w'} A (L.obj G) t)]
    (τ : Ext.{w'} A (L.obj G) t →ₗ[ZMod n] ZMod n) :
    ((extPairingLinearMap L A n F G r s t h).compr₂ τ).flip.comp
        (AddMonoidHom.toZModLinearMap n ((Ext.mk₀ u).precomp G (zero_add s))) =
      (AddMonoidHom.toZModLinearMap n
        ((Ext.mk₀ (L.map u)).postcomp A (add_zero r))).dualMap.comp
          ((extPairingLinearMap L A n F' G r s t h).compr₂ τ).flip := by
  have hh := extPairingLinearMap_compr₂_naturality L A n u r s t h τ
  ext y x
  exact (LinearMap.congr_fun (LinearMap.congr_fun hh x) y).symm

/-- The whole original pairing is unchanged by an actual coefficient Iso,
using its original covariant forward map and contravariant inverse map. -/
theorem extPairingLinearMap_compr₂_iso {F F' G : C} (e : F ≅ F')
    (r s t : ℕ) (h : r + s = t)
    [Module (ZMod n) (Ext.{w'} A (L.obj F) r)]
    [Module (ZMod n) (Ext.{w'} A (L.obj F') r)]
    [Module (ZMod n) (Ext.{w} F G s)] [Module (ZMod n) (Ext.{w} F' G s)]
    [Module (ZMod n) (Ext.{w'} A (L.obj G) t)]
    (τ : Ext.{w'} A (L.obj G) t →ₗ[ZMod n] ZMod n) :
    ((extPairingLinearMap L A n F' G r s t h).compr₂ τ).compl₁₂
        (Ext.postcompZModLinearEquiv n (L.mapIso e) A r)
        (Ext.precompZModLinearEquiv n e.symm G s) =
      (extPairingLinearMap L A n F G r s t h).compr₂ τ := by
  ext x y
  simp only [LinearMap.compl₁₂_apply, LinearMap.compr₂_apply, LinearEquiv.coe_coe,
    Ext.postcompZModLinearEquiv_apply, Ext.precompZModLinearEquiv_apply,
    extPairingLinearMap_apply_apply]
  change τ (extPairing L A (x.comp (Ext.mk₀ (L.map e.hom)) (add_zero r))
      ((Ext.mk₀ e.inv).comp y (zero_add s)) h) = τ (extPairing L A x y h)
  rw [extPairing_naturality, Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]

end CategoryTheory.Functor

namespace LinearMap

variable {R : Type*} [CommSemiring R] {I : Type*} [Fintype I]
    {M N : I → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (N i)]
    [∀ i, Module R (M i)] [∀ i, Module R (N i)]

/-- Component perfectness makes the original finite-product left dual map bijective. -/
theorem finitePiPairing_bijective (B : ∀ i, M i →ₗ[R] N i →ₗ[R] R)
    (hB : ∀ i, (B i).IsPerfPair) : Function.Bijective (finitePiPairing B) := by
  classical
  let (i : I) : (B i).IsPerfPair := hB i
  let E := (LinearEquiv.piCongrRight (fun i => (B i).toPerfPair)).trans
    (LinearMap.lsum R N R)
  change Function.Bijective E
  exact E.bijective

/-- Finite sums of perfect component pairings are perfect, also for an empty index. -/
theorem finitePiPairing_isPerfPair (B : ∀ i, M i →ₗ[R] N i →ₗ[R] R)
    (hB : ∀ i, (B i).IsPerfPair) : (finitePiPairing B).IsPerfPair := by
  refine ⟨finitePiPairing_bijective B hB, ?_⟩
  rw [finitePiPairing_flip]
  exact finitePiPairing_bijective (fun i => (B i).flip) (fun i => (hB i).flip)

end LinearMap

private theorem isPerfPair_iff_of_compl₁₂
    {R : Type*} [CommSemiring R] {M N M' N' : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid M'] [AddCommMonoid N']
    [Module R M] [Module R N] [Module R M'] [Module R N']
    (E : M ≃ₗ[R] M') (H : N ≃ₗ[R] N')
    {p : M →ₗ[R] N →ₗ[R] R} {q : M' →ₗ[R] N' →ₗ[R] R}
    (hpair : q.compl₁₂ E H = p) : q.IsPerfPair ↔ p.IsPerfPair := by
  constructor
  · intro hq
    let : q.IsPerfPair := hq
    rw [← hpair]
    exact LinearMap.IsPerfPair.compl₁₂ q E H
  · intro hp
    let : p.IsPerfPair := hp
    exact LinearMap.IsPerfPair.congr p E.symm H.symm q hpair

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (A : D) (n : ℕ)

/-- Component perfectness gives perfectness of the SAME original trace pairing
at the actual finite coefficient biproduct, with its native scalar actions. -/
theorem isPerfPair_extPairingLinearMap_compr₂_biproduct {I : Type*} [Finite I]
    {F : I → C} {b : Bicone F} (hb : b.IsBilimit) (G : C)
    (r s t : ℕ) (h : r + s = t)
    [Module (ZMod n) (Ext.{w'} A (L.obj b.pt) r)]
    [∀ i, Module (ZMod n) (Ext.{w'} A (L.obj (F i)) r)]
    [Module (ZMod n) (Ext.{w} b.pt G s)]
    [∀ i, Module (ZMod n) (Ext.{w} (F i) G s)]
    [Module (ZMod n) (Ext.{w'} A (L.obj G) t)]
    (τ : Ext.{w'} A (L.obj G) t →ₗ[ZMod n] ZMod n)
    (hF : ∀ i, ((extPairingLinearMap L A n (F i) G r s t h).compr₂ τ).IsPerfPair) :
    ((extPairingLinearMap L A n b.pt G r s t h).compr₂ τ).IsPerfPair := by
  classical
  let : Fintype I := Fintype.ofFinite I
  rw [extPairingLinearMap_compr₂_biproduct L A n hb G r s t h τ]
  let B := LinearMap.finitePiPairing
    (fun i => (extPairingLinearMap L A n (F i) G r s t h).compr₂ τ)
  let : B.IsPerfPair := LinearMap.finitePiPairing_isPerfPair _ hF
  exact LinearMap.IsPerfPair.compl₁₂ B (extPairingBiproductLeftEquiv L A n hb r)
    (Ext.biproductZModLinearEquiv n hb G s)

/-- An actual coefficient Iso preserves perfectness of the same trace-composed
pairing in both directions; no finiteness or freeness is assumed. -/
theorem isPerfPair_extPairingLinearMap_compr₂_iso_iff {F F' G : C} (e : F ≅ F')
    (r s t : ℕ) (h : r + s = t)
    [Module (ZMod n) (Ext.{w'} A (L.obj F) r)]
    [Module (ZMod n) (Ext.{w'} A (L.obj F') r)]
    [Module (ZMod n) (Ext.{w} F G s)] [Module (ZMod n) (Ext.{w} F' G s)]
    [Module (ZMod n) (Ext.{w'} A (L.obj G) t)]
    (τ : Ext.{w'} A (L.obj G) t →ₗ[ZMod n] ZMod n) :
    ((extPairingLinearMap L A n F' G r s t h).compr₂ τ).IsPerfPair ↔
      ((extPairingLinearMap L A n F G r s t h).compr₂ τ).IsPerfPair := by
  let E := Ext.postcompZModLinearEquiv n (L.mapIso e) A r
  let H := Ext.precompZModLinearEquiv n e.symm G s
  have hpair := extPairingLinearMap_compr₂_iso L A n e r s t h τ
  have hh := isPerfPair_iff_of_compl₁₂ E H hpair
  exact hh

end CategoryTheory.Functor
