/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Support.Finite
public import Aglib.AlgebraicGeometry.Cohomology.Exact.Modules
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Coefficient
public import Aglib.AlgebraicGeometry.Modules.Generators.GlobalSections
public import Aglib.AlgebraicGeometry.Modules.Linear
public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact
public import Aglib.AlgebraicGeometry.Modules.Stalk.Reflection
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite-support enlargement with a coefficient-valued trace

The original Hom/H1 comparisons and their trace forward law split a short
exact row whose finite-support quotient has nonzero middle H1. For a pure
coherent middle sheaf F, a finite-support quotient of H0 dimension at least
two forces the image of the original global-section evaluation together
with the canonical inclusion to be all of F.

Finite-support vanishing and zero detection use the original additive
stalks. Coherence of the evaluation image is obtained from a finite row
spanning actual global sections. All cohomology groups and maps retain the
specified structural scalar map through moduleCohomologyFunctorOfHom.

The trace-valued Serre comparisons, purity of F, and the actual quotient
support and dimension are genuine inputs. No orientation of the supplied
coefficient line, generation premise, or splitting premise is introduced.
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology.CanonicalEnlargement

variable {X : Scheme.{u}}

/-- Finite closed support is a condition on the actual additive stalks. -/
def HasFiniteClosedSupport (M : X.Modules) : Prop :=
  ∃ (n : ℕ) (p : Fin n → X), Function.Injective p ∧
    (∀ i, IsClosed ({p i} : Set X)) ∧
    ∀ x, x ∉ Set.range p → IsZero ((stalkFunctor X x).obj M)

/-- Original higher cohomology vanishes on actual finite closed support. -/
theorem finiteSupport_positive {M : X.Modules}
    (hM : HasFiniteClosedSupport M) (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) (q + 1)) := by
  rcases hM with ⟨n, p, hp, hc, hz⟩
  exact finiteClosedSupportCohomology_positive X p hp hc (moduleAddSheaf X M) hz q

/-- The original H0 detects zero on finite closed support. -/
theorem finiteSupport_isZero_of_H0 {M : X.Modules}
    (hM : HasFiniteClosedSupport M)
    (h0 : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) 0)) :
    IsZero M := by
  classical
  rcases hM with ⟨n, p, hp, hc, hz⟩
  let e := finiteClosedSupportH0Equiv X p hp hc (moduleAddSheaf X M) hz
  let := h0
  let : Subsingleton (∀ i : Fin n, (stalkFunctor X (p i)).obj M) :=
    e.symm.injective.subsingleton
  apply (isZero_iff_stalks M).mpr
  intro x
  by_cases hx : x ∈ Set.range p
  · obtain ⟨i, rfl⟩ := hx
    let : Subsingleton ((stalkFunctor X (p i)).obj M) :=
      (Function.surjective_eval
        (β := fun j : Fin n => ((stalkFunctor X (p j)).obj M : Type u)) i).subsingleton
    exact AddCommGrpCat.isZero_of_subsingleton _
  · exact hz x hx

/-- A subobject inherits the original finite support of its target. -/
theorem finiteSupport_of_mono {M N : X.Modules} (f : M ⟶ N) [Mono f]
    (hN : HasFiniteClosedSupport N) : HasFiniteClosedSupport M := by
  rcases hN with ⟨n, p, hp, hc, hz⟩
  refine ⟨n, p, hp, hc, fun x hx => ?_⟩
  exact IsZero.of_mono ((stalkFunctor X x).map f) (hz x hx)

/-- A quotient inherits the original finite support of its source. -/
theorem finiteSupport_of_epi {M N : X.Modules} (f : M ⟶ N) [Epi f]
    (hM : HasFiniteClosedSupport M) : HasFiniteClosedSupport N := by
  rcases hM with ⟨n, p, hp, hc, hz⟩
  refine ⟨n, p, hp, hc, fun x hx => ?_⟩
  let : PreservesFiniteColimits (stalkFunctor X x) :=
    preservesFiniteColimits_of_natIso (moduleStalkForgetIso X x)
  exact IsZero.of_epi ((stalkFunctor X x).map f) (hz x hx)

/-- Factoring a map with finite cokernel through a monomorphism gives
finite cokernel at both factors. No quotient-image mono is assumed. -/
theorem finiteSupport_cokernels_of_factor
    {W B F : X.Modules} (a : W ⟶ B) (b : B ⟶ F) [Mono b]
    (h : HasFiniteClosedSupport (cokernel (a ≫ b))) :
    HasFiniteClosedSupport (cokernel a) ∧
      HasFiniteClosedSupport (cokernel b) := by
  rcases h with ⟨n, p, hp, hc, hz⟩
  have hout (x : X) (hx : x ∉ Set.range p) :
      IsZero ((stalkFunctor X x).obj (cokernel a)) ∧
        IsZero ((stalkFunctor X x).obj (cokernel b)) := by
    let P := stalkFunctor X x
    let : PreservesFiniteColimits P :=
      preservesFiniteColimits_of_natIso (moduleStalkForgetIso X x)
    have hzero : IsZero (cokernel (P.map (a ≫ b))) :=
      (hz x hx).of_iso (PreservesCokernel.iso P (a ≫ b)).symm
    let : Epi (P.map (a ≫ b)) :=
      Preadditive.epi_of_isZero_cokernel _ hzero
    have hcomp : Epi (P.map a ≫ P.map b) := by
      rw [← P.map_comp]
      infer_instance
    let := hcomp
    let : Epi (P.map b) := epi_of_epi (P.map a) (P.map b)
    let : IsIso (P.map b) := isIso_of_mono_of_epi (P.map b)
    let : Epi (P.map a) :=
      (epi_comp_iff_of_isIso (P.map a) (P.map b)).mp hcomp
    exact ⟨(isZero_cokernel_of_epi (P.map a)).of_iso (PreservesCokernel.iso P a),
      (isZero_cokernel_of_epi (P.map b)).of_iso (PreservesCokernel.iso P b)⟩
  exact ⟨⟨n, p, hp, hc, fun x hx => (hout x hx).1⟩,
    ⟨n, p, hp, hc, fun x hx => (hout x hx).2⟩⟩

/-- The actual H1 object, with the specified original scalar map. -/
abbrev H1 (k : Type u) [Field k] (α : k →+* Γ(X, ⊤)) (M : X.Modules) :=
  (moduleCohomologyFunctorOfHom X α 1).obj M

/-- The actual H0 object, with the specified original scalar map. -/
abbrev H0 (k : Type u) [Field k] (α : k →+* Γ(X, ⊤)) (M : X.Modules) :=
  (moduleCohomologyFunctorOfHom X α 0).obj M

/-- The original short exact row gives its original H1 surjection when
the original quotient has finite closed support. Scalar instances are
fixed before specializing the linear exactness theorem. -/
private theorem H1_surjective_of_finiteSupport
    (k : Type u) [Field k] (α : k →+* Γ(X, ⊤))
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hQ : HasFiniteClosedSupport S.X₃) :
    Function.Surjective ((moduleCohomologyFunctorOfHom X α 1).map S.f) := by
  let := moduleCohomologyModuleOfHom X α S.X₁ 1
  let := moduleCohomologyModuleOfHom X α S.X₂ 1
  let := moduleCohomologyModuleOfHom X α S.X₃ 1
  have hz : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₃) 1) :=
    finiteSupport_positive hQ 0
  have hg : moduleCohomologyMapOfHom X α S.g 1 = 0 := by
    apply LinearMap.ext
    intro x
    exact hz.elim _ _
  have hex := moduleCohomologyMapOfHom_exact X α S hS 1
  exact (LinearMap.surjective_iff_eq_zero_of_exact hex).mpr hg

section LinearCore

variable {k : Type u} [Field k]
    {P : Type*} [AddCommGroup P] [Module k P]
    {Q : Type*} [AddCommGroup Q] [Module k Q]

/-- A surjection from a line to a nonzero vector space is injective,
without orienting the line. -/
theorem injective_of_line_surjective (f : P →ₗ[k] Q)
    (hP : Module.finrank k P = 1) [Nontrivial Q]
    (hf : Function.Surjective f) : Function.Injective f := by
  obtain ⟨y, hy⟩ := exists_ne (0 : Q)
  obtain ⟨x, hx⟩ := hf y
  have hx0 : x ≠ 0 := by
    intro h
    apply hy
    rw [← hx, h, map_zero]
  have hk (z : P) (hz : f z = 0) : z = 0 := by
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hP hx0 z
    have hcy : c • y = 0 := by
      exact (congrArg (fun q : Q => c • q) hx.symm).trans
        ((f.map_smul c x).symm.trans ((congrArg f hc).trans hz))
    have hc0 : c = 0 := (smul_eq_zero.mp hcy).resolve_right hy
    rw [← hc, hc0, zero_smul]
  intro z z' hzz'
  apply sub_eq_zero.mp
  exact hk (z - z') (by rw [map_sub, hzz', sub_self])

end LinearCore

section TraceSplitting

variable (k : Type u) [Field k] (α : k →+* Γ(X, ⊤))
    (V : Type v) [AddCommGroup V] [Module k V]
    (hV : Module.finrank k V = 1)
    (W : X.Modules) (τ : H1 k α W ≃ₗ[k] V)

include hV

/-- Trace-normalized Hom/H1 comparisons provide a retraction of the
original sheaf map. Both comparisons remain explicit upstream inputs. -/
theorem retraction_of_H1_surjective
    (B : X.Modules) (a : W ⟶ B)
    (DB : (B ⟶ W) ≃ (H1 k α B →ₗ[k] V))
    (DW : (W ⟶ W) ≃ (H1 k α W →ₗ[k] V))
    (hDB : ∀ b x, DB b x =
      τ ((moduleCohomologyFunctorOfHom X α 1).map b x))
    (hDW : ∀ b x, DW b x =
      τ ((moduleCohomologyFunctorOfHom X α 1).map b x))
    [Nontrivial (H1 k α B)]
    (ha : Function.Surjective ((moduleCohomologyFunctorOfHom X α 1).map a)) :
    ∃ b : B ⟶ W, a ≫ b = 𝟙 W := by
  let H := moduleCohomologyFunctorOfHom X α 1
  let f : H1 k α W →ₗ[k] H1 k α B := (H.map a).hom
  have hWdim : Module.finrank k (H1 k α W) = 1 := τ.finrank_eq.trans hV
  let e := LinearEquiv.ofBijective f
    ⟨injective_of_line_surjective f hWdim ha, ha⟩
  let l : H1 k α B →ₗ[k] V := τ.toLinearMap.comp e.symm.toLinearMap
  let b : B ⟶ W := DB.symm l
  refine ⟨b, DW.injective ?_⟩
  apply LinearMap.ext
  intro x
  have he : e x = H.map a x := rfl
  have hei : e.symm (H.map a x) = x :=
    (congrArg e.symm he.symm).trans (e.symm_apply_apply x)
  have hb : τ (H.map b (H.map a x)) = τ x := by
    have hh := LinearMap.congr_fun (DB.apply_symm_apply l) (H.map a x)
    have hdb : DB b (H.map a x) = τ (H.map b (H.map a x)) :=
      hDB b (H.map a x)
    have hl : l (H.map a x) = τ (e.symm (H.map a x)) := rfl
    exact hdb.symm.trans (hh.trans (hl.trans (congrArg τ hei)))
  have hcomp : H.map (a ≫ b) x = H.map b (H.map a x) :=
    ConcreteCategory.congr_hom (H.map_comp a b) x
  have hid : H.map (𝟙 W) x = x :=
    ConcreteCategory.congr_hom (H.map_id W) x
  exact (hDW (a ≫ b) x).trans ((congrArg τ hcomp).trans
    (hb.trans ((congrArg τ hid).symm.trans (hDW (𝟙 W) x).symm)))

/-- Actual short exactness and finite support supply the H1 surjection. -/
theorem splitting_of_finiteSupport
    (B : X.Modules) (a : W ⟶ B) [Mono a]
    (hQ : HasFiniteClosedSupport (cokernel a))
    (DB : (B ⟶ W) ≃ (H1 k α B →ₗ[k] V))
    (DW : (W ⟶ W) ≃ (H1 k α W →ₗ[k] V))
    (hDB : ∀ b x, DB b x =
      τ ((moduleCohomologyFunctorOfHom X α 1).map b x))
    (hDW : ∀ b x, DW b x =
      τ ((moduleCohomologyFunctorOfHom X α 1).map b x))
    [Nontrivial (H1 k α B)] :
    Nonempty (ShortComplex.cokernelSequence a).Splitting := by
  let S := ShortComplex.cokernelSequence a
  have hS : S.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact a,
      mono_f := inferInstanceAs (Mono a) }
  have ha : Function.Surjective
      ((moduleCohomologyFunctorOfHom X α 1).map a) :=
    H1_surjective_of_finiteSupport k α S hS hQ
  obtain ⟨b, hb⟩ := retraction_of_H1_surjective k α V hV W τ B a DB DW hDB hDW ha
  exact ⟨ShortComplex.Splitting.ofExactOfRetraction S hS.exact b hb hS.epi_g⟩

end TraceSplitting

/-- The same retraction constructs a splitting of a supplied ORIGINAL
short exact row, not just of its chosen cokernel presentation. -/
theorem splitting_originalRow
    (k : Type u) [Field k] (α : k →+* Γ(X, ⊤))
    (V : Type v) [AddCommGroup V] [Module k V]
    (hV : Module.finrank k V = 1)
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hQ : HasFiniteClosedSupport S.X₃)
    (τ : H1 k α S.X₁ ≃ₗ[k] V)
    (DB : (S.X₂ ⟶ S.X₁) ≃ (H1 k α S.X₂ →ₗ[k] V))
    (DW : (S.X₁ ⟶ S.X₁) ≃ (H1 k α S.X₁ →ₗ[k] V))
    (hDB : ∀ b x, DB b x =
      τ ((moduleCohomologyFunctorOfHom X α 1).map b x))
    (hDW : ∀ b x, DW b x =
      τ ((moduleCohomologyFunctorOfHom X α 1).map b x))
    [Nontrivial (H1 k α S.X₂)] : Nonempty S.Splitting := by
  have ha : Function.Surjective
      ((moduleCohomologyFunctorOfHom X α 1).map S.f) :=
    H1_surjective_of_finiteSupport k α S hS hQ
  obtain ⟨b, hb⟩ := retraction_of_H1_surjective k α V hV S.X₁ τ
    S.X₂ S.f DB DW hDB hDW ha
  exact ⟨ShortComplex.Splitting.ofExactOfRetraction S hS.exact b hb hS.epi_g⟩

section GlobalSections

variable {A B F Q : X.Modules}

/-- Factorization of all original unit sections is surjectivity on sections. -/
theorem sections_surjective_of_unitHom_factor (b : B ⟶ F)
    (h : ∀ s : 𝟙_ X.Modules ⟶ F, ∃ t : 𝟙_ X.Modules ⟶ B, t ≫ b = s) :
    Function.Surjective (b.val.app (op ⊤)) := by
  intro x
  obtain ⟨t, ht⟩ := h ((unitHomGlobalSectionsEquiv X F).symm x)
  refine ⟨unitHomGlobalSectionsEquiv X B t, ?_⟩
  have hn : unitHomGlobalSectionsEquiv X F (t ≫ b) =
      b.val.app (op ⊤) (unitHomGlobalSectionsEquiv X B t) := rfl
  exact hn.symm.trans ((congrArg (unitHomGlobalSectionsEquiv X F) ht).trans
    ((unitHomGlobalSectionsEquiv X F).apply_symm_apply x))

/-- A map annihilating an image containing all sections is zero on sections. -/
theorem sections_map_zero_of_factor (a : A ⟶ F) (q : F ⟶ Q)
    (haq : a ≫ q = 0)
    (h : ∀ s : 𝟙_ X.Modules ⟶ F, ∃ t : 𝟙_ X.Modules ⟶ A, t ≫ a = s) :
    ∀ x, q.val.app (op ⊤) x = 0 := by
  intro x
  let s : 𝟙_ X.Modules ⟶ F := (unitHomGlobalSectionsEquiv X F).symm x
  obtain ⟨t, ht⟩ := h s
  have hs : unitHomGlobalSectionsEquiv X F s = x :=
    (unitHomGlobalSectionsEquiv X F).apply_symm_apply x
  have hcomp : s ≫ q = (0 : 𝟙_ X.Modules ⟶ Q) :=
    (congrArg (fun f : 𝟙_ X.Modules ⟶ F => f ≫ q) ht.symm).trans
      ((Category.assoc t a q).trans
        ((congrArg (fun f : A ⟶ Q => t ≫ f) haq).trans (comp_zero)))
  have hn : unitHomGlobalSectionsEquiv X Q (s ≫ q) =
      q.val.app (op ⊤) (unitHomGlobalSectionsEquiv X F s) := rfl
  let eQ : (𝟙_ X.Modules ⟶ Q) ≃+ Q.val.obj (op ⊤) :=
    unitHomGlobalSectionsAddEquiv X Q
  have hz : unitHomGlobalSectionsEquiv X Q (0 : 𝟙_ X.Modules ⟶ Q) = 0 :=
    eQ.map_zero
  exact (congrArg (fun z => q.val.app (op ⊤) z) hs).symm.trans
    (hn.symm.trans ((congrArg (unitHomGlobalSectionsEquiv X Q) hcomp).trans
      hz))

/-- Zero on sections is zero on original H0, with no new cohomology model. -/
theorem H0_map_zero_of_sections_zero (k : Type u) [Field k]
    (α : k →+* Γ(X, ⊤)) (q : F ⟶ Q)
    (hq : ∀ x, q.val.app (op ⊤) x = 0) :
    ((moduleCohomologyFunctorOfHom X α 0).map q).hom = 0 := by
  apply LinearMap.ext
  intro x
  change (moduleCohomologyFunctorOfHom X α 0).map q x = 0
  apply (Sheaf.H.equiv₀ (moduleAddSheaf X Q) isTerminalTop).injective
  have hn := Sheaf.H.equiv₀_naturality isTerminalTop
    ((SheafOfModules.toSheaf X.ringCatSheaf).map q) x
  change q.val.app (op ⊤) ((Sheaf.H.equiv₀ (moduleAddSheaf X F) isTerminalTop) x) =
    (Sheaf.H.equiv₀ (moduleAddSheaf X Q) isTerminalTop)
      ((moduleCohomologyFunctorOfHom X α 0).map q x) at hn
  exact hn.symm.trans
    ((hq ((Sheaf.H.equiv₀ (moduleAddSheaf X F) isTerminalTop) x)).trans
      ((Sheaf.H.equiv₀ (moduleAddSheaf X Q) isTerminalTop).map_zero).symm)

/-- Vanishing H1 and factorization of all sections kill the finite cokernel. -/
theorem epi_of_H1_zero_of_sections_factor
    (k : Type u) [Field k] (α : k →+* Γ(X, ⊤))
    (b : B ⟶ F) [Mono b]
    (hC : HasFiniteClosedSupport (cokernel b))
    (hB : Subsingleton (H1 k α B))
    (h : ∀ s : 𝟙_ X.Modules ⟶ F, ∃ t : 𝟙_ X.Modules ⟶ B, t ≫ b = s) :
    Epi b := by
  let S := ShortComplex.cokernelSequence b
  have hS : S.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact b,
      mono_f := inferInstanceAs (Mono b) }
  let := moduleCohomologyModuleOfHom X α S.X₃ 0
  let := moduleCohomologyModuleOfHom X α S.X₁ (0 + 1)
  have hδ : moduleCohomologyConnectingOfHom X α S hS 0 = 0 := by
    apply LinearMap.ext
    intro x
    exact hB.elim _ _
  have hsurj : Function.Surjective ((cokernel.π b).val.app (op ⊤)) :=
    surjective_of_moduleCohomologyConnectingOfHom_zero_eq_zero (X := X) α S hS hδ
  have hz := sections_map_zero_of_factor b (cokernel.π b) (cokernel.condition b) h
  have hsec (x : (cokernel b).val.obj (op ⊤)) : x = 0 := by
    obtain ⟨y, rfl⟩ := hsurj x
    exact hz y
  have h0 : Subsingleton (H0 k α (cokernel b)) := by
    refine ⟨fun x y => ?_⟩
    apply (Sheaf.H.equiv₀ (moduleAddSheaf X (cokernel b)) isTerminalTop).injective
    exact (hsec _).trans (hsec _).symm
  exact Preadditive.epi_of_isZero_cokernel b (finiteSupport_isZero_of_H0 hC h0)

end GlobalSections

section Enlargement

variable [IsLocallyNoetherian X]
    (k : Type u) [Field k] (α : k →+* Γ(X, ⊤))
    (V : Type v) [AddCommGroup V] [Module k V]
    (hV : Module.finrank k V = 1)
    (W : X.Modules) (hW : affineLocallyFiniteType X W)
    (τ : H1 k α W ≃ₗ[k] V)
    (D : ∀ (T : X.Modules), affineLocallyFiniteType X T →
      (T ⟶ W) ≃ (H1 k α T →ₗ[k] V))
    (hD : ∀ T hT f x, D T hT f x =
      τ ((moduleCohomologyFunctorOfHom X α 1).map f x))

include hV hW τ D hD

/-- A coherent subobject containing W and all original sections equals F.
Purity belongs to F, not merely W. -/
theorem epi_intermediate_of_trace
    (F : X.Modules) (a : W ⟶ F) [Mono a]
    (hQ : HasFiniteClosedSupport (cokernel a))
    (hdeg : 2 ≤ Module.finrank k (H0 k α (cokernel a)))
    (hPure : ∀ (T : X.Modules), affineLocallyFiniteType X T →
      HasFiniteClosedSupport T → ∀ t : T ⟶ F, Mono t → IsZero T)
    (B : X.Modules) (hBcoh : affineLocallyFiniteType X B)
    (b : B ⟶ F) [Mono b] (aB : W ⟶ B) (hab : aB ≫ b = a)
    (hsections : ∀ s : 𝟙_ X.Modules ⟶ F,
      ∃ t : 𝟙_ X.Modules ⟶ B, t ≫ b = s) : Epi b := by
  have hcomp : HasFiniteClosedSupport (cokernel (aB ≫ b)) := by
    rw [hab]
    exact hQ
  obtain ⟨hT, hC⟩ := finiteSupport_cokernels_of_factor aB b hcomp
  let : Mono aB := mono_of_mono_fac hab
  rcases subsingleton_or_nontrivial (H1 k α B) with hB0 | hBnt
  · exact epi_of_H1_zero_of_sections_factor k α b hC hB0 hsections
  · let := hBnt
    obtain ⟨sp⟩ := splitting_of_finiteSupport k α V hV W τ B aB hT
      (D B hBcoh) (D W hW) (hD B hBcoh) (hD W hW)
    have hTcoh : affineLocallyFiniteType X (cokernel aB) :=
      (affineLocallyFiniteType X).prop_cokernel aB hW hBcoh
    let j : cokernel aB ⟶ B := sp.s
    have hjg : j ≫ cokernel.π aB = 𝟙 (cokernel aB) := sp.s_g
    have hj : Mono j := mono_of_mono_fac hjg
    have hb : Mono b := inferInstance
    have hjb : Mono (j ≫ b) :=
      { right_cancellation := fun f g h => hj.right_cancellation f g
          (hb.right_cancellation (f ≫ j) (g ≫ j)
            ((Category.assoc f j b).trans (h.trans (Category.assoc g j b).symm))) }
    have hzT : IsZero (cokernel aB) :=
      hPure _ hTcoh hT (j ≫ b) hjb
    let S₁ := ShortComplex.cokernelSequence aB
    have hS₁ : S₁.ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact aB,
        mono_f := inferInstanceAs (Mono aB) }
    let : IsIso aB := hS₁.isIso_f_iff.mpr hzT
    have hsectionsW : ∀ s : 𝟙_ X.Modules ⟶ F,
        ∃ t : 𝟙_ X.Modules ⟶ W, t ≫ a = s := by
      intro s
      obtain ⟨t, ht⟩ := hsections s
      refine ⟨t ≫ inv aB, ?_⟩
      rw [← hab, Category.assoc, IsIso.inv_hom_id_assoc]
      exact ht
    have hg0 : ((moduleCohomologyFunctorOfHom X α 0).map (cokernel.π a)).hom = 0 :=
      H0_map_zero_of_sections_zero k α (cokernel.π a)
        (sections_map_zero_of_factor a (cokernel.π a)
          (cokernel.condition a) hsectionsW)
    let S := ShortComplex.cokernelSequence a
    have hS : S.ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact a,
        mono_f := inferInstanceAs (Mono a) }
    let := moduleCohomologyModuleOfHom X α S.X₂ 0
    let := moduleCohomologyModuleOfHom X α S.X₃ 0
    let := moduleCohomologyModuleOfHom X α S.X₁ 1
    let δ : H0 k α (cokernel a) →ₗ[k] H1 k α W :=
      moduleCohomologyConnectingOfHom X α S hS 0
    have hex : Function.Exact
        ((moduleCohomologyFunctorOfHom X α 0).map (cokernel.π a)).hom δ :=
      moduleCohomologyConnectingOfHom_exact_left X α S hS 0
    have hi : Function.Injective δ :=
      (LinearMap.injective_iff_eq_zero_of_exact hex).mpr hg0
    let : Module.Finite k V := FiniteDimensional.of_finrank_eq_succ hV
    let : Module.Finite k (H1 k α W) :=
      FiniteDimensional.of_injective τ.toLinearMap τ.injective
    have hle : Module.finrank k (H0 k α (cokernel a)) ≤
        Module.finrank k (H1 k α W) :=
      LinearMap.finrank_le_finrank_of_injective hi
    have hw : Module.finrank k (H1 k α W) = 1 := τ.finrank_eq.trans hV
    omega

/-- The concrete image of a finite section row together with W is coherent,
and its inclusion is epi. Surjectivity is only assumed on global sections. -/
theorem epi_sections_coprod_canonical
    (F : X.Modules) (hF : affineLocallyFiniteType X F)
    (a : W ⟶ F) [Mono a]
    (hQ : HasFiniteClosedSupport (cokernel a))
    (hdeg : 2 ≤ Module.finrank k (H0 k α (cokernel a)))
    (hPure : ∀ (T : X.Modules), affineLocallyFiniteType X T →
      HasFiniteClosedSupport T → ∀ t : T ⟶ F, Mono t → IsZero T)
    {J : Type u} [Finite J] (s : J → (𝟙_ X.Modules ⟶ F))
    (hs : Function.Surjective ((Sigma.desc s).val.app (op ⊤))) :
    Epi (coprod.desc (Sigma.desc s) a) := by
  let P : X.Modules := ∐ fun _ : J => 𝟙_ X.Modules
  let ν : P ⟶ F := Sigma.desc s
  let f : P ⨿ W ⟶ F := coprod.desc ν a
  let B := Abelian.image f
  let b : B ⟶ F := Abelian.image.ι f
  let v : P ⨿ W ⟶ B := Abelian.factorThruImage f
  let aB : W ⟶ B := coprod.inr ≫ v
  have hP : affineLocallyFiniteType X P :=
    (affineLocallyFiniteType X).prop_coproduct
      (fun _ => affineLocallyFiniteType_unit X)
  have hPW : affineLocallyFiniteType X (P ⨿ W) :=
    (affineLocallyFiniteType X).prop_coprod P W hP hW
  have hB : affineLocallyFiniteType X B :=
    (affineLocallyFiniteType X).prop_kernel (cokernel.π f) hF
      ((affineLocallyFiniteType X).prop_cokernel f hPW hF)
  have hab : aB ≫ b = a := by
    simp only [aB, Category.assoc, v, b, Abelian.image.fac, f, coprod.inr_desc]
  have hsec : ∀ t : 𝟙_ X.Modules ⟶ F,
      ∃ z : 𝟙_ X.Modules ⟶ B, z ≫ b = t := by
    intro t
    obtain ⟨z, hz⟩ := exists_unitHom_factor_of_surjective ν hs t
    refine ⟨z ≫ coprod.inl ≫ v, ?_⟩
    simpa only [Category.assoc, v, b, Abelian.image.fac, f, coprod.inl_desc] using hz
  let : Epi b := epi_intermediate_of_trace k α V hV W hW τ D hD
    F a hQ hdeg hPure B hB b aB hab hsec
  have hvb : Epi (v ≫ b) := inferInstance
  simpa only [v, b, Abelian.image.fac, f, ν] using hvb

end Enlargement

section OriginalEvaluation

variable (F : X.Modules) {J : Type u} [Finite J]
    (s : J → (𝟙_ X.Modules ⟶ F))

/-- The finite section row factors through the original all-section evaluation. -/
def finiteRowToEvaluation :
    (∐ fun _ : J => 𝟙_ X.Modules) ⟶
      (∐ fun _ : (𝟙_ X.Modules ⟶ F) => 𝟙_ X.Modules) :=
  Sigma.desc fun j => Sigma.ι (fun _ : (𝟙_ X.Modules ⟶ F) => 𝟙_ X.Modules) (s j)

theorem finiteRowToEvaluation_fac :
    finiteRowToEvaluation F s ≫ globalSectionsEval F = Sigma.desc s := by
  apply Sigma.hom_ext
  intro j
  simp [finiteRowToEvaluation, ι_globalSectionsEval]

/-- The reverse evaluation factorization uses surjectivity on sections;
it does not assume that the finite row is epi as a sheaf map. -/
theorem evaluation_factors_finiteRow
    (hs : Function.Surjective ((Sigma.desc s).val.app (op ⊤))) :
    ∃ q, q ≫ Sigma.desc s = globalSectionsEval F := by
  classical
  have h : ∀ t : 𝟙_ X.Modules ⟶ F,
      ∃ z : 𝟙_ X.Modules ⟶ (∐ fun _ : J => 𝟙_ X.Modules),
        z ≫ Sigma.desc s = t :=
    fun t => exists_unitHom_factor_of_surjective (Sigma.desc s) hs t
  choose z hz using h
  refine ⟨Sigma.desc z, ?_⟩
  apply Sigma.hom_ext
  intro t
  rw [Sigma.ι_comp_desc_assoc, hz, ι_globalSectionsEval]

/-- The actual finite evaluation image is coherent. The two factorizations
above identify it with the original all-section evaluation image. -/
theorem finiteEvaluationImage_coherent [IsLocallyNoetherian X]
    (hF : affineLocallyFiniteType X F) :
    affineLocallyFiniteType X (Abelian.image (Sigma.desc s)) := by
  have hP : affineLocallyFiniteType X (∐ fun _ : J => 𝟙_ X.Modules) :=
    (affineLocallyFiniteType X).prop_coproduct
      (fun _ => affineLocallyFiniteType_unit X)
  exact (affineLocallyFiniteType X).prop_kernel (cokernel.π (Sigma.desc s)) hF
    ((affineLocallyFiniteType X).prop_cokernel (Sigma.desc s) hP hF)

end OriginalEvaluation


section CanonicalPurity

variable (k : Type u) [Field k] (α : k →+* Γ(X, ⊤))
    (V : Type v) [AddCommGroup V] [Module k V] (W : X.Modules)

/-- The coherent Hom/H1 comparison alone excludes coherent finite-support
subobjects of the actual canonical sheaf. No generation is used. -/
theorem no_finiteSupport_subobject_of_comparison
    (T : X.Modules) (hT : HasFiniteClosedSupport T)
    (D : (T ⟶ W) ≃ (H1 k α T →ₗ[k] V))
    (t : T ⟶ W) [Mono t] : IsZero T := by
  let : Subsingleton (H1 k α T) := finiteSupport_positive hT 0
  have ht : t = 0 := D.injective (Subsingleton.elim _ _)
  exact IsZero.of_mono_eq_zero t ht

end CanonicalPurity

section FiniteRow

/-- Finiteness of original H0 produces a finite row spanning all global
sections. This does not assert sheaf generation by that row. -/
theorem exists_finiteRow_surjective_on_sections
    (k : Type u) [Field k] (α : k →+* Γ(X, ⊤))
    (F : X.Modules) (hF0 : Module.Finite k (H0 k α F)) :
    ∃ (J : Type u) (_ : Fintype J) (s : J → (𝟙_ X.Modules ⟶ F)),
      Function.Surjective ((Sigma.desc s).val.app (op ⊤)) := by
  classical
  let := moduleCategoryLinearOfHom X α
  let := moduleCohomologyModuleOfHom X α F 0
  dsimp only [H0, moduleCohomologyFunctorOfHom] at hF0
  let : Module.Finite k (Sheaf.H.{u + 1} (moduleAddSheaf X F) 0) := hF0
  let : Module k Γ(F, ⊤) := Module.compHom _ α
  let G : Type u := 𝟙_ X.Modules ⟶ F
  let e : G ≃+ Γ(F, ⊤) := unitHomGlobalSectionsAddEquiv X F
  let r : Sheaf.H.{u + 1} (moduleAddSheaf X F) 0 ≃ₗ[k] Γ(F, ⊤) :=
    moduleH0EquivOfHom X α F
  have he : ∀ (a : k) (f : G), e (a • f) = a • e f := by
    intro a f
    have happ := moduleCategoryLinearOfHom_smul_app X α f a ⊤ (1 : Γ(X, ⊤))
    have hpoint : e (a • f) = globalRestriction X ⊤ (α a) • e f := happ
    exact hpoint.trans (congrArg (fun z : Γ(X, ⊤) => z • e f)
      (globalRestriction_top_apply X (α a)))
  let E : G ≃ₗ[k] Sheaf.H.{u + 1} (moduleAddSheaf X F) 0 :=
    { __ := e.trans r.symm.toAddEquiv
      map_smul' := fun a f => (congrArg r.symm (he a f)).trans
        (r.symm.map_smul a (e f)) }
  let : Module.Finite k G :=
    FiniteDimensional.of_injective E.toLinearMap E.injective
  let b := Module.Basis.ofVectorSpace k G
  let J := Module.Basis.ofVectorSpaceIndex k G
  let : Fintype J := inferInstance
  refine ⟨J, inferInstance, b, ?_⟩
  apply sections_surjective_of_unitHom_factor
  intro t
  refine ⟨∑ j : J, b.repr t j • Sigma.ι (fun _ : J => 𝟙_ X.Modules) j, ?_⟩
  simp only [Preadditive.sum_comp, Linear.smul_comp, Sigma.ι_comp_desc]
  exact b.sum_repr t

end FiniteRow

section OriginalEvaluationSum

variable [IsLocallyNoetherian X]
    (k : Type u) [Field k] (α : k →+* Γ(X, ⊤))
    (V : Type v) [AddCommGroup V] [Module k V]
    (hV : Module.finrank k V = 1)
    (W : X.Modules) (hW : affineLocallyFiniteType X W)
    (τ : H1 k α W ≃ₗ[k] V)
    (D : ∀ (T : X.Modules), affineLocallyFiniteType X T →
      (T ⟶ W) ≃ (H1 k α T →ₗ[k] V))
    (hD : ∀ T hT f x, D T hT f x =
      τ ((moduleCohomologyFunctorOfHom X α 1).map f x))

include hV hW τ D hD

/-- The final algebraic-core endpoint uses the original all-section
evaluation. Its epimorphy says precisely that its image G plus W is F. -/
theorem epi_originalEvaluation_sum
    (F : X.Modules) (hF : affineLocallyFiniteType X F)
    (a : W ⟶ F) [Mono a]
    (hQ : HasFiniteClosedSupport (cokernel a))
    (hdeg : 2 ≤ Module.finrank k (H0 k α (cokernel a)))
    (hPure : ∀ (T : X.Modules), affineLocallyFiniteType X T →
      HasFiniteClosedSupport T → ∀ t : T ⟶ F, Mono t → IsZero T)
    {J : Type u} [Finite J] (s : J → (𝟙_ X.Modules ⟶ F))
    (hs : Function.Surjective ((Sigma.desc s).val.app (op ⊤))) :
    Epi (coprod.desc (globalSectionsEval F) a) := by
  let : Epi (coprod.desc (Sigma.desc s) a) :=
    epi_sections_coprod_canonical k α V hV W hW τ D hD F hF a hQ hdeg hPure s hs
  have hfac :
      coprod.map (finiteRowToEvaluation F s) (𝟙 W) ≫
        coprod.desc (globalSectionsEval F) a =
          coprod.desc (Sigma.desc s) a := by
    apply coprod.hom_ext
    · simpa only [Category.assoc, coprod.inl_map_assoc, coprod.inl_desc,
        coprod.inl_desc_assoc] using finiteRowToEvaluation_fac F s
    · simp
  exact epi_of_epi_fac hfac

/-- Finite original H0 and the original trace-normalized comparisons
give the actual evaluation-image enlargement conclusion. -/
theorem epi_originalEvaluation_sum_of_finiteH0
    (F : X.Modules) (hF : affineLocallyFiniteType X F)
    (hF0 : Module.Finite k (H0 k α F))
    (a : W ⟶ F) [Mono a]
    (hQ : HasFiniteClosedSupport (cokernel a))
    (hdeg : 2 ≤ Module.finrank k (H0 k α (cokernel a)))
    (hPure : ∀ (T : X.Modules), affineLocallyFiniteType X T →
      HasFiniteClosedSupport T → ∀ t : T ⟶ F, Mono t → IsZero T) :
    Epi (coprod.desc (globalSectionsEval F) a) := by
  obtain ⟨J, hJ, s, hs⟩ := exists_finiteRow_surjective_on_sections k α F hF0
  let := hJ
  exact epi_originalEvaluation_sum k α V hV W hW τ D hD
    F hF a hQ hdeg hPure s hs

end OriginalEvaluationSum

/-- Finite support transports along the specified sheaf isomorphism. -/
theorem finiteSupport_of_iso {M N : X.Modules} (e : M ≅ N)
    (hN : HasFiniteClosedSupport N) : HasFiniteClosedSupport M := by
  rcases hN with ⟨n, p, hp, hc, hz⟩
  exact ⟨n, p, hp, hc, fun x hx =>
    (hz x hx).of_iso ((stalkFunctor X x).mapIso e)⟩

/-- The comparison with a supplied original quotient is the unique
comparison of its two actual cokernel cocones. -/
def originalRowCokernelIso (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    cokernel S.f ≅ S.X₃ := by
  let := hS.epi_g
  exact (cokernelIsCokernel S.f).coconePointUniqueUpToIso hS.exact.gIsCokernel

/-- The cokernel comparison retains the original quotient arrow. -/
theorem originalRowCokernelIso_hom (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    cokernel.π S.f ≫ (originalRowCokernelIso S hS).hom = S.g := by
  let := hS.epi_g
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel S.f) hS.exact.gIsCokernel WalkingParallelPair.one

/-- Original-row endpoint: the actual evaluation image plus the original
canonical inclusion is the whole middle sheaf. -/
theorem epi_originalRowEvaluation_sum [IsLocallyNoetherian X]
    (k : Type u) [Field k] (α : k →+* Γ(X, ⊤))
    (V : Type v) [AddCommGroup V] [Module k V]
    (hV : Module.finrank k V = 1)
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hW : affineLocallyFiniteType X S.X₁)
    (hF : affineLocallyFiniteType X S.X₂)
    (hF0 : Module.Finite k (H0 k α S.X₂))
    (hQ : HasFiniteClosedSupport S.X₃)
    (hdeg : 2 ≤ Module.finrank k (H0 k α S.X₃))
    (τ : H1 k α S.X₁ ≃ₗ[k] V)
    (D : ∀ (T : X.Modules), affineLocallyFiniteType X T →
      (T ⟶ S.X₁) ≃ (H1 k α T →ₗ[k] V))
    (hD : ∀ T hT f x, D T hT f x =
      τ ((moduleCohomologyFunctorOfHom X α 1).map f x))
    (hPure : ∀ (T : X.Modules), affineLocallyFiniteType X T →
      HasFiniteClosedSupport T → ∀ t : T ⟶ S.X₂, Mono t → IsZero T) :
    Epi (coprod.desc (globalSectionsEval S.X₂) S.f) := by
  let := hS.mono_f
  let e := originalRowCokernelIso S hS
  have hQ' : HasFiniteClosedSupport (cokernel S.f) :=
    finiteSupport_of_iso e hQ
  let E : H0 k α (cokernel S.f) ≃ₗ[k] H0 k α S.X₃ :=
    ((moduleCohomologyFunctorOfHom X α 0).mapIso e).toLinearEquiv
  have hdeg' : 2 ≤ Module.finrank k (H0 k α (cokernel S.f)) := by
    rw [E.finrank_eq]
    exact hdeg
  exact epi_originalEvaluation_sum_of_finiteH0 k α V hV S.X₁ hW τ D hD
    S.X₂ hF hF0 S.f hQ' hdeg' hPure

end AlgebraicGeometry.Scheme.Cohomology.CanonicalEnlargement

