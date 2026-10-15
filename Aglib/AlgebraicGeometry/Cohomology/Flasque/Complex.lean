/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Flasque.Pushforward
public import Aglib.Algebra.Homology.CochainComplex.KernelSequence
public import Aglib.Algebra.Homology.MappingCone.Acyclicity

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/FlasqueComplex.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 181]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Bounded-below flasque complexes and original direct image

Actual finite biproducts of flasque module sheaves are flasque. In an acyclic
bounded-below complex of flasque sheaves, induction from the lower bound
makes every original differential kernel flasque. Section surjectivity then
proves exactness after any scheme direct image. Applying this to the actual
mapping cone proves preservation of quasi-isomorphisms between bounded-below
flasque complexes. There is no upper-bound, affine or quasicoherence premise.
-/

@[expose] public section
noncomputable section

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
/-- Flasqueness is transported by an actual original sheaf isomorphism. -/
theorem flasque_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    [TopCat.Presheaf.IsFlasque M.presheaf] : TopCat.Presheaf.IsFlasque N.presheaf where
  epi {U V} k := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro z
    obtain ⟨x, hx⟩ := (AddCommGrpCat.epi_iff_surjective (M.presheaf.map k)).mp
      (TopCat.Presheaf.IsFlasque.epi k) (e.inv.app V.unop z)
    refine ⟨e.hom.app U.unop x, ?_⟩
    have hn := ConcreteCategory.congr_hom (e.hom.mapPresheaf.naturality k) x
    change e.hom.app V.unop (M.presheaf.map k x) =
      N.presheaf.map k (e.hom.app U.unop x) at hn
    rw [← hn, hx]
    exact congrArg (fun f : N ⟶ N => f.app V.unop z) e.inv_hom_id
/-- An actual binary product of flasque module sheaves is flasque. -/
instance prod_isFlasque {X : Scheme.{u}} (M N : X.Modules)
    [TopCat.Presheaf.IsFlasque M.presheaf] [TopCat.Presheaf.IsFlasque N.presheaf] :
    TopCat.Presheaf.IsFlasque (M ⨯ N).presheaf where
  epi {U V} k := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro z
    let i : M ⟶ M ⨯ N := prod.lift (𝟙 M) 0
    let j : N ⟶ M ⨯ N := prod.lift 0 (𝟙 N)
    obtain ⟨a, ha⟩ := (AddCommGrpCat.epi_iff_surjective (M.presheaf.map k)).mp
      (TopCat.Presheaf.IsFlasque.epi k) ((Scheme.Modules.Hom.app prod.fst V.unop) z)
    obtain ⟨b, hb⟩ := (AddCommGrpCat.epi_iff_surjective (N.presheaf.map k)).mp
      (TopCat.Presheaf.IsFlasque.epi k) ((Scheme.Modules.Hom.app prod.snd V.unop) z)
    refine ⟨i.app U.unop a + j.app U.unop b, ?_⟩
    have hi := ConcreteCategory.congr_hom (i.mapPresheaf.naturality k) a
    have hj := ConcreteCategory.congr_hom (j.mapPresheaf.naturality k) b
    change i.app V.unop (M.presheaf.map k a) =
      (M ⨯ N).presheaf.map k (i.app U.unop a) at hi
    change j.app V.unop (N.presheaf.map k b) =
      (M ⨯ N).presheaf.map k (j.app U.unop b) at hj
    rw [map_add, ← hi, ← hj, ha, hb]
    have hid : (prod.fst : M ⨯ N ⟶ M) ≫ i + prod.snd ≫ j = 𝟙 (M ⨯ N) := by
      apply prod.hom_ext <;> simp [i, j, Preadditive.add_comp]
    exact congrArg (fun f : M ⨯ N ⟶ M ⨯ N => f.app V.unop z) hid
attribute [local instance] Abelian.hasFiniteBiproducts
/-- The original binary biproduct of flasque module sheaves is flasque. -/
instance biprod_isFlasque {X : Scheme.{u}} (M N : X.Modules)
    [TopCat.Presheaf.IsFlasque M.presheaf] [TopCat.Presheaf.IsFlasque N.presheaf] :
    TopCat.Presheaf.IsFlasque (M ⊞ N).presheaf :=
  flasque_of_iso (biprod.isoProd M N).symm
end AlgebraicGeometry.Scheme.Modules
end

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
namespace AlgebraicGeometry.Scheme.Modules
/-- The actual differential kernels of a bounded-below acyclic flasque complex are flasque. -/
theorem acyclicComplex_kernel_isFlasque {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ)
    (a : ℤ) (hl : ∀ n, n < a → IsZero (K.X n)) (hA : ∀ n, K.ExactAt n)
    (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.X n).presheaf) (n : ℤ) :
    TopCat.Presheaf.IsFlasque (kernel (K.d n (n + 1))).presheaf := by
  have hbelow (m : ℤ) (hm : m < a) :
      TopCat.Presheaf.IsFlasque (kernel (K.d m (m + 1))).presheaf := by
    let : Injective (kernel (K.d m (m + 1))) :=
      (IsZero.of_mono (kernel.ι (K.d m (m + 1))) (hl m hm)).injective
    infer_instance
  by_cases hn : n < a
  · exact hbelow n hn
  have han : a - 1 ≤ n := by omega
  clear hn
  induction n, han using Int.leInduction with
  | base => exact hbelow (a - 1) (by omega)
  | succ n hn ih =>
    let : TopCat.Presheaf.IsFlasque
        (CochainComplex.kernelSequence K n).X₁.presheaf := ih
    let : TopCat.Presheaf.IsFlasque
        (CochainComplex.kernelSequence K n).X₂.presheaf := hK n
    have h := flasque_of_shortExact
      (CochainComplex.kernelSequence_shortExact K n (hA (n + 1)))
    rw [show n + 1 + 1 = n + 2 by omega]
    exact h
/-- Original direct image preserves exactness of a bounded-below acyclic flasque complex. -/
theorem pushforward_exactAt_succ_of_acyclic_flasque {X Y : Scheme.{u}}
    (f : X ⟶ Y) (K : CochainComplex X.Modules ℤ)
    (a : ℤ) (hl : ∀ n, n < a → IsZero (K.X n)) (hA : ∀ n, K.ExactAt n)
    (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.X n).presheaf) (n : ℤ) :
    (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj K).ExactAt (n + 1) := by
  let F := Scheme.Modules.pushforward f
  let k := kernel.lift (K.d (n + 1) (n + 2)) (K.d n (n + 1)) (K.d_comp_d n (n + 1) (n + 2))
  let : TopCat.Presheaf.IsFlasque
      (CochainComplex.kernelSequence K n).X₁.presheaf :=
    acyclicComplex_kernel_isFlasque K a hl hA hK n
  have hk (U : X.Opens) : Function.Surjective (k.app U) :=
    sections_surjective_of_flasque_kernel
      (CochainComplex.kernelSequence_shortExact K n (hA (n + 1))) U
  have he : Epi (F.map k) := by
    constructor
    intro N g h eq
    ext U m
    obtain ⟨x, hx⟩ := hk (f ⁻¹ᵁ U) m
    have hc := congrArg (fun q => q.app U x) eq
    change g.app U (k.app (f ⁻¹ᵁ U) x) = h.app U (k.app (f ⁻¹ᵁ U) x) at hc
    simpa only [hx] using hc
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp; omega),
    ShortComplex.exact_iff_epi_kernel_lift]
  have h : kernel.lift (F.map (K.d (n + 1) (n + 2))) (F.map (K.d n (n + 1)))
      (by rw [← F.map_comp, K.d_comp_d, F.map_zero]) =
      F.map k ≫ kernelComparison (K.d (n + 1) (n + 2)) F := by
    apply (cancel_mono (kernel.ι (F.map (K.d (n + 1) (n + 2))))).mp
    simp only [kernel.lift_ι, Category.assoc, kernelComparison_comp_ι, ← F.map_comp]
    rw [kernel.lift_ι]
  change Epi (kernel.lift (F.map (K.d (n + 1) (n + 2))) (F.map (K.d n (n + 1))) _)
  rw [h]
  infer_instance
end AlgebraicGeometry.Scheme.Modules
end

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex CochainComplex
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
/-- The original cone of a morphism between flasque complexes has flasque terms. -/
theorem mappingCone_isFlasque {X : Scheme.{u}} {K L : CochainComplex X.Modules ℤ}
    (s : K ⟶ L) (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.X n).presheaf)
    (hL : ∀ n, TopCat.Presheaf.IsFlasque (L.X n).presheaf) (n : ℤ) :
    TopCat.Presheaf.IsFlasque ((mappingCone s).X n).presheaf := by
  let := hK (n + 1)
  let := hL n
  exact flasque_of_iso (homotopyCofiber.XIsoBiprod s n (n + 1) rfl).symm
/-- Original direct image preserves quasi-isomorphisms between bounded-below flasque complexes. -/
theorem quasiIso_pushforward_of_flasque {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : CochainComplex X.Modules ℤ} (s : K ⟶ L) [QuasiIso s]
    (a b : ℤ) (hKa : ∀ n, n < a → IsZero (K.X n))
    (hLb : ∀ n, n < b → IsZero (L.X n))
    (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.X n).presheaf)
    (hL : ∀ n, TopCat.Presheaf.IsFlasque (L.X n).presheaf) :
    QuasiIso (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).map s) := by
  have hlow (n : ℤ) (hn : n < min a b - 1) : IsZero ((mappingCone s).X n) := by
    rw [mappingCone.isZero_X_iff]
    exact ⟨hKa (n + 1) (by omega), hLb n (by omega)⟩
  have hA := CochainComplex.mappingCone_acyclic_of_quasiIso s
  have hF := mappingCone_isFlasque s hK hL
  apply CochainComplex.quasiIso_of_mappingCone_acyclic
  intro n
  have h := pushforward_exactAt_succ_of_acyclic_flasque f (mappingCone s)
    (min a b - 1) hlow hA hF (n - 1)
  rw [sub_add_cancel] at h
  exact h.of_iso (mappingCone.mapHomologicalComplexIso s (Scheme.Modules.pushforward f))
end AlgebraicGeometry.Scheme.Modules
end
