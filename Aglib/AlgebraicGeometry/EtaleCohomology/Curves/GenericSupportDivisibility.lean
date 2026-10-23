/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericArtinCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.CohomologyConsequences
public import Aglib.CategoryTheory.Sites.SheafCohomology.Vanishing.MapBijective

/-!
# Divisibility through the original generic unit and its supported defects

This is conditional assembly, not the geometric support theorem. Actual
kernel/cokernel acyclicity, higher-image divisibility and higher source
divisibility remain explicit. The final maps are the original Gm power map
and ordinary Picard Kummer boundary.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u w w' dS dX dA

private theorem nsmul_bijective_of_addEquiv {A B : Type*}
    [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (n : ℕ)
    (h : Function.Bijective (fun b : B => n • b)) :
    Function.Bijective (fun a : A => n • a) := by
  have he : (fun a : A => n • a) = e.symm ∘ (fun b : B => n • b) ∘ e := by
    funext a
    simp
  rw [he]
  exact e.symm.bijective.comp (h.comp e.bijective)

variable (X : Scheme.{u}) [IsNoetherian X]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} (genericArtinLocus X))]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} (genericArtinLocus X))]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}]
  (n : ℕ)
  (hk : ∀ k : ℕ, 1 ≤ k → Subsingleton (Sheaf.H.{w'} (kernel (genericArtinUnit X)) k))
  (hc : ∀ k : ℕ, 1 ≤ k → Subsingleton (Sheaf.H.{w'} (cokernel (genericArtinUnit X)) k))
  (hh : ∀ k : ℕ, 1 ≤ k → IsIso
    (n • 𝟙 ((higherDirectImage (genericArtinMap X) k).obj (gm (genericArtinLocus X)))))
  (hs : ∀ k : ℕ, 2 ≤ k → Function.Bijective
    (Sheaf.H.map (power (genericArtinLocus X) n) k))

include hk hc hh hs in
/-- Positive defect acyclicity transfers generic divisibility to the original Gm power map. -/
theorem genericUnit_power_bijective (q : ℕ) (hq : 1 ≤ q) :
    Function.Bijective (Sheaf.H.map (power X n) (q + 1)) := by
  let : Subsingleton (Sheaf.H.{w'} (kernel (genericArtinUnit X)) (q + 1)) :=
    hk _ (by omega)
  let : Subsingleton (Sheaf.H.{w'} (kernel (genericArtinUnit X)) (q + 1 + 1)) :=
    hk _ (by omega)
  let : Subsingleton (Sheaf.H.{w'} (cokernel (genericArtinUnit X)) q) := hc _ hq
  let : Subsingleton (Sheaf.H.{w'} (cokernel (genericArtinUnit X)) (q + 1)) :=
    hc _ (by omega)
  let e := AddEquiv.ofBijective (Sheaf.H.map (genericArtinUnit X) (q + 1))
    (Sheaf.H.map_bijective_of_kernel_cokernel (genericArtinUnit X) q)
  have hb := genericDirectImage_nsmul_bijective X n q hq hh hs
  have hb' : Function.Bijective (fun x : Sheaf.H.{w'}
      ((directImage (genericArtinMap X)).obj (gm (genericArtinLocus X))) (q + 1) =>
      n • x) := by
    have heq : (Sheaf.H.map
        (n • 𝟙 ((directImage (genericArtinMap X)).obj (gm (genericArtinLocus X))))
        (q + 1) : _ → _) = (fun x => n • x) :=
      funext (cohomology_map_nsmul_id _ (q + 1) n)
    exact heq ▸ hb
  have ha := nsmul_bijective_of_addEquiv e n hb'
  have heq : (Sheaf.H.map (power X n) (q + 1) : _ → _) = (fun x => n • x) :=
    funext (cohomology_map_nsmul_id (gm X) (q + 1) n)
  exact heq.symm ▸ ha

include hk hc hh hs in
/-- The conditional geometric inputs give surjectivity of the original Picard boundary. -/
theorem genericUnit_picardBoundary_surjective (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) :
    Function.Surjective (Kummer.picardBoundary X n hn hinv) :=
  Kummer.picardBoundary_surjective_of_power_injective X n hn hinv
    (genericUnit_power_bijective X n hk hc hh hs 1 (by omega)).injective

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
