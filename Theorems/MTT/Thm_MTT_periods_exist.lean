module

public import Definitions.MTT.Def_MTT_Measures

import Definitions.MTT.Def_MTT_Cohomology
import Definitions.MTT.Def_MTT_Arithmetic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Theorems.MTT.Thm_MTT_Cohomology_integral_finite_generation
import Theorems.MTT.Thm_MTT_Cohomology_base_change
import Theorems.MTT.Thm_MTT_Cohomology_integration_map
import Theorems.MTT.Thm_MTT_Cohomology_signed_evaluation
import Theorems.MTT.Thm_MTT_Cohomology_signed_packet_multiplicity_one
import Theorems.MTT.Thm_MTT_Cohomology_eigenclass_descent
import Theorems.MTT.Thm_MTT_Cohomology_evaluation_lattice

section privateSection

set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

namespace P2MPE

/-- `ℚ` is a flat `ℤ`-module: it is the localization of `ℤ` at its nonzero divisors. -/
instance flat_int_rat : Module.Flat ℤ ℚ :=
  IsLocalization.flat ℚ (nonZeroDivisors ℤ)

/-- Any field that is a `ℚ`-algebra is flat over `ℤ`. -/
instance flat_int_of_rat_algebra (K : Type*) [Field K] [Algebra ℚ K] :
    Module.Flat ℤ K :=
  haveI : Module.Free ℚ K := Module.Free.of_divisionRing ℚ K
  haveI : Module.Flat ℚ K := Module.Flat.of_free
  Module.Flat.trans ℤ ℚ K

/-- Coefficientwise extension of classes transports the integral evaluation
functionals along the coefficient homomorphism. -/
theorem evaluation_extends {N n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (ι : R →+* S) (ψ : Hc N n R) (φ : Hc N n S) (h : Extends ι ψ φ) (j : ℕ) (r : ℚ) :
    evaluation j r φ = ι (evaluation j r ψ) := by
  show AddMonoidAlgebra.coeff (φ.val (OnePoint.infty, (r : Cusp))) _
      = ι (AddMonoidAlgebra.coeff (ψ.val (OnePoint.infty, (r : Cusp))) _)
  rw [h OnePoint.infty ((r : ℚ) : Cusp)]
  exact MvPolynomial.coeff_map _ _ _

end P2MPE

open P2MPE in
theorem solution {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) :
    Nonempty (MTT.Periods k ι f.form) := by
  have hZ : Module.Finite ℤ (Hc N (k - 2) ℤ) :=
    MTT.Cohomology.integral_finite_generation hN
  have hQ : BaseChange N (k - 2) MTT.Qbar := MTT.Cohomology.base_change hN _
  have hC : BaseChange N (k - 2) ℂ := MTT.Cohomology.base_change hN _
  obtain ⟨I, -, hT, hI⟩ := MTT.Cohomology.integration_map (N := N) (k := k) hN hk
  obtain ⟨φ, hφ⟩ := MTT.Cohomology.signed_evaluation hN hk I hI hT ι f
  have hdesc : ∀ s : Bool, ∃ ω : ℂ, ω ≠ 0 ∧
      ∃ ψ : Hc N (k - 2) MTT.Qbar, Extends ι ψ (ω⁻¹ • φ s) := fun s =>
    MTT.Cohomology.eigenclass_descent hZ hQ hC ι f.epsilon f.coeff s
      (fun a b ha hb => MTT.Cohomology.signed_packet_multiplicity_one hN hk ι f s a b ha hb)
      (φ s) (hφ s).2
  choose ω hω ψ hψ using hdesc
  refine ⟨{ omega := ω, omega_ne := hω,
            value := fun s j r => evaluation j r (ψ s) / ((k - 2).choose j : MTT.Qbar),
            comparison := ?_, lattice_fg := ?_ }⟩
  · intro s j r hj
    have hbin : ((k - 2).choose j : ℂ) ≠ 0 := by
      exact_mod_cast Nat.cast_ne_zero.mpr (Nat.choose_pos hj).ne'
    have hkey : ι (evaluation j r (ψ s)) = (ω s)⁻¹ * evaluation j r (φ s) := by
      rw [← evaluation_extends ι (ψ s) _ (hψ s) j r]
      exact map_smul (evaluation j r) _ (φ s)
    rw [map_div₀, map_natCast, hkey, (hφ s).1 j r hj]
    field_simp
  · exact MTT.Cohomology.evaluation_lattice hZ hQ ψ
end

end privateSection

public section publicSection

noncomputable section
open scoped BigOperators

theorem MTT.periods_exist
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) :
    Nonempty (MTT.Periods k ι f.form) := _root_.solution hN hk ι f
end

end publicSection
