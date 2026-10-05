import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

import Definitions.FLT.Def_HeckeEis_EichlerIntegral

open scoped Manifold
theorem HeckeEis.IsEichlerIntegral.isBoundedAtImInfty_eval {n : ℕ} {g : UpperHalfPlane → ℂ}
    {G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hG : HeckeEis.IsEichlerIntegral n g G) {h : ℤ} (hh : 0 < h)
    (hper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) ((h : ℝ) : ℂ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hbdd : UpperHalfPlane.IsBoundedAtImInfty g)
    (hT : ∀ τ : UpperHalfPlane, G ((h : ℝ) +ᵥ τ) = HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ h) (G τ)) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ : UpperHalfPlane =>
      MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((G τ : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)) := by sorry
