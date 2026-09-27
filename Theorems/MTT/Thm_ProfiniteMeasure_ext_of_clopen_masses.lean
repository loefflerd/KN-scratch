import Mathlib.NumberTheory.Padics.Measure.Basic
import Mathlib.Analysis.Normed.Field.Lemmas

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Set Filter UniformSpace ContinuousMap TopologicalSpace

theorem ProfiniteMeasure.ext_of_clopen_masses {X R : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [NormedField R]
    (μ ν : AbstractMeasure X R R)
    (h : ∀ U : Clopens X,
      μ ⟨(U : Set X).indicator (fun _ => (1 : R)),
        U.isClopen.continuous_indicator continuous_const⟩ =
      ν ⟨(U : Set X).indicator (fun _ => (1 : R)),
        U.isClopen.continuous_indicator continuous_const⟩) : μ = ν := by sorry
