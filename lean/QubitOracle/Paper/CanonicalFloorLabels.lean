import QubitOracle.Paper.EventualFloor

namespace QubitOracle.Paper

namespace Label

/-- Supplement proposition `prop:SI_floor`: consistency toward an interior
truth and a vanishing floor imply eventual strict feasibility and hence
eventual inactivity of any projection that fixes the strict interior. -/
theorem prop_SI_floor
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (project : ℝ → E → E)
    (fixesInterior : ∀ r z, ‖z‖ < r → project r z = z)
    (x : ℕ → E) (xStar : E) (eta : ℕ → ℝ)
    (hx : Filter.Tendsto x Filter.atTop (nhds xStar))
    (heta : Filter.Tendsto eta Filter.atTop (nhds 0))
    (hinterior : ‖xStar‖ < 1) :
    (∀ᶠ n in Filter.atTop, ‖x n‖ < 1 - 2 * eta n) ∧
    (∀ᶠ n in Filter.atTop, project (1 - 2 * eta n) (x n) = x n) :=
  ⟨eventually_inside_vanishing_floor x xStar eta hx heta hinterior,
    eventually_floor_projection_inactive
      project fixesInterior x xStar eta hx heta hinterior⟩

/-- Supplement equation `eq:SI_floor_projection`: the floor projection is
eventually exactly the identity along every consistent interior controller. -/
theorem eq_SI_floor_projection
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (project : ℝ → E → E)
    (fixesInterior : ∀ r z, ‖z‖ < r → project r z = z)
    (x : ℕ → E) (xStar : E) (eta : ℕ → ℝ)
    (hx : Filter.Tendsto x Filter.atTop (nhds xStar))
    (heta : Filter.Tendsto eta Filter.atTop (nhds 0))
    (hinterior : ‖xStar‖ < 1) :
    ∀ᶠ n in Filter.atTop, project (1 - 2 * eta n) (x n) = x n :=
  eventually_floor_projection_inactive
    project fixesInterior x xStar eta hx heta hinterior

end Label

end QubitOracle.Paper
