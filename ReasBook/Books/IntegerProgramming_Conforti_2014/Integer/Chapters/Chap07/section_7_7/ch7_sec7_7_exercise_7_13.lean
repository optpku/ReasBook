import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_example_7_3

section Exercise713

/-- Exercise 7.13. The fractional lifted inequality from Example 7.8, represented by
`example_7_3_fractional_lifted_vector`, induces a facet of the corresponding `0,1` knapsack
polytope. -/
theorem exercise_7_13_example_7_8_lifted_cover_inequality_induces_facet :
    IsFacetOf
      (zero_one_knapsack_polytope example_7_3_weights 22)
      (lifted_cover_face example_7_3_weights 22 example_7_3_cover_set
        example_7_3_fractional_lifted_vector) := by
  -- Route correction: once Example 7.3 imports the canonical cover-lifting owners, the source
  -- proof closes by eliminating the known facet-defining-lifting membership statement.
  -- Reinterpret the known facet-defining lifting membership as the corresponding facet statement.
  simpa using
    mem_facet_defining_liftings_of_cover_inequality_iff.mp
      example_7_3_fractional_lifted_inequality_facet_defining

end Exercise713
