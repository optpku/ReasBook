module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_definition_1_15.BigO

public section

/- Definition 1.15 (1). For functions `f g : S → NNReal` on an unbounded subset `S ⊆ NNReal`,
the source threshold formulation of `f(x) = O(g(x))` is realized by the reusable bridge
`Asymptotics.isBigO_nnrealSubtype_iff`. -/
#check Asymptotics.isBigO_nnrealSubtype_iff

/- Definition 1.15 (2). For functions `f g : (Fin k → NNReal) → NNReal`, the shared-threshold
formulation of `f(x₁, ..., x_k) = O(g(x₁, ..., x_k))` is realized by the reusable bridge
`Asymptotics.isBigO_finNNReal_iff`. -/
#check Asymptotics.isBigO_finNNReal_iff

end
