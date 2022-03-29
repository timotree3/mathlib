import analysis.calculus.fderiv
import linear_algebra.matrix.determinant

#check 1

variables {n 𝕜 A : Type*} [nondiscrete_normed_field 𝕜]
  [normed_ring A] [fintype n] [decidable_eq n] [normed_space 𝕜 A]

local attribute [instance] matrix.normed_group matrix.normed_space

def matrix.trace_clm : matrix n n A →L[𝕜] A :=
begin
  refine @linear_map.mk_continuous 𝕜 𝕜 (matrix n n A) A _ _ _ _ _,
end

example : fderiv 𝕜 (λ A : matrix n n 𝕜, A.det) 1 = matrix.trace :=
begin

end
