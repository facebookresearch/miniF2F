(*
  Authors: Wenda Li
*)

theory amc12a_2002_p12 imports
  Complex_Main
  "HOL-Computational_Algebra.Computational_Algebra"
begin

theorem amc12a_2002_p12:
  fixes f :: "real => real"
    and k :: real and a b::nat
  assumes "\<forall> x. f x = x^2 - 63 * x + k"
    and "f -` {0} = {of_nat a, of_nat b}"
    and "prime a" and "prime b"
  shows "k=122"
  sorry

end