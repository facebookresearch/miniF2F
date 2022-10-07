(*
  Authors: Wenda Li
*)

theory mathd_numbertheory_126 
  imports Complex_Main "HOL-Computational_Algebra.Computational_Algebra"
    "HOL-Number_Theory.Number_Theory"
begin

theorem mathd_numbertheory_126:
  fixes x :: nat
  assumes "x>0"
  shows "(LEAST a. gcd a 40 = x + 3 \<and> lcm a 40 = x * (x + 3)) =  8"
  sorry

end   