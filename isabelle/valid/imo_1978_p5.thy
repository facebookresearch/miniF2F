(*
  Authors: Wenda Li
*)

theory imo_1978_p5 
  imports Complex_Main "HOL-Computational_Algebra.Computational_Algebra"
begin

theorem imo_1978_p5:
  fixes n :: nat and f :: "nat \<Rightarrow> nat"
  assumes "inj f" and "f 0 = 0"
  shows "(\<Sum> k \<in>{1..<n+1}. 1 / k) \<le> (\<Sum> k \<in>{1..<n+1}. (f k) / k^2)"
  sorry

end   