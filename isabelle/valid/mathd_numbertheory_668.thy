(*
  Authors: Wenda Li
*)

theory mathd_numbertheory_668 
  imports Complex_Main "HOL-Computational_Algebra.Computational_Algebra"
    "HOL-Number_Theory.Number_Theory"
begin

theorem mathd_numbertheory_668:
  fixes l r::int and a b::int
  assumes "0\<le>l" "l<7" "0\<le>r" "r<7"
    and "[l * (2 + 3) = 1] (mod 7)" 
    and "0\<le>a \<and> a<7 \<and> [a*2=1] (mod 7)"
    and "0\<le>b \<and> b<7 \<and> [b*3=1] (mod 7)"
    and "r = (a+b) mod 7"
  shows "l - r = 1"
  sorry

end   