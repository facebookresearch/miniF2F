(*
  Authors: Wenda Li
*)

theory mathd_numbertheory_233 
  imports Complex_Main "HOL-Computational_Algebra.Computational_Algebra"
          "HOL-Number_Theory.Number_Theory"
begin

theorem mathd_numbertheory_233:
  fixes b::int
  assumes "0\<le>b"
    and "b<11^2"
    and "[b * 24 = 1] (mod (11^2))"
  shows "b = 116"
  sorry

end
    