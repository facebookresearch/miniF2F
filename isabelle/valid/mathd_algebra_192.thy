(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_192 imports
  Complex_Main
begin

theorem mathd_algebra_192:
  fixes q e d :: complex
  assumes h0 : "q = Complex 11 (-5)"
    and h1 : "e = Complex 11 5"
    and h2 : "d = Complex 0 2"
  shows "q * e * d = Complex 0 292"
  unfolding assms
  by eval

end