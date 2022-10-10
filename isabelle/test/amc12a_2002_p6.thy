(*
  Authors: Wenda Li
*)

theory amc12a_2002_p6
  imports Complex_Main 
begin

theorem amc12a_2002_p6:
  fixes m ::nat 
  assumes "m>0"
  shows "\<exists> n. (n>0) \<and>  m * n \<le> m + n"
  sorry

end
