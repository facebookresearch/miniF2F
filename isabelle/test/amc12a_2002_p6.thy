(*
  Authors: Wenda Li
*)

theory amc12a_2002_p6
  imports Complex_Main 
begin

theorem amc12a_2002_p6:
  fixes n ::nat 
  assumes "n>0"
  shows "\<exists> m. (m>0) \<and>  n * m \<le> n + m"
  sorry

end
