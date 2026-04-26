(* SPDX-License-Identifier: PMPL-1.0-or-later *)
theory Tropical_Ordinal_Bridge
  imports Tropical_Ordinal Tropical_v2
begin

text \<open>
  Rung 1 \<sim>1.5: bridge between the generic ordinal-coefficient lift
  (\<open>Tropical_Ordinal\<close>) and the concrete \<open>nat\<close>-coefficient version
  (\<open>Tropical_v2\<close>). The bijection lets every theorem of \<open>Tropical_v2\<close>
  be re-derived as a corollary of the generic lift, justifying the
  whole-ladder strategy of working at the abstract level.
\<close>

fun nat_to_tropO :: "tropical \<Rightarrow> nat trop_o" where
  "nat_to_tropO NegInf  = NegInfO"
| "nat_to_tropO (Fin n) = FinO n"

fun tropO_to_nat :: "nat trop_o \<Rightarrow> tropical" where
  "tropO_to_nat NegInfO  = NegInf"
| "tropO_to_nat (FinO n) = Fin n"

lemma nat_tropO_inverse [simp]:
  "tropO_to_nat (nat_to_tropO x) = x"
  by (cases x) simp_all

lemma tropO_nat_inverse [simp]:
  "nat_to_tropO (tropO_to_nat x) = x"
  by (cases x) simp_all

lemma nat_to_tropO_add:
  "nat_to_tropO (trop_add a b) = tropO_add (nat_to_tropO a) (nat_to_tropO b)"
  by (cases a; cases b) simp_all

lemma nat_to_tropO_mul:
  "nat_to_tropO (trop_mul a b) = tropO_mul (nat_to_tropO a) (nat_to_tropO b)"
  by (cases a; cases b) simp_all

end
