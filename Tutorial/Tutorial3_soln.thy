theory tut3_soln
imports
Main

begin

locale Geom =
  fixes on :: "'point \<Rightarrow> 'line \<Rightarrow> bool"
  assumes line_on_two_pts: "a \<noteq> b  \<Longrightarrow> (\<exists>l. on a l \<and> on b l)" 
  and line_on_two_pts_unique: 
           "\<lbrakk> a \<noteq> b; on a l; on b l; on a m; on b m \<rbrakk> \<Longrightarrow> l = m"
  and two_points_on_line: "\<exists>a b. a \<noteq> b \<and> on a l \<and> on b l"
  and three_points_not_on_line: "\<exists>a b c. a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c \<and> 
                                    \<not> (\<exists>l. on a l \<and> on b l \<and> on c l)"
begin
thm Geom_def      

(* i *)
lemma exists_pt_not_on_line_apply: "\<forall>l.  \<exists>x. \<not> on x l"
  apply (rule allI)
  apply (cut_tac three_points_not_on_line)
  apply (erule exE)+
  apply (erule conjE)+  
  apply (rule ccontr)
  apply (erule_tac P="\<exists>l. on a l \<and> on b l \<and> on c l" in notE)
  apply (rule_tac x=l in exI)
  apply (rule conjI)
  apply (rule ccontr)
  apply (erule_tac P="\<exists> x. \<not> on x l" in notE)
  apply (rule_tac x=a in exI)
   apply assumption
  apply (rule conjI)
  apply (rule ccontr)
  apply (erule_tac P="\<exists> x. \<not> on x l" in notE)
   apply (rule_tac x=b in exI)
   apply assumption
  apply (rule ccontr)
  apply (erule_tac P="\<exists> x. \<not> on x l" in notE)
   apply (rule_tac x=c in exI)
  apply assumption
  done

(* ii *)

lemma t02_2: "\<not>(\<exists> x. P x) \<Longrightarrow> \<forall> x. \<not>P x" 
  apply (rule allI)
  apply (rule notI)
  apply (erule notE)
  apply (rule_tac x="x" in exI)
  by assumption

lemma nneq: "\<not> x \<noteq> y \<Longrightarrow> x = y"
  apply (rule ccontr)
  apply (erule notE)
  by assumption

lemma ex_distinct_point: "\<forall>x :: 'point. \<exists>z. z \<noteq> x"
  apply (rule allI)
  apply (rule ccontr)
  apply (drule t02_2)
  apply (cut_tac two_points_on_line)
  apply (erule exE)
  apply (erule exE)
  apply (erule conjE)
  apply (erule_tac P="a = b" in notE)
  apply (frule_tac x="a" in spec)
  apply (drule nneq)
  apply (frule_tac x="b" in spec)
  apply (drule nneq)
  apply (erule ssubst) (* Substitution of equivalents *)
  apply (rule sym) (* Symmetry of equality *)
  by assumption

lemma not_on_line_neq: "\<not> on a l \<Longrightarrow> on b l \<Longrightarrow> a \<noteq> b"
  apply (rule ccontr)
  apply (drule nneq)
  apply (cut_tac t="a" and s="b" and P="\<lambda>b. on b l" in ssubst) (* Substitution of equivalents *)
    apply assumption
   apply assumption
  apply (rule notE)
  by assumption

lemma lines_disjoint: "on a l \<Longrightarrow> \<not> on a k \<Longrightarrow> l \<noteq> k"
  apply (rule ccontr)
  apply (drule nneq)
  apply (cut_tac t="l" and s="k" and P="\<lambda>k. \<not> on a k" in ssubst) (* Substitution of equivalents *)
    apply assumption
   apply assumption
  apply (rule notE)
  by assumption

lemma two_lines_through_each_point_apply: "\<forall>x. \<exists>l m. on x l \<and> on x m \<and> l \<noteq> m"
  apply (rule allI)
  apply (cut_tac ex_distinct_point)
  apply (erule_tac x="x" in allE)
  apply (erule exE)
  apply (cut_tac a="z" and b="x" in line_on_two_pts)
   apply assumption
  apply (erule exE)
  apply (erule conjE)
  apply (cut_tac exists_pt_not_on_line_apply)
  apply (drule_tac x="l" in spec)
  apply (erule exE)
  apply (cut_tac a="xa" and b="x" in line_on_two_pts)
   apply (erule not_on_line_neq)
   apply assumption
  apply (erule exE)
  apply (erule conjE)
  apply (cut_tac a="xa" and l="la" and k="l" in lines_disjoint)
    apply assumption
   apply assumption
  apply (rule_tac x="la" in exI)
  apply (rule_tac x="l" in exI)
  apply (rule conjI)
   apply assumption
  apply (rule conjI)
   apply assumption
  by assumption

(* iii *)
lemma "\<forall>l m x y. l \<noteq> m \<and> on x l \<and> on x m \<and> on y l \<and> on y m \<longrightarrow> x = y"
  apply (rule allI)+
  apply (rule impI)
  apply (erule conjE)+
  apply (rule ccontr)
  apply (cut_tac a="x" and b="y" and l="l" and m="m" in line_on_two_pts_unique)
       apply (assumption)+
  apply (erule notE)
  by assumption

end

(* Not asked for in tutorial: An extension of the locale with a new definition 
   using the "in" keyword *)

definition (in Geom) 
  collinear :: "'point \<Rightarrow> 'point \<Rightarrow> 'point \<Rightarrow> bool" 
  where "collinear a b c \<equiv> \<exists>l. on a l \<and> on b l \<and> on c l"


end
