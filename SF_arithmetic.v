
(**********************************************************************)
(* This Program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(**********************************************************************)
(*                        SF-Calculus                                 *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *) 
(* Lambda Calculus from Project Coq                                   *) 
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                     Matching.v                                     *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import ArithRing.
Require Import Max. 
Require Import Test.
Require Import General. 
Require Import SF_Terms.
Require Import SF_Tactics.
Require Import Substitution_term.
Require Import SF_reduction.
Require Import SF_Normal.
Require Import SF_Closed.
Require Import SF_Eval.
Require Import Star.
Require Import Equal.
Require Import Extensions.


(* arithmetic *) 

Fixpoint church n := 
match n with 
| 0 => s_op
| S k => App s_op (church k)
end.

Definition zero:= s_op.
Definition succ:= App s_op.
Definition plus_fn := (star (star (
App (App (App (Op Fop) (Ref 0)) i_op) 
    (App k_op (star (star (App s_op (App (App (Ref 3) (Ref 1)) (Ref 0))))))))).
Definition plus := fix_comb plus_fn . 

Lemma plus_check: forall m n, sf_red (App (App plus (church m)) (church n)) (church (m+n)).
Proof.
induction m; split_all. unfold_op. 
(* 2 *) 
apply transitive_red with 
(App (App (App plus_fn (fix_comb plus_fn)) (Op Sop)) (church n)) . 
eapply2 preserves_app_sf_red. 
eapply2 fix_comb_fix.
unfold plus_fn at 1; unfold_op.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_beta2. auto. 
unfold subst, subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst, subst_rec; fold subst_rec. eval_SF0. eval_SF0. 
(* 1 *) 
apply transitive_red with 
(App (App (App plus_fn (fix_comb plus_fn)) (App s_op (church m))) (church n)). 
eapply2 preserves_app_sf_red. 
eapply2 fix_comb_fix.
unfold plus_fn at 1; unfold_op. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_beta2. auto. 
unfold subst, subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst, subst_rec; fold subst_rec. rewrite lift_rec_null_term. 
rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null_term. 
repeat eval_SF0. eapply2 preserves_app_sf_red. 
insert_Ref_out. rewrite lift_rec_null_term. 
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. 
eval_SF0.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eval_SF0.  eval_SF0. eval_SF0. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. auto. 
eapply transitive_red. eval_SF0.  
eapply transitive_red. eval_SF0.  
eapply transitive_red. eval_SF0.  
eapply transitive_red. eval_SF0.  
eapply transitive_red. eval_SF0.  auto. 
eapply transitive_red. eval_SF0.  
eapply transitive_red. eval_SF0.  
eapply transitive_red. eval_SF0.  
eapply transitive_red. eval_SF0.  
eapply transitive_red. eval_SF0.  auto. 
eapply2 IHm. 
Qed. 

Definition lteq_fn := star (star (
App (App (App (Op Fop) (Ref 0)) (App k_op k_op))
    (App k_op (star (star (App (App (App f_op (Ref 0)) (App k_op i_op))
                               (App k_op (star (App (App (Ref 4) (Ref 2)) (Ref 0)))))))))).
Definition lteq := fix_comb lteq_fn .


Lemma maxvar_lteq: maxvar lteq = 0. 
Proof. unfold lteq; split_all. Qed. 

Lemma lteq_check : forall m n, m<= n -> sf_red (App (App lteq (church m)) (church n)) k_op.
Proof.
  induction m; split_all; unfold lteq. eapply transitive_red. eapply preserves_app_sf_red. 
  apply transitive_red with 
(App (App lteq_fn (fix_comb lteq_fn)) s_op).
eapply2 fix_comb_fix.
unfold lteq_fn at 1; unfold_op.
eapply2 star_beta2. auto. 
unfold_op; unfold subst, subst_rec; fold subst_rec. 
insert_Ref_out. unfold subst, subst_rec; fold subst_rec. 
eval_SF0.
(* 1 *)
eapply transitive_red. eapply preserves_app_sf_red. 
  apply transitive_red with 
(App (App lteq_fn (fix_comb lteq_fn)) (App s_op (church m))).
eapply2 fix_comb_fix.
unfold lteq_fn at 1; unfold_op.
eapply2 star_beta2. auto. 
unfold_op; unfold subst, subst_rec; fold subst_rec. 
insert_Ref_out. unfold subst, subst_rec; fold subst_rec. 
rewrite lift_rec_null_term. rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null_term.
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply preserves_app_sf_red. auto.
eval_SF0. eval_SF0. eval_SF0.
replace n with (S (pred n)) by omega. unfold church; fold church. unfold_op.
eapply succ_red. eapply2 f_compound_red. simpl. 
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. insert_Ref_out. rewrite lift_rec_null. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. eval_SF0.
eval_SF0. eval_SF0.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. auto.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. auto.  eapply2 IHm. omega.
Qed.

 Lemma lteq_check2 : forall m n, m < n -> sf_red (App (App lteq (church n)) (church m)) (App k_op i_op).
Proof.
  induction m; split_all; unfold lteq. 
  eapply transitive_red. eapply preserves_app_sf_red.
  replace n with (S (pred n)) by omega. simpl. unfold_op. 
  apply transitive_red with 
(App (App lteq_fn (fix_comb lteq_fn)) (App (Op Sop) (church (pred n)))).
eapply2 fix_comb_fix.
unfold lteq_fn at 1; unfold_op.
eapply transitive_red.
eapply2 star_beta2. 
eapply subst_preserves_sf_red. eapply subst_preserves_sf_red. eval_SF0.
instantiate(1:=(lift 1 (App (Op Sop) (church (pred n))))). 
auto. 
auto. 
auto.
unfold subst, subst_rec; fold subst_rec. insert_Ref_out. rewrite lift_rec_null_term.
unfold subst, subst_rec; fold subst_rec. rewrite subst_rec_lift_rec; try omega.
rewrite lift_rec_null_term.
eapply transitive_red. eapply preserves_app_sf_red.
eapply succ_red. eapply2 f_compound_red. 
eval_SF0. auto. eval_SF0. eval_SF0. eval_SF0.  eval_SF0.  eval_SF0. 
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eapply preserves_app_sf_red. auto. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
 eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
 eapply preserves_app_sf_red. eapply preserves_app_sf_red. auto. eval_SF0. eval_SF0. eval_SF0.
 eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
 eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eapply preserves_app_sf_red. auto. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
(* 1 *)
  eapply transitive_red. eapply preserves_app_sf_red.
  replace n with (S (pred n)) by omega. simpl. unfold_op. 
  apply transitive_red with 
(App (App lteq_fn (fix_comb lteq_fn)) (App (Op Sop) (church (pred n)))).
eapply2 fix_comb_fix.
unfold lteq_fn at 1; unfold_op.
eapply transitive_red.
eapply2 star_beta2. 
eapply subst_preserves_sf_red. eapply subst_preserves_sf_red. eval_SF0.
instantiate(1:=(lift 1 (App (Op Sop) (church (pred n))))). 
auto. 
auto. 
auto.
unfold subst, subst_rec; fold subst_rec. insert_Ref_out. rewrite lift_rec_null_term.
unfold subst, subst_rec; fold subst_rec. rewrite subst_rec_lift_rec; try omega.
rewrite lift_rec_null_term.
eapply transitive_red. eapply preserves_app_sf_red.
eapply succ_red. eapply2 f_compound_red. 
eval_SF0. auto. eval_SF0. eval_SF0. eval_SF0.  eval_SF0.  eval_SF0. 
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
 eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
 eval_SF0. eval_SF0. eval_SF0. 
 insert_Ref_out.  rewrite lift_rec_null_term.
 eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
auto.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. eapply transitive_red. eval_SF0.
auto.
eapply2 IHm.  omega.
Qed.



Definition size_fn :=  (star (
extension (App (Ref 1) (Ref 0)) (App (App plus (App (Ref 2) (Ref 1))) (App (Ref 2) (Ref 0))) 
(App k_op k_op))).
Definition size := fix_comb size_fn. 

Lemma size_compound: 
forall M, compound M -> 
          sf_red (App size M) 
                (App (App plus (App size (left_component M))) (App size (right_component M))).
Proof. 
intros. 
unfold size. 
apply transitive_red with 
(App (App size_fn (fix_comb size_fn)) M).
eapply2 fix_comb_fix.
unfold size_fn at 1; unfold_op.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 star_beta. auto. 
unfold_op; unfold extension, subst, subst_rec; fold subst_rec. 
unfold_op; unfold extension, subst, subst_rec; fold subst_rec. 
unfold case. 
eapply succ_red. eapply2 s_red. 
rewrite fold_subst.
eapply transitive_red. eapply preserves_app_sf_red. 
2: eval_SF0. 
eapply subst_preserves_sf_red.
eapply2 star_beta. auto.
unfold subst, subst_rec; fold subst_rec. insert_Ref_out. rewrite lift_rec_null_term. 
rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null_term.
unfold_op; rewrite subst_rec_closed; auto.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. red. 
match goal with 
| |- multi_step sf_red1 (App (App (App (Op Fop) ?M) _) ?N) _ => 
apply succ_red with (App (App N (left_component M)) (right_component M))
end. 
auto. 
repeat (rewrite subst_rec_lift_rec; try omega). 
rewrite lift_rec_null_term.
rewrite fold_subst. 
unfold subst. rewrite fold_subst.
eapply subst_preserves_sf_red.
eapply2 star_beta2.
auto. unfold swap; simpl. insert_Ref_out. rewrite lift_rec_null_term.
rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null_term. auto.
auto.
unfold subst, subst_rec; fold subst_rec.
repeat (rewrite subst_rec_lift_rec; try omega). rewrite lift_rec_null_term.
rewrite fold_subst. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply preserves_app_sf_red. eapply subst_preserves_sf_red.
eapply2 star_beta. auto. auto.
insert_Ref_out. rewrite lift_rec_null_term.
rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null_term.
rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null_term. auto.
auto. auto. auto. 
unfold subst, subst_rec; fold subst_rec.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply succ_red. eapply f_op_red. auto. auto. auto. auto. auto. auto. 
rewrite fold_subst. rewrite fold_subst. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply preserves_app_sf_red. eapply subst_preserves_sf_red. eapply subst_preserves_sf_red.
eapply2 star_beta. 
insert_Ref_out. simpl. insert_Ref_out. rewrite lift_rec_null_term.
rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null_term.
auto. auto. auto. auto. auto. 
unfold subst, subst_rec; fold subst_rec.
repeat (rewrite (subst_rec_closed plus); [| unfold plus, plus_fn; auto]). 
insert_Ref_out. simpl. insert_Ref_out. repeat rewrite lift_rec_null_term.
eval_SF0.
rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null_term.
rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null_term.
rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null_term.
auto. 
Qed.


Fixpoint numerical_rank M :=
  match M with
    | Ref _ => 1
    | Op _ => 1
    | App _ M2 => S(numerical_rank M2)
  end
    .

Lemma numerical_rank_positive:  forall M, numerical_rank M > 0.
    Proof. induction M; split_all. Qed. 

Lemma lteq_true:
  forall M N, program M -> program N -> numerical_rank M <= numerical_rank N -> 
              sf_red (App (App lteq M) N) k_op. 
Proof.
  induction M; split_all.
  (* 3 *)
  inversion H; simpl in *; discriminate. 
  (* 2 *)
  unfold lteq. eapply transitive_red. eapply preserves_app_sf_red. 
  eapply2 fix_comb_fix. auto. 
  unfold lteq_fn. 
  eapply transitive_red. eapply preserves_app_sf_red.
  eapply2 star_beta2. auto. 
  unfold subst, subst_rec; fold subst_rec. 
  insert_Ref_out. unfold_op. unfold subst_rec; fold subst_rec. 
  eval_SF0.
  (* 1 *)
  unfold lteq. eapply transitive_red. eapply preserves_app_sf_red. 
  eapply2 fix_comb_fix. auto. 
  unfold lteq_fn. 
  eapply transitive_red. eapply preserves_app_sf_red.
  eapply2 star_beta2. auto. 
  unfold subst, subst_rec; fold subst_rec. 
  insert_Ref_out. unfold_op. unfold subst_rec; fold subst_rec. 
  repeat rewrite lift_rec_null.
  repeat (rewrite subst_rec_lift_rec; try omega). 
  repeat rewrite lift_rec_null.
  eapply transitive_red. eapply preserves_app_sf_red.
  eapply succ_red. eapply2 f_compound_red.
  assert(factorable (App M1 M2)) by eapply2 programs_are_factorable. inversion H2; auto.
  split_all.
  eapply transitive_red. eapply preserves_app_sf_red.
  eapply succ_red. eapply2 f_op_red.
  auto. auto. auto. auto.
  repeat rewrite fold_subst. unfold subst. repeat rewrite fold_subst.
  replace (multi_step sf_red1) with sf_red by auto.
  eapply transitive_red. repeat eapply subst_preserves_sf_red. 
  eapply2 star_beta2. auto. auto. 
  unfold subst, subst_rec; fold subst_rec.
  insert_Ref_out. unfold subst_rec; fold subst_rec. 
  repeat (rewrite subst_rec_lift_rec; try omega).  repeat rewrite lift_rec_null. 
  repeat (rewrite subst_rec_lift_rec; try omega).  repeat rewrite lift_rec_null. 
  repeat (rewrite subst_rec_lift_rec; try omega).  repeat rewrite lift_rec_null. 
  repeat (rewrite subst_rec_lift_rec; try omega).  repeat rewrite lift_rec_null.
  generalize H0 H1; clear H0 H1; case N; intros. 
  (* 3 *)
  inversion H0. simpl in H3; discriminate. 
  (* 2 *)
  simpl in H1. assert(numerical_rank M2 >0) by eapply2 numerical_rank_positive. noway. 
  (* 1 *)
  eapply succ_red. eapply2 f_compound_red.
  assert(factorable (App s s0)) by eapply2 programs_are_factorable. 
  inversion H2; split_all.
  eapply transitive_red. eapply preserves_app_sf_red.
  eapply succ_red. eapply2 f_op_red. auto. split_all. 
  repeat rewrite fold_subst. 
  eapply transitive_red. repeat eapply subst_preserves_sf_red.
  eapply2 star_beta. 
  inversion H0. repeat rewrite lift_rec_closed; auto. 
  inversion H. simpl in H3; max_out. simpl.
  repeat rewrite lift_rec_closed; auto.
  inversion H. simpl in H3; max_out. simpl.
  repeat rewrite lift_rec_closed; auto.
  auto. 
  unfold subst, subst_rec; fold subst_rec. 
  insert_Ref_out.  unfold subst, subst_rec; fold subst_rec.
  insert_Ref_out.  unfold subst, subst_rec; fold subst_rec.
  insert_Ref_out.  unfold subst, subst_rec; fold subst_rec.
  insert_Ref_out.  unfold subst, subst_rec; fold subst_rec.
  insert_Ref_out.  unfold subst, subst_rec; fold subst_rec.
  repeat (rewrite subst_rec_lift_rec; try omega).  repeat rewrite lift_rec_null. 
  repeat (rewrite subst_rec_lift_rec; try omega).  repeat rewrite lift_rec_null. 
  repeat (rewrite subst_rec_lift_rec; try omega).  repeat rewrite lift_rec_null. 
  repeat (rewrite subst_rec_lift_rec; try omega).  repeat rewrite lift_rec_null. 
  repeat (rewrite subst_rec_lift_rec; try omega).  repeat rewrite lift_rec_null. 
  inversion H.  simpl in H3; max_out.
  repeat (rewrite subst_rec_closed; try omega).
  replace (fix_comb
              (star
                 (star
                    (App
                       (App (App (Op Fop) (Ref 0))
                          (App (App (Op Fop) (Op Fop))
                             (App (Op Fop) (Op Fop))))
                       (App (App (Op Fop) (Op Fop))
                          (star
                             (star
                                (App
                                   (App (App (Op Fop) (Ref 0))
                                      (App (App (Op Fop) (Op Fop))
                                         (App
                                            (App (Op Sop)
                                               (App (Op Fop) (Op Fop)))
                                            (App (Op Fop) (Op Fop)))))
                                   (App (App (Op Fop) (Op Fop))
                                      (star
                                         (App (App (Ref 4) (Ref 2)) (Ref 0))))))))))))
          with lteq by auto. 
eapply2 IHM2. 
inversion H.   simpl in H6. max_out. unfold program; inversion H3; auto.
inversion H0.   simpl in H6. max_out. unfold program; inversion H3; auto.
simpl in *. omega.
Qed.


Lemma lteq_false:
  forall M N, program M -> program N -> numerical_rank M > numerical_rank N -> 
              sf_red (App (App lteq M) N) (App k_op i_op). 
Proof.
  induction M; split_all.
  (* 3 *)
  inversion H; simpl in *; discriminate. 
  (* 2 *)
  assert(factorable N) by eapply2 programs_are_factorable. 
  inversion H2; split_all; subst; simpl in *. noway.
  inversion H3; subst; simpl in *; noway.
  (* 1 *)
  assert(factorable N) by eapply2 programs_are_factorable. 
  unfold lteq. eapply transitive_red. eapply preserves_app_sf_red. 
  eapply2 fix_comb_fix. auto. 
  unfold lteq_fn. 
  eapply transitive_red. eapply preserves_app_sf_red.
  eapply2 star_beta2. auto. 
  unfold subst, subst_rec; fold subst_rec. 
  insert_Ref_out. unfold_op. unfold subst_rec; fold subst_rec. 
  repeat rewrite lift_rec_null.
  repeat (rewrite subst_rec_lift_rec; try omega). 
  repeat rewrite lift_rec_null.
  eapply transitive_red. eapply preserves_app_sf_red.
  eapply succ_red. eapply2 f_compound_red.
  assert(factorable (App M1 M2)) by eapply2 programs_are_factorable. inversion H3; auto.
  split_all.
  eapply transitive_red. eapply preserves_app_sf_red.
  eapply succ_red. eapply2 f_op_red.
  auto. auto. auto. auto.
  repeat rewrite fold_subst. unfold subst. repeat rewrite fold_subst.
  replace (multi_step sf_red1) with sf_red by auto.
  eapply transitive_red. repeat eapply subst_preserves_sf_red. 
  eapply2 star_beta2. auto. auto. 
  unfold subst, subst_rec; fold subst_rec.
  insert_Ref_out. unfold subst_rec; fold subst_rec.
  repeat rewrite lift_rec_null.
  repeat (rewrite subst_rec_lift_rec; try omega). 
  repeat rewrite lift_rec_null.
  repeat (rewrite subst_rec_lift_rec; try omega). 
  repeat rewrite lift_rec_null.
  repeat (rewrite subst_rec_lift_rec; try omega). 
  repeat rewrite lift_rec_null.
  (* 1 *)
  inversion H2.  inversion H3; subst.
  eapply succ_red. eapply2 f_op_red. auto. 
  eapply succ_red. eapply2 f_compound_red.
  eapply transitive_red. eapply preserves_app_sf_red.
  eapply succ_red. eapply2 f_op_red. auto. auto.
  repeat rewrite fold_subst. 
  replace (multi_step sf_red1) with sf_red by auto.
  eapply transitive_red. repeat eapply subst_preserves_sf_red. 
  eapply2 star_beta.
  inversion H0. repeat (rewrite lift_rec_closed); auto.
  inversion H. simpl in H5; max_out. simpl.
  repeat rewrite lift_rec_closed; auto.
  inversion H. simpl in H5; max_out. simpl.
  repeat rewrite lift_rec_closed; auto.
  auto. 
  unfold subst, subst_rec; fold subst_rec. 
  insert_Ref_out.  unfold subst, subst_rec; fold subst_rec.
  insert_Ref_out.  unfold subst, subst_rec; fold subst_rec.
  insert_Ref_out.  unfold subst, subst_rec; fold subst_rec.
  insert_Ref_out.  unfold subst, subst_rec; fold subst_rec.
  insert_Ref_out.  unfold subst, subst_rec; fold subst_rec.
  repeat (rewrite subst_rec_lift_rec; try omega).  repeat rewrite lift_rec_null. 
  repeat (rewrite subst_rec_lift_rec; try omega).  repeat rewrite lift_rec_null. 
  repeat (rewrite subst_rec_lift_rec; try omega).  repeat rewrite lift_rec_null. 
  repeat (rewrite subst_rec_lift_rec; try omega).  repeat rewrite lift_rec_null. 
  repeat (rewrite subst_rec_lift_rec; try omega).  repeat rewrite lift_rec_null. 
  inversion H.  simpl in H5; max_out.
  repeat (rewrite subst_rec_closed; try omega).
  replace (fix_comb
              (star
                 (star
                    (App
                       (App (App (Op Fop) (Ref 0))
                          (App (App (Op Fop) (Op Fop))
                             (App (Op Fop) (Op Fop))))
                       (App (App (Op Fop) (Op Fop))
                          (star
                             (star
                                (App
                                   (App (App (Op Fop) (Ref 0))
                                      (App (App (Op Fop) (Op Fop))
                                         (App
                                            (App (Op Sop)
                                               (App (Op Fop) (Op Fop)))
                                            (App (Op Fop) (Op Fop)))))
                                   (App (App (Op Fop) (Op Fop))
                                      (star
                                         (App (App (Ref 4) (Ref 2)) (Ref 0))))))))))))
          with lteq by auto. 
  eapply2 IHM2.
  (* 3 *) 
inversion H.   simpl in H8. max_out. unfold program; inversion H5; auto.
(* 2 *)
inversion H0. 
inversion H3; subst. simpl in *. inversion H5; unfold program; split_all.
simpl in H8. max_out. inversion H5; unfold program; split_all.
inversion H3; subst; simpl in *; split_all; omega. 
Qed.



Lemma plus_zero: forall o M, sf_red (App (App plus (Op o)) M) M.
Proof.
  intros. eapply transitive_red. eapply preserves_app_sf_red. 
 unfold plus. eapply2 fix_comb_fix. auto. 
unfold plus_fn at 1.   eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 star_beta2. auto. unfold subst, subst_rec; fold subst_rec. 
insert_Ref_out. unfold_op; unfold subst_rec; fold subst_rec. 
eval_SF0. eval_SF0. 
Qed. 



Lemma program_church: forall i, program (church i).
Proof.  induction i; split_all; unfold_op; split_all; inversion IHi; auto. Qed.

Hint Resolve program_church. 

Lemma church_monotonic: forall k i,  church k = church i -> k = i.
Proof.
  induction k; split_all. gen_case H i. discriminate. 
  gen_case H i. discriminate. inversion H. 
assert (k = n) by eapply2 IHk.   auto. 
Qed.
