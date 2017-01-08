
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
(*                  SF-Calculus                                       *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *) 
(* Lambda Calculus from Project Coq                                   *) 
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                   Substituting.v                                   *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import ArithRing.
Require Import List.
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
Require Import SF_arithmetic.
Require Import Lifting.


Lemma maxvar_lift: forall M k, maxvar M > 0 -> maxvar(lift k M) = maxvar M + k. 
Proof. 
induction M; split_all. relocate_lt. omega. noway. 
unfold lift in *.
assert(maxvar M1 = 0 -> maxvar (lift_rec M1 0 k) = 0)
by (split_all;  rewrite lift_rec_closed; auto).   
assert(maxvar M2 = 0 -> maxvar (lift_rec M2 0 k) = 0)
by (split_all;  rewrite lift_rec_closed; auto).   
gen3_case IHM1 H H0 (maxvar M1); gen3_case IHM2 H H1 (maxvar M2); try noway. 
rewrite H0; try omega;  rewrite IHM2; simpl; omega. 
rewrite H1; try omega.   rewrite IHM1; simpl.  omega. omega. 
rewrite IHM1; try omega; rewrite IHM2; try omega. 
rewrite <- max_succ. rewrite <- max_plus. auto. 
Qed. 

Definition predecessor i := App (App (App f_op i) i) (App k_op i_op). 

Definition insert_Ref_comb i N M :=
  (* from subst_rec (var i M) N *) 
  App (App (App f_op i) (App (App fold_app N) M)) 
      (App k_op (App k_op (var (predecessor i) M)))
.


Lemma maxvar_insert_Ref_comb: forall i N M, 
maxvar (insert_Ref_comb i N M) = maxvar (App i (App N M)). 
Proof. 
assert(maxvar fold_app = 0). 
unfold fold_app; split_all. 
intros; unfold insert_Ref_comb, predecessor. 
rewrite maxvar_app. rewrite maxvar_app. rewrite maxvar_app. rewrite maxvar_app. 
rewrite maxvar_app. rewrite H. rewrite maxvar_app. rewrite maxvar_app.  
rewrite maxvar_var. unfold_op; split_all. 
assert(max (max (maxvar i) (max (maxvar N) (maxvar M)))
     (max (max (max (maxvar i) (maxvar i)) 0) (maxvar M)) >=
   max (maxvar i) (max (maxvar N) (maxvar M)))
by max_l. 
assert(max (maxvar i) (max (maxvar N) (maxvar M)) >= 
       max (max (maxvar i) (max (maxvar N) (maxvar M)))
     (max (max (max (maxvar i) (maxvar i)) 0) (maxvar M))). 
eapply2 max_max2. rewrite max_zero. 
eapply2 max_max2. eapply2 max_max2; max_l. max_r. max_r. 
omega. 
Qed. 



Lemma subst_rec_preserves_insert_Ref_comb: 
forall i M N k1 N1, 
subst_rec (insert_Ref_comb i N M) N1 k1 = 
insert_Ref_comb (subst_rec i N1 k1) (subst_rec N N1 k1) (subst_rec M N1 k1). 
Proof. 
intros; unfold insert_Ref_comb. unfold_op; unfold subst_rec; fold subst_rec. 
rewrite (subst_rec_closed fold_app). 
2: unfold fold_app, fold_app_fn; rewrite maxvar_fix_comb; repeat rewrite maxvar_star; simpl; omega.
rewrite subst_rec_preserves_var. 
unfold predecessor; split_all. 
Qed. 

Definition swap_vars s M := App (lambda_term s (App (App (App lift_rec_comb s) M) 
                                                    (church 2)))
                                (var (church 1) s_op). 

Definition subst_rec_comb_fn :=   (* abs = fix \s.\M.\N.... *) 
  star(extension (var (Ref 1) (Ref 0))
                 (star (insert_Ref_comb (Ref 2) (Ref 0) (App (App (Ref 3) (Ref 1)) (Ref 0))))
      (extension (lambda_term (Ref 1) (Ref 0))                           
                 (star(App(App(App(App equal_comb (Ref 3)) (Ref 2))
                              (lambda_term (Ref 2) 
                                           (App(lambda_term (Ref 2)
                                                            (swap_vars (Ref 3) (Ref 1)))
                                               (App (App(App lift_rec_comb (Ref 3))
                                                        (Ref 0)) s_op))))
                          (lambda_term (App(App(Ref 3)(Ref 2))(Ref 0))
                                       (App(App(Ref 3)(Ref 1))(Ref 0)))))   
       (star(App(App (App f_op (Ref 0)) (App k_op (Ref 0)))
                (star(star(App(App s_op (App(Ref 3)(Ref 1)))
                              (App(Ref 3)(Ref 0)))))))))
.

Definition subst_rec_comb := fix_comb (subst_rec_comb_fn).
Definition abs M := app_comb subst_rec_comb M . 




Lemma maxvar_subst_rec_comb: maxvar subst_rec_comb = 0. 
Proof. 
unfold subst_rec_comb. rewrite maxvar_fix_comb. 
unfold subst_rec_comb_fn, lambda_term. 
rewrite maxvar_star. rewrite maxvar_extension. rewrite maxvar_star at 1. 
rewrite maxvar_insert_Ref_comb at 1. 
rewrite maxvar_extension. rewrite maxvar_star at 1. 
unfold maxvar at 1; fold maxvar. 
rewrite maxvar_app at 1. rewrite maxvar_app at 1. 
rewrite maxvar_app at 1. rewrite maxvar_app at 1. 
rewrite maxvar_equal_comb at 1. 
rewrite maxvar_app_comb at 1. rewrite maxvar_app at 1. rewrite maxvar_app at 1. 
rewrite maxvar_app_comb at 1. 
rewrite maxvar_app at 1. unfold swap_vars, lambda_term. rewrite maxvar_app at 1. 
rewrite maxvar_app_comb at 1. 
rewrite maxvar_app at 1. rewrite maxvar_app at 1.  
rewrite maxvar_app at 1. rewrite maxvar_app at 1.  
rewrite maxvar_lift_rec_comb. 
rewrite maxvar_app at 1. rewrite maxvar_app at 1.  
rewrite maxvar_app at 1. 
rewrite maxvar_lift_rec_comb. 
rewrite maxvar_star at 1.
split_all. 
Qed. 

Lemma normal_subst_rec_comb: normal subst_rec_comb.
Proof.
  unfold subst_rec_comb. eapply fix_comb_normal. unfold subst_rec_comb_fn. eapply2 star_normal.
Qed.

Hint Resolve maxvar_subst_rec_comb normal_subst_rec_comb. 

Proposition subst_rec_comb_op :
  forall N o, sf_red (App (App subst_rec_comb (Op o)) N) (Op o). 
Proof.
  intros. eapply transitive_red. eapply preserves_app_sf_red.  
   unfold subst_rec_comb.
   eapply2 fix_comb_fix. auto. 
   unfold subst_rec_comb_fn at 1.
   eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.  
   eapply2 star_beta. auto. auto. 
   unfold subst. repeat rewrite fold_subst.
   eapply transitive_red. eapply preserves_app_sf_red. 
   repeat eapply subst_preserves_sf_red.
   unfold lift, lift_rec. 
   2: auto. 2: auto. 
   (* 2 *)
   eapply2 extensions_by_matchfail.
   eapply2 matchfail_app_op. 
   unfold_op; repeat eapply2 nf_compound. 
   (* 1 *) 
   eapply transitive_red.  eapply preserves_app_sf_red. repeat eapply subst_preserves_sf_red.
   (* 2 *)
   eapply2 extensions_by_matchfail.
   eapply2 matchfail_app_op. unfold_op; repeat eapply2 nf_compound. auto. auto. 
   (* 1 *)
   eapply transitive_red. eapply preserves_app_sf_red. eapply subst_preserves_sf_red. 
   eapply transitive_red.  eapply2 star_beta. unfold_op; unfold subst, subst_rec; fold subst_rec. 
   insert_Ref_out. eval_SF0. auto. auto.  unfold subst, subst_rec; fold subst_rec. 
   eval_SF0. 
Qed. 


Proposition subst_rec_comb_var :
  forall N i M, sf_red (App (App subst_rec_comb (var i M)) N)
                      (insert_Ref_comb i N (App (App subst_rec_comb M) N)).
Proof.
  intros. eapply transitive_red. eapply preserves_app_sf_red.  
   unfold subst_rec_comb.
   eapply2 fix_comb_fix. auto. 
   unfold subst_rec_comb_fn at 1.
   eapply transitive_red. eapply preserves_app_sf_red.  
   eapply preserves_app_sf_red.   eapply2 star_beta. auto. auto. 
   eapply transitive_red. repeat (unfold subst; rewrite fold_subst). 
   repeat eapply subst_preserves_sf_red. eapply preserves_app_sf_red.  
   2: auto. 2: auto. 
   (* 2 *)
   unfold lift. repeat rewrite lift_rec_preserves_var. 
   eapply2 extensions_by_matching.
   eapply2 var_matching. 
   (* 1 *)
   unfold length; fold length. 
   unfold map; fold map. unfold app; fold app. unfold fold_left; fold fold_left.
   unfold subst. repeat rewrite fold_subst.
  match goal with 
    | |- _ _ (subst_rec ?M ?N 0) _ => 
      replace (subst_rec M N 0) with (subst M N) by auto
  end. 
  eapply transitive_red. repeat (eapply subst_preserves_sf_red). 
  eapply2 star_beta.   auto. auto. auto.
  (* 1 *) 
  unfold subst. repeat (rewrite subst_rec_preserves_insert_Ref_comb). 
  simpl. insert_Ref_out. repeat rewrite lift_rec_null. 
  repeat (rewrite subst_rec_lift_rec; try omega). repeat rewrite lift_rec_null. 
  repeat (rewrite subst_rec_lift_rec; try omega). repeat rewrite lift_rec_null. 
  repeat (rewrite subst_rec_lift_rec; try omega). repeat rewrite lift_rec_null. 
auto. 
Qed. 


Proposition subst_rec_comb_abs :
  forall N M, sf_red (App (App subst_rec_comb (abs M)) N)
                    (abs (App (abs (swap_vars subst_rec_comb M)) 
                              (App (App (App lift_rec_comb subst_rec_comb) N) s_op))). 
Proof.
  intros. unfold abs, lambda_term. 
  eapply transitive_red. eapply preserves_app_sf_red.
   unfold subst_rec_comb. eapply2 fix_comb_fix. auto. 
unfold subst_rec_comb_fn at 1.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.  
eapply2 star_beta. auto. auto. 
unfold subst. repeat rewrite fold_subst. unfold subst. repeat rewrite fold_subst. 
eapply transitive_red. repeat eapply subst_preserves_sf_red. eapply preserves_app_sf_red. 
unfold lift. repeat (rewrite (lift_rec_preserves_app_comb)).
2: auto. 2: auto. 
(* 2 *)
eapply2 extensions_by_matchfail.
unfold var. eapply2 app_comb_matchfail. 
eapply2 matchfail_app_l. 
 eapply2 matchfail_app_r. 
repeat(rewrite lift_rec_closed; try (rewrite maxvar_subst_rec_comb; auto)). 
eapply2 app_comb_matchfail. eapply2 matchfail_app_l.  
eapply2 pattern_is_program3;  unfold program; split_all. discriminate. 
assert(maxvar subst_rec_comb = 0) by eapply2 maxvar_subst_rec_comb. 
unfold subst_rec_comb in H. auto.  
(* 1 *) 
eapply transitive_red. repeat eapply subst_preserves_sf_red. eapply preserves_app_sf_red. 
2: auto. 2: auto. 
eapply2 extensions_by_matching.
unfold lambda_term. 
eapply2 app_comb_matching.   
unfold length, map, app, fold_left. 
unfold subst; repeat rewrite fold_subst. 
  match goal with 
    | |- _ _ (subst_rec ?M ?N 0) _ => 
      replace (subst_rec M N 0) with (subst M N) by auto
  end. 
  eapply transitive_red. repeat (eapply subst_preserves_sf_red). 
eapply2 star_beta. auto. auto. auto. 
(* 1 *) 
unfold subst, subst_rec; fold subst_rec. 
repeat (rewrite (subst_rec_closed equal_comb)). 2: rewrite maxvar_equal_comb; auto. 
repeat (rewrite insert_Ref_gt; [| omega]). 
unfold subst, subst_rec; fold subst_rec. 
repeat (rewrite insert_Ref_gt; [| omega]). 
unfold subst, subst_rec; fold subst_rec. 
repeat (rewrite insert_Ref_gt; [| omega]). 
unfold subst, subst_rec; fold subst_rec. 
repeat (rewrite insert_Ref_eq; [| omega]). 
unfold lift; repeat rewrite lift_rec_null. 
rewrite subst_rec_lift_rec; try omega. 
 rewrite lift_rec_null. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply equal_programs. replace (fix_comb subst_rec_comb_fn) with subst_rec_comb by auto. 
 unfold program; split; auto. auto. auto. 
unfold_op.  eapply succ_red. eapply2 f_op_red. 
unfold lambda_term, swap. 
repeat rewrite subst_rec_preserves_app_comb. 
unfold subst_rec; fold subst_rec. 
repeat rewrite subst_rec_preserves_app_comb. 
unfold subst_rec; fold subst_rec. 
eapply app_comb_preserves_sf_red. 
(* 2 *) 
rewrite insert_Ref_gt; try omega. 
unfold subst_rec; fold subst_rec. 
rewrite insert_Ref_gt; try omega. 
unfold subst_rec; fold subst_rec. 
rewrite insert_Ref_eq; try omega. 
unfold lift; rewrite lift_rec_null. 
rewrite subst_rec_lift_rec; try omega.  rewrite lift_rec_null. 
auto. 
(* 1 *) 
rewrite insert_Ref_gt; try omega. 
unfold subst_rec; fold subst_rec. 
rewrite insert_Ref_gt; try omega. 
unfold subst_rec; fold subst_rec. 
rewrite insert_Ref_eq; try omega. 
unfold lift; rewrite lift_rec_null. 
unfold_op; unfold subst_rec; fold subst_rec. 
rewrite insert_Ref_gt; try omega. 
unfold subst_rec; fold subst_rec. 
rewrite insert_Ref_gt; try omega. 
unfold subst_rec; fold subst_rec. 
rewrite insert_Ref_gt; try omega. 
unfold subst_rec; fold subst_rec. 
rewrite insert_Ref_eq; try omega. 
unfold lift; rewrite lift_rec_null.
rewrite insert_Ref_eq; try omega. 
unfold lift; rewrite lift_rec_null.
  repeat (rewrite subst_rec_lift_rec; try omega). repeat rewrite lift_rec_null. 
  repeat (rewrite subst_rec_lift_rec; try omega). repeat rewrite lift_rec_null. 
  repeat (rewrite subst_rec_lift_rec; try omega). repeat rewrite lift_rec_null. 
rewrite (subst_rec_closed lift_rec_comb) at 1; try (rewrite maxvar_lift_rec_comb; omega).  
rewrite (subst_rec_closed lift_rec_comb) at 1; try (rewrite maxvar_lift_rec_comb; omega).  
rewrite (subst_rec_closed lift_rec_comb) at 1; try (rewrite maxvar_lift_rec_comb; omega).  
rewrite (subst_rec_closed lift_rec_comb) at 1; try (rewrite maxvar_lift_rec_comb; omega).  
eapply2 preserves_app_sf_red. 
eapply2 app_comb_preserves_sf_red. 


Lemma subst_rec_preserves_lambda_term : 
forall M1 M2 N k, subst_rec (lambda_term M1 M2) N k = 
                  lambda_term (subst_rec M1 N k) (subst_rec M2 N k). 
Proof. unfold lambda_term, app_comb; split_all. Qed. 

Lemma subst_rec_preserves_swap_vars: 
forall M1 M2 N k, subst_rec (swap_vars M1 M2) N k = 
                  swap_vars (subst_rec M1 N k) (subst_rec M2 N k). 
Proof. 
unfold swap_vars.  intros. unfold subst_rec; fold subst_rec. 
rewrite subst_rec_preserves_lambda_term. unfold subst_rec; fold subst_rec. 
rewrite (subst_rec_closed lift_rec_comb). 
repeat rewrite subst_rec_preserves_var. 
unfold church; unfold_op; unfold subst_rec; fold subst_rec. split_all. 
rewrite maxvar_lift_rec_comb; omega. 
Qed. 

  repeat (rewrite subst_rec_preserves_swap_vars). unfold subst_rec; fold subst_rec. 
rewrite insert_Ref_gt; try omega. 
unfold subst_rec; fold subst_rec. 
rewrite insert_Ref_gt; try omega. 
unfold subst_rec; fold subst_rec. 
rewrite insert_Ref_gt; try omega. 
unfold subst_rec; fold subst_rec. 
rewrite insert_Ref_eq; try omega. 
unfold lift; rewrite lift_rec_null.
rewrite insert_Ref_gt; try omega. 
unfold subst_rec; fold subst_rec. 
rewrite insert_Ref_eq; try omega. 
unfold lift; rewrite lift_rec_null. 
  repeat (rewrite subst_rec_lift_rec; try omega). repeat rewrite lift_rec_null. 
  repeat (rewrite subst_rec_lift_rec; try omega). repeat rewrite lift_rec_null. 
auto. 
Qed. 



Proposition subst_rec_comb_app :
  forall N M1 M2, compound (App M1 M2) -> 
                      matchfail (var (Ref 1) (Ref 0))  (App M1 M2) -> 
                      matchfail (lambda_term  (Ref 1) (Ref 0)) (App M1 M2) -> 
      sf_red (App (App subst_rec_comb (App M1 M2)) N) 
            (App (App (App subst_rec_comb M1) N)
                 (App (App subst_rec_comb M2) N))
. 
Proof.
  intros. 
  eapply transitive_red. eapply preserves_app_sf_red.  
  unfold subst_rec_comb.
  eapply2 fix_comb_fix. auto. 
  unfold subst_rec_comb_fn at 1.
  eapply transitive_red. eapply preserves_app_sf_red.  
  eapply preserves_app_sf_red.  
  eapply2 star_beta. auto. auto. 
  unfold subst. repeat rewrite fold_subst. unfold subst. repeat rewrite fold_subst. 
  eapply transitive_red.   repeat eapply subst_preserves_sf_red. eapply preserves_app_sf_red.
  2: auto. 2: auto. 
  (* 2 *)
  eapply2 extensions_by_matchfail. 
  repeat eapply2 matchfail_lift.
  (* 1 *) 
  eapply transitive_red. repeat eapply subst_preserves_sf_red. eapply preserves_app_sf_red. 
  2: auto. 2: auto. 
  (* 2 *) 
  apply extensions_by_matchfail. 
  repeat eapply2 matchfail_lift.
  (* 1 *) 
  eapply transitive_red. repeat eapply subst_preserves_sf_red. eapply preserves_app_sf_red. 
  eapply2 star_beta.  auto. auto. 
  eapply transitive_red. repeat eapply subst_preserves_sf_red. eapply preserves_app_sf_red.
  unfold_op; unfold subst, subst_rec; fold subst_rec. insert_Ref_out. 
  repeat rewrite lift_rec_null.
  eapply succ_red. eapply2 f_compound_red. 
  replace (App (lift_rec M1 0 1) (lift_rec M2 0 1))
  with (lift_rec (App M1 M2) 0 1) by auto. 
eapply2 lift_rec_preserves_compound. 
unfold left_component, right_component. 
  rewrite fold_subst. unfold subst;  rewrite fold_subst.
  eapply subst_preserves_sf_red. eapply2 star_beta2. split_all. auto. auto. 
  (* 1 *) 
  unfold subst, subst_rec; fold subst_rec.  
  rewrite insert_Ref_gt; try omega. 
  rewrite insert_Ref_gt; try omega. 
  rewrite insert_Ref_eq; try omega. 
  unfold subst, subst_rec; fold subst_rec.  
  rewrite insert_Ref_gt; try omega. 
  rewrite insert_Ref_eq; try omega. 
  unfold subst, subst_rec; fold subst_rec.  
  rewrite insert_Ref_gt; try omega. 
  unfold lift; repeat rewrite lift_rec_null.
  unfold subst, subst_rec; fold subst_rec.  
  rewrite insert_Ref_eq; try omega. 
  unfold lift; repeat rewrite lift_rec_null.
  repeat (rewrite subst_rec_lift_rec; try omega; repeat rewrite lift_rec_null). 
  eval_SF0. 
Qed. 



(* abstraction *)

Theorem beta: forall M N, sf_red (App (abs M) N) (App (App subst_rec_comb M) N). 
Proof.
intros; unfold abs. eapply transitive_red. eapply2 app_comb_red. eapply2 preserves_app_sf_red. 
Qed.

Theorem xi: forall M N, sf_red M N -> sf_red (abs M) (abs N).
Proof. intros; repeat eapply2 preserves_app_sf_red. Qed. 




Lemma insert_Ref_comb_zero:
 forall N M, sf_red (insert_Ref_comb s_op N M) (App (App fold_app N) M). 
Proof.  intros. unfold insert_Ref_comb. unfold_op; eval_SF0. Qed.

Lemma insert_Ref_comb_succ : 
  forall i M N, sf_red (insert_Ref_comb (church (S i)) N M) (var (church i) M). 
Proof.
  intros.  eapply transitive_red. unfold insert_Ref_comb, church; fold church; unfold_op. 
eapply succ_red. eapply2 f_compound_red. eval_SF0.  
unfold predecessor. eapply var_preserves_sf_red. eval_SF0. eval_SF0. eval_SF0. auto.  
Qed.

