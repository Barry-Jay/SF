
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
(*                      Lifting.v                                     *)
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


Lemma app_comb_preserves_sf_red: 
forall M1 M2 N1 N2, sf_red M1 N1 -> sf_red M2 N2 -> sf_red (app_comb M1 M2) (app_comb N1 N2). 
Proof. split_all; unfold app_comb; unfold_op. repeat eapply2 preserves_app_sf_red. Qed. 

Lemma var_preserves_sf_red: 
forall M1 M2 N1 N2, sf_red M1 N1 -> sf_red M2 N2 -> sf_red (var M1 M2) (var N1 N2). 
Proof. split_all; unfold var; unfold_op. repeat eapply2 app_comb_preserves_sf_red. Qed. 



Hint Resolve vee_normal. 


Definition lambda_term s M := app_comb s M.  

Definition relocate_term n i  := App (App (App (App lteq n) i) (App s_op i)) i.

Definition lift_rec_comb_fn := 
  (* Ref 0 is not bound, but represents the substitution parameter. 
     lifts by 1. l, M n = recursion parameter, index to begin lifting, argument *) 

star(extension(var (Ref 1) (Ref 0))
                   (star (var (relocate_term (Ref 0) (Ref 2))
                              (App (App (Ref 3) (Ref 1)) (Ref 0))))
                   (extension(lambda_term (Ref 1) (Ref 0))
                             (App(App(App (App equal_comb (Ref 3)) (Ref 1))
                                     (star (lambda_term (Ref 2) 
                                                        (App (App (Ref 3) (Ref 1)) 
                                                             (App s_op (Ref 0))))))
                                 (star(lambda_term (App(App(Ref 3)(Ref 2))(Ref 0))
                                                   (App(App(Ref 3)(Ref 1))(Ref 0)))))
                             (star (App (App (App f_op (Ref 0)) (App k_op (Ref 0)))
                                        (star(star(App (App s_op (App(Ref 3)(Ref 1)))
                                                       (App(Ref 3)(Ref 0)))))))))
.

Definition lift_rec_comb := star (fix_comb (lift_rec_comb_fn)). 

Lemma maxvar_lift_rec_comb : maxvar lift_rec_comb = 0.  
Proof. 
unfold lift_rec_comb.
rewrite maxvar_star. rewrite maxvar_fix_comb.
unfold lift_rec_comb_fn, extension.
repeat rewrite maxvar_star.
rewrite maxvar_app at 1. 
rewrite maxvar_app at 1. 
rewrite maxvar_case at 1. rewrite maxvar_star at 1. rewrite maxvar_var at 1. 
assert ((maxvar
                    (App (relocate_term (Ref 0) (Ref 2))
                       (App (App (Ref 3) (Ref 1)) (Ref 0)))) = 4) by split_all. 
rewrite H. 
rewrite maxvar_app at 1. rewrite maxvar_app at 1. rewrite maxvar_app at 1.
rewrite maxvar_case at 1. 
rewrite maxvar_app at 1. rewrite maxvar_app at 1. rewrite maxvar_app at 1.
rewrite maxvar_app at 1.
rewrite maxvar_equal_comb.
rewrite maxvar_star. rewrite maxvar_star. 
rewrite maxvar_app at 1. rewrite maxvar_star. 
split_all. 
Qed. 

Proposition lift_rec_comb_op :
  forall s o n, sf_red (App (App (fix_comb (subst_rec lift_rec_comb_fn s 0)) (Op o)) n) (Op o). 
Proof.
  intros. eapply transitive_red. eapply preserves_app_sf_red.  
  eapply2 fix_comb_fix. auto. 
  unfold lift_rec_comb_fn at 1. 
  unfold subst. rewrite fold_subst.
  eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
  eapply subst_preserves_sf_red.
  eapply2 star_beta.  auto. auto. auto. 
  unfold subst. repeat rewrite fold_subst. 
  eapply transitive_red. eapply preserves_app_sf_red. repeat  eapply subst_preserves_sf_red.
  unfold lift, lift_rec.  
  eapply transitive_red. 
  eapply2 extensions_by_matchfail. unfold var, app_comb; unfold_op. 
  eapply2 matchfail_app_op. repeat eapply2 nf_compound. 
  eapply transitive_red. 
  eapply2 extensions_by_matchfail. unfold lambda_term, app_comb; unfold_op. 
  eapply2 matchfail_app_op. repeat eapply2 nf_compound. 
  eapply2 star_beta. auto. auto. auto. unfold_op.  
  unfold subst, subst_rec; fold subst_rec. insert_Ref_out. 
  unfold subst, subst_rec; fold subst_rec. eval_SF0. 
Qed. 

Proposition lift_rec_comb_op1:
  forall s o n, sf_red (App (App (App lift_rec_comb s) (Op o)) n) (Op o). 
Proof. 
split_all. eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
unfold lift_rec_comb. eapply2 star_beta. auto. auto. eapply2 lift_rec_comb_op. 
Qed. 

Proposition lift_rec_comb_var :
  forall s i M n, sf_red (App (App (App lift_rec_comb s) (var i M)) n)
                        (var (relocate_term n i)
                             (App(App(fix_comb (subst_rec lift_rec_comb_fn s 0)) M) n)). 
Proof.
  intros. eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.
  unfold lift_rec_comb.
  eapply2 star_beta. auto. auto. 
  rewrite subst_preserves_fix_comb. 
  eapply transitive_red. eapply preserves_app_sf_red.  
  eapply2 fix_comb_fix. auto. 
  unfold lift_rec_comb_fn at 1.
  repeat (unfold subst; rewrite fold_subst). 
  eapply transitive_red. eapply subst_preserves_sf_red. eapply preserves_app_sf_red.  
  eapply preserves_app_sf_red. 
  eapply2 star_beta. auto. auto. auto. 
  repeat (unfold subst; rewrite fold_subst). 
  eapply transitive_red.  repeat eapply subst_preserves_sf_red. eapply preserves_app_sf_red. 
  eapply transitive_red. 
  eapply2 extensions_by_matching. 
  unfold lift; repeat rewrite lift_rec_preserves_var. 
  eapply2 var_matching. 
  unfold length, map; fold map. unfold app; fold app. unfold fold_left; fold fold_left.
  auto. auto. auto. auto. 
  repeat (unfold subst; rewrite fold_subst). 
  eapply transitive_red.  repeat eapply subst_preserves_sf_red. 
  eapply2 star_beta. auto. auto. auto. auto. 
  repeat rewrite subst_preserves_var. eapply2 var_preserves_sf_red.


Lemma subst_preserves_relocate_term : 
forall M1 M2 N, subst (relocate_term M1 M2) N = relocate_term (subst M1 N) (subst M2 N). 
Proof. unfold relocate_term, subst. unfold_op; split_all. Qed. 

repeat rewrite subst_preserves_relocate_term. 
unfold subst, subst_rec; fold subst_rec. insert_Ref_out. 
repeat (repeat rewrite lift_rec_null; repeat (rewrite subst_rec_lift_rec; try omega)). 
unfold subst, subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst, subst_rec; fold subst_rec. insert_Ref_out. 
repeat (repeat rewrite lift_rec_null; repeat (rewrite subst_rec_lift_rec; try omega)). 
auto. 
repeat (unfold subst, subst_rec; fold subst_rec; insert_Ref_out). 
repeat (repeat rewrite lift_rec_null; repeat (rewrite subst_rec_lift_rec; try omega)). 
auto. 
Qed. 


Proposition lift_rec_comb_abs :
  forall s n M, program s -> matchfail (app_comb vee (Ref 1)) s -> 
                sf_red (App (App (App lift_rec_comb s) (lambda_term s M)) n)
                      (lambda_term s 
                                   (App
                                      (App (fix_comb (subst_rec lift_rec_comb_fn s 0))
                                           M) (App (Op Sop) n))). 
Proof.
  intros. inversion H. 
  eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.
  unfold lift_rec_comb.
  eapply2 star_beta. auto. auto. 
  rewrite subst_preserves_fix_comb. 
  eapply transitive_red. eapply preserves_app_sf_red.  
  eapply2 fix_comb_fix. auto. 
  unfold lift_rec_comb_fn at 1.
  repeat (unfold subst; rewrite fold_subst). 
  eapply transitive_red. eapply subst_preserves_sf_red.
  eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
  eapply2 star_beta.  auto. auto. auto.   unfold_op. 
  unfold subst; repeat rewrite fold_subst. 
  match goal with 
    | |- _ _ (subst_rec ?M ?N 0) _ => 
      replace (subst_rec M N 0) with (subst M N) by auto
  end. 
  eapply transitive_red. repeat (eapply subst_preserves_sf_red). 
  eapply preserves_app_sf_red. eapply subst_preserves_sf_red. 
  eapply2 extensions_by_matchfail. unfold var, lambda_term. 
  unfold lift; repeat rewrite lift_rec_preserves_app_comb. 
  eapply2 app_comb_matchfail. 
  eapply2 matchfail_app_l; repeat eapply2 nf_compound. 
  eapply2 matchfail_app_r; repeat eapply2 nf_compound. 
  repeat rewrite lift_rec_closed; auto. auto. auto. auto. 
  (* 1 *)
  eapply transitive_red. repeat eapply subst_preserves_sf_red. eapply preserves_app_sf_red. 
  eapply subst_preserves_sf_red. eapply2 extensions_by_matching. 
  unfold lift, lift_rec, lambda_term; fold lift_rec. 
  repeat rewrite lift_rec_preserves_app_comb.
  repeat rewrite (lift_rec_closed s); auto.  
  eapply2 app_comb_matching. auto. auto. auto. 
  unfold length. unfold map; fold map. unfold app; fold app. unfold fold_left. 
  unfold subst, subst_rec; fold subst_rec. 
  assert(maxvar equal_comb = 0). eapply2 maxvar_equal_comb. 
  repeat (rewrite (subst_rec_closed equal_comb)); auto. 
  insert_Ref_out. 
  repeat (unfold subst, subst_rec; fold subst_rec; insert_Ref_out). 
  repeat rewrite lift_rec_null. 
  repeat(rewrite (subst_rec_closed s); try omega). 
  eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.  
  eapply preserves_app_sf_red. 
  eapply2 equal_programs. auto. auto. auto. 
  eapply transitive_red. eapply preserves_app_sf_red.   unfold_op. 
  eapply succ_red. eapply2 f_op_red. auto. auto. 
  repeat rewrite fold_subst. 
  eapply transitive_red. repeat eapply subst_preserves_sf_red. 
  eapply2 star_beta. auto. auto. auto. auto.

Lemma subst_preserves_lambda_term: 
forall M1 M2 N, subst (lambda_term M1 M2) N = lambda_term (subst M1 N) (subst M2 N). 
Proof. unfold lambda_term, subst. unfold_op; split_all. Qed. 

  repeat rewrite subst_preserves_lambda_term. 
  unfold subst, lift, subst_rec; fold subst_rec. 
  repeat (repeat rewrite lift_rec_null; repeat (rewrite subst_rec_lift_rec; try omega)). 
  insert_Ref_out. 
  unfold subst, lift, subst_rec; fold subst_rec. 
  repeat (repeat rewrite lift_rec_null; repeat (rewrite subst_rec_lift_rec; try omega)). 
  insert_Ref_out. 
  unfold subst, lift, subst_rec; fold subst_rec. 
  repeat (repeat rewrite lift_rec_null; repeat (rewrite subst_rec_lift_rec; try omega)). 
  insert_Ref_out. 
  unfold subst, lift, subst_rec; fold subst_rec. 
  repeat (repeat rewrite lift_rec_null; repeat (rewrite subst_rec_lift_rec; try omega)). 
  insert_Ref_out. 
  repeat rewrite lift_rec_null. 
  repeat (rewrite (subst_rec_closed s)); try omega. 
  repeat (repeat rewrite lift_rec_null; repeat (rewrite subst_rec_lift_rec; try omega)). 
  auto. 
Qed. 

Lemma lift_rec_comb_not_abs :
  forall s n M s1, program s -> program s1 -> matchfail (app_comb vee (Ref 1)) s1 -> 
                   s <> s1 -> 
      sf_red (App (App (App lift_rec_comb s) (lambda_term s1 M)) n)
            (lambda_term (App (App (fix_comb (subst_rec lift_rec_comb_fn s 0)) s1) n)
                         (App (App (fix_comb (subst_rec lift_rec_comb_fn s 0)) M) n))
. 
Proof.
  intros. inversion H0. inversion H. 
  eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.
  unfold lift_rec_comb.
  eapply2 star_beta. auto. auto. 
  rewrite subst_preserves_fix_comb. 
  eapply transitive_red. eapply preserves_app_sf_red.  
  eapply2 fix_comb_fix. auto. 
  unfold lift_rec_comb_fn at 1.
  repeat (unfold subst; rewrite fold_subst). 
  eapply transitive_red.   eapply subst_preserves_sf_red.  eapply preserves_app_sf_red. 
   eapply preserves_app_sf_red. eapply2 star_beta. auto. auto. auto. 
  unfold subst; repeat rewrite fold_subst. 
  unfold subst; repeat rewrite fold_subst. 
  match goal with 
    | |- _ _ (subst_rec ?M ?N 0) _ => 
      replace (subst_rec M N 0) with (subst M N) by auto
  end. 
  eapply transitive_red. repeat (eapply subst_preserves_sf_red).  eapply preserves_app_sf_red.
  eapply2 extensions_by_matchfail. 
  unfold lift, lift_rec; fold lift_rec. repeat (rewrite lift_rec_preserves_app_comb). 
  repeat (rewrite (lift_rec_closed s1); try omega). 
  unfold var. eapply2 app_comb_matchfail. 
  eapply2 matchfail_app_l. auto. auto. auto. 
  eapply transitive_red.  repeat eapply subst_preserves_sf_red.  eapply preserves_app_sf_red.
  eapply2 extensions_by_matching. 
  unfold lift.   


Lemma  lift_rec_preserves_lambda_term: 
forall M1 M2 n k, lift_rec (lambda_term M1 M2) n k = 
                  lambda_term (lift_rec M1 n k) (lift_rec M2 n k). 
Proof. unfold lambda_term; split_all. Qed. 

repeat (rewrite lift_rec_preserves_lambda_term). 
  eapply2 app_comb_matching. auto. auto. auto. 
  unfold length. unfold map; fold map. unfold app; fold app. 
  unfold fold_left. unfold subst, subst_rec; fold subst_rec. 
  assert(maxvar equal_comb = 0). eapply2 maxvar_equal_comb. 
  repeat (rewrite (subst_rec_closed equal_comb)); auto. insert_Ref_out. 
  unfold subst_rec; fold subst_rec. insert_Ref_out. 
  unfold subst_rec; fold subst_rec. insert_Ref_out. 
  unfold subst_rec; fold subst_rec. insert_Ref_out.
  repeat rewrite lift_rec_null. 
  repeat (rewrite subst_rec_lift_rec; try omega; rewrite lift_rec_null).  
  (* 1 *) 
  eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.   
  eapply preserves_app_sf_red. 
  eapply2 unequal_programs. auto. auto. auto. 
  unfold_op. 
  eapply transitive_red. eapply preserves_app_sf_red.   eapply preserves_app_sf_red.  
  eapply succ_red. eapply2 f_op_red. auto. auto. auto. 
  eapply transitive_red. eapply preserves_app_sf_red.   
  eapply succ_red. eapply2 s_red. 
  eapply succ_red. eapply2 f_op_red. auto. auto. 
  repeat rewrite fold_subst. 
  eapply transitive_red. repeat eapply subst_preserves_sf_red. 
  eapply2 star_beta. auto. auto. auto. auto. 
  repeat rewrite subst_preserves_lambda_term. 
  repeat (unfold subst, subst_rec; fold subst_rec; insert_Ref_out). 
  repeat rewrite lift_rec_null. 
  repeat (rewrite (subst_rec_closed s1)); try omega.  
  repeat (rewrite subst_rec_lift_rec; try omega; repeat rewrite lift_rec_null). 
  auto. 
Qed. 


Proposition lift_rec_comb_app :
  forall s n M1 M2, program  s -> compound (App M1 M2) -> 
                      matchfail (var (Ref 1) (Ref 0))  (App M1 M2) -> 
                      matchfail (lambda_term (Ref 1) (Ref 0))  (App M1 M2) -> 
      sf_red (App (App (fix_comb (subst_rec lift_rec_comb_fn s 0)) (App M1 M2)) n)
            (App (App (App (fix_comb (subst_rec lift_rec_comb_fn s 0)) M1) n)
                 (App (App (fix_comb (subst_rec lift_rec_comb_fn s 0)) M2) n))
. 
Proof.
  intros. 
  eapply transitive_red. eapply preserves_app_sf_red.
  eapply2 fix_comb_fix.  auto. unfold lift_rec_comb_fn at 1.
  repeat (unfold subst; rewrite fold_subst). 
  eapply transitive_red. repeat eapply subst_preserves_sf_red. eapply preserves_app_sf_red.  
  eapply preserves_app_sf_red. 
  eapply2 star_beta.  auto. auto. auto. 
  (* 1 *)
  unfold_op. unfold subst. repeat rewrite fold_subst. 
  unfold subst. repeat rewrite fold_subst. 
  match goal with 
    | |- _ _ (subst_rec ?M ?N 0) _ => 
      replace (subst_rec M N 0) with (subst M N) by auto
  end. 
  eapply transitive_red. repeat (eapply subst_preserves_sf_red).  eapply preserves_app_sf_red.  
  eapply2 extensions_by_matchfail. repeat eapply2 matchfail_lift. auto. auto. auto. 
(* 1 *) 
  eapply transitive_red. repeat eapply subst_preserves_sf_red.   eapply preserves_app_sf_red.
  eapply2 extensions_by_matchfail. repeat eapply2 matchfail_lift. auto. auto. auto. 
  eapply transitive_red. repeat eapply subst_preserves_sf_red.   eapply preserves_app_sf_red. 
  eapply transitive_red. eapply2 star_beta. 
  unfold subst, subst_rec; fold subst_rec. insert_Ref_out. repeat rewrite lift_rec_null. 
  eapply succ_red. eapply2 f_compound_red. 
  replace (App (lift_rec (lift_rec M1 0 1) 0 1) (lift_rec (lift_rec M2 0 1) 0 1)) with 
  (lift_rec (lift_rec (App M1 M2) 0 1) 0 1) by auto. 
  repeat eapply2 lift_rec_preserves_compound. 
  unfold left_component, right_component. 
  rewrite fold_subst. unfold subst; rewrite fold_subst. 
  eapply transitive_red. repeat eapply subst_preserves_sf_red. 
  eapply transitive_red. eapply2 star_beta2. auto. auto. auto. auto. auto. auto. 
  unfold subst. repeat rewrite fold_subst. 
  unfold subst, subst_rec; fold subst_rec. insert_Ref_out. repeat rewrite lift_rec_null. 
  unfold subst, subst_rec; fold subst_rec. insert_Ref_out. repeat rewrite lift_rec_null.
  repeat (rewrite subst_rec_lift_rec; try omega; repeat (rewrite lift_rec_null)). 
  unfold subst, subst_rec; fold subst_rec. insert_Ref_out. repeat rewrite lift_rec_null.
  unfold subst, subst_rec; fold subst_rec. insert_Ref_out. repeat rewrite lift_rec_null.
  unfold subst, subst_rec; fold subst_rec. insert_Ref_out. repeat rewrite lift_rec_null.
  repeat (rewrite subst_rec_lift_rec; try omega; repeat (rewrite lift_rec_null)). 
  eapply succ_red. eapply2 s_red. auto. 
Qed. 
