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
(*                       SF-Calculus                                  *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *) 
(* Lambda Calculus from Project Coq                                   *) 
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                    Extensions.v                                    *)
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



Lemma fold_subst_list:
  forall sigma M N,  App (fold_left subst sigma M) N =
                     fold_left subst sigma (App M (lift (length sigma) N)).
Proof.
  induction sigma; split_all.
  (* 2 *)
  unfold lift; rewrite lift_rec_null. auto. 
  (* 1 *) 
  rewrite IHsigma. unfold subst. simpl. unfold lift. rewrite subst_rec_lift_rec; try omega. auto.
Qed.


Lemma list_subst_preserves_op:
  forall sigma o, fold_left subst sigma (Op o) = Op o. 
  Proof. induction sigma; split_all. unfold subst in *. split_all. Qed. 

Lemma list_subst_preserves_app:
  forall sigma M N, fold_left subst sigma (App M N) =
                    App (fold_left subst sigma M) (fold_left subst sigma N).
  Proof. induction sigma; split_all. unfold subst in *. split_all. Qed. 

Lemma list_subst_preserves_sf_red:
  forall sigma M N, sf_red M N -> sf_red (fold_left subst sigma M) (fold_left subst sigma N).
Proof.  induction sigma; split_all. eapply2 IHsigma. eapply2 subst_preserves_sf_red. Qed. 



Lemma list_subst_lift: forall sigma M, fold_left subst sigma (lift (length sigma) M) = M.
Proof.
  induction sigma; split_all. unfold lift; rewrite lift_rec_null. auto. 
unfold lift, subst. rewrite subst_rec_lift_rec; try omega. unfold lift in *. rewrite IHsigma. auto. 
Qed.


Fixpoint star_opt M := 
match M with 
| Ref 0 => App (App (Op Sop) (App (Op Fop) (Op Fop))) (App (Op Fop) (Op Fop))
| Ref (S n) => App (App (Op Fop) (Op Fop)) (Ref n)
| Op o => App (App (Op Fop) (Op Fop)) (Op o)
| App M1 M2 =>
  match star_opt M1 with
    | App (App (Op Fop) (Op Fop)) M3 =>
      match star_opt M2 with
        | App (App (Op Fop) (Op Fop)) M4 => App (App (Op Fop) (Op Fop)) (App M3 M4)
        | App (App (Op Sop) (App (Op Fop) (Op Fop)))  (App (Op Fop) (Op Fop)) => M3
        | M4 => App (App (Op Sop) (App (App (Op Fop) (Op Fop)) M3)) M4
      end
    | M3 => App (App (Op Sop) M3) (star_opt M2)
  end
end
.


Definition S_not_F M :=
  App (App (App (App M (Op Fop)) (App (Op Fop) (Op Fop))) (App (Op Fop) (Op Fop)))
      (App (App (Op Sop) (App (Op Fop) (Op Fop))) (App (Op Fop) (Op Fop))).
Definition eq_op := 
   App
     (App (Op Sop)
        (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (Op Sop)))
           (App
              (App (Op Sop)
                 (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (Op Sop)))
                    (App
                       (App (Op Sop)
                          (App (App (Op Fop) (Op Fop))
                             (App (Op Fop) (Op Fop))))
                       (App
                          (App (Op Sop)
                             (App
                                (App (Op Sop)
                                   (App
                                      (App (Op Sop)
                                         (App
                                            (App (Op Sop)
                                               (App
                                                  (App 
                                                  (Op Sop)
                                                  (App (Op Fop) (Op Fop)))
                                                  (App (Op Fop) (Op Fop))))
                                            (App (App (Op Fop) (Op Fop))
                                               (Op Fop))))
                                      (App (App (Op Fop) (Op Fop))
                                         (App (Op Fop) (Op Fop)))))
                                (App (App (Op Fop) (Op Fop))
                                   (App (Op Fop) (Op Fop)))))
                          (App (App (Op Fop) (Op Fop))
                             (App (App (Op Sop) (App (Op Fop) (Op Fop)))
                                (App (Op Fop) (Op Fop))))))))
              (App (App (Op Fop) (Op Fop))
                 (App
                    (App (Op Sop)
                       (App
                          (App (Op Sop)
                             (App
                                (App (Op Sop)
                                   (App
                                      (App (Op Sop)
                                         (App
                                            (App (Op Sop)
                                               (App (Op Fop) (Op Fop)))
                                            (App (Op Fop) (Op Fop))))
                                      (App (App (Op Fop) (Op Fop)) (Op Fop))))
                                (App (App (Op Fop) (Op Fop))
                                   (App (Op Fop) (Op Fop)))))
                          (App (App (Op Fop) (Op Fop))
                             (App (Op Fop) (Op Fop)))))
                    (App (App (Op Fop) (Op Fop))
                       (App (App (Op Sop) (App (Op Fop) (Op Fop)))
                          (App (Op Fop) (Op Fop)))))))))
     (App (App (Op Fop) (Op Fop))
        (App
           (App (Op Sop)
              (App
                 (App (Op Sop)
                    (App
                       (App (Op Sop)
                          (App
                             (App (Op Sop)
                                (App
                                   (App (Op Sop)
                                      (App
                                         (App (Op Sop)
                                            (App
                                               (App 
                                                  (Op Sop)
                                                  (App (Op Fop) (Op Fop)))
                                               (App (Op Fop) (Op Fop))))
                                         (App (App (Op Fop) (Op Fop))
                                            (Op Fop))))
                                   (App (App (Op Fop) (Op Fop))
                                      (App (Op Fop) (Op Fop)))))
                             (App (App (Op Fop) (Op Fop))
                                (App (Op Fop) (Op Fop)))))
                       (App (App (Op Fop) (Op Fop))
                          (App (App (Op Sop) (App (Op Fop) (Op Fop)))
                             (App (Op Fop) (Op Fop))))))
                 (App (App (Op Fop) (Op Fop))
                    (App (App (Op Fop) (Op Fop))
                       (App (App (Op Sop) (App (Op Fop) (Op Fop)))
                          (App (Op Fop) (Op Fop)))))))
           (App (App (Op Fop) (Op Fop)) (App (Op Fop) (Op Fop)))))
. 


Lemma aux_eq_op: eq_op = star_opt (star_opt (iff (S_not_F (Ref 1)) (S_not_F (Ref 0)))).
Proof. unfold eq_op, S_not_F, iff, not; unfold_op; unfold star_opt; split_all. Qed. 

Lemma maxvar_eq_op: maxvar eq_op = 0. 
Proof. split_all. Qed. 

Hint Resolve maxvar_eq_op. 

Lemma eq_op_true: forall o, sf_red (App (App eq_op (Op o)) (Op o)) k_op. 
Proof. unfold eq_op; unfold_op; split_all; case o; repeat eval_SF0. Qed. 

Lemma eq_op_false: forall o1 o2, o1<>o2 -> sf_red (App(App eq_op(Op o1))(Op o2)) (App k_op i_op). 
Proof. 
  unfold eq_op; unfold_op; intros.  
  gen_case H o1; gen_case H o2; try discriminate; repeat eval_SF0. 
  eapply2 preserves_app_sf_red. eval_SF0. 
Qed. 



Definition swap M := App (App s_op i_op) (App k_op M).

Lemma swap_check : forall M N, sf_red (App (swap M) N) (App N M). 
Proof. 
unfold swap; split_all; unfold_op; eval_SF0. eval_SF0. eapply2 preserves_app_sf_red;  eval_SF0. 
Qed. 

Fixpoint case P M := 
  match P with
    | Ref _ => star (App k_op M)
               (* the indices are renumbered, with binding from left to right *) 
    | Op o => 
      star(App (App (App (Op Fop) (Ref 0))
                    (App (App (App (App eq_op (Op o)) (Ref 0)) (App k_op (lift 1 M)))
                         (swap (Ref 0))))
               (App k_op (App k_op ((swap (Ref 0))))))
    | App P1 P2 => 
      star(App (App (App (App (Op Fop) (Ref 0)) i_op) 
                    (lift 1 (star (star (App (App (App (App 
                               (lift 2 (case P1 (case P2 (App k_op (App k_op M)))))
                               (Ref 1)) 
                                                       (App k_op (App k_op (App k_op i_op))))
                                                  (Ref 0))
                                             (App k_op i_op))))))
               (swap (Ref 0)))
  end.


Fixpoint pattern_size P :=
  match P with
    | Ref _ => 1
    | Op _ => 0
    | App P1 P2 => pattern_size P1 + (pattern_size P2)
  end.

Lemma lift_rec_preserves_case:
  forall P M n k, lift_rec (case P M) n k = case P (lift_rec M (n+ pattern_size P) k).
Proof.
  induction P; intros. 
  (* 3 *)
  split_all; rewrite lift_rec_preserves_star. replace (n0+1) with (S n0) by omega.  auto.
  (* 2 *)
  unfold pattern_size, case. rewrite lift_rec_preserves_star.
  unfold lift_rec; fold lift_rec. relocate_lt. rewrite lift_rec_closed.
  2: unfold eq_op; auto. unfold_op; unfold lift_rec; fold lift_rec.
  unfold lift, swap. unfold_op; unfold lift_rec; fold lift_rec.  relocate_lt.
  rewrite (lift_lift_rec M); try omega.
  replace (n+0) with n by omega. auto. 
  (* 1 *)
  unfold pattern_size, case; fold pattern_size; fold case.
  repeat rewrite lift_rec_preserves_star.
  unfold lift, lift_rec; fold lift_rec.
  relocate_lt. rewrite lift_rec_closed.
  2: unfold i_op; auto.
  repeat rewrite lift_rec_preserves_star.
  unfold_op; unfold lift, lift_rec; fold lift_rec.
  unfold relocate at 2. elim(test 2 1); intro. noway. relocate_lt.  
  repeat rewrite IHP1. repeat rewrite IHP2.
  unfold relocate at 2. elim(test 2 0); intro. noway. relocate_lt.  
  unfold swap; unfold_op. unfold lift, lift_rec; fold lift_rec. relocate_lt.
  replace(0 + pattern_size P1 + pattern_size P2) with (pattern_size P1 + pattern_size P2) by omega. 
  replace(2 + pattern_size P1 + pattern_size P2) with (2+ (pattern_size P1 + pattern_size P2)) by omega. 
rewrite lift_lift_rec; try omega. 
rewrite lift_lift_rec; try omega. 
replace(S (S (S n)) + pattern_size P1 + pattern_size P2) with (2+ (1 +(n + pattern_size P1 + pattern_size P2))) by omega. 
rewrite lift_lift_rec; try omega. 
rewrite lift_lift_rec; try omega. 
replace  (n + pattern_size P1 + pattern_size P2) with (n + (pattern_size P1 + pattern_size P2))
                                                        by omega. auto. 
Qed.


(* matching *) 


Inductive matching : SF -> SF -> list SF -> Prop :=
| match_ref : forall i M, matching (Ref i) M (cons M nil)
| match_op: forall o, matching (Op o) (Op o) nil
| match_app: forall p1 p2 M1 M2 sigma1 sigma2,
               normal (App p1 p2) -> compound (App M1 M2) ->
               matching p1 M1 sigma1 -> matching p2 M2 sigma2 ->
               matching (App p1 p2) (App M1 M2) ((map (lift (length sigma1)) sigma2) ++ sigma1)
.

Hint Constructors matching. 

Lemma matching_lift:
  forall P M sigma, matching P M sigma -> forall k, matching P (lift k M) (map (lift k) sigma). 
Proof.
  induction P; split_all; inversion H; subst; unfold map; fold map; auto. 
replace (lift k (App M1 M2)) with (App (lift k M1) (lift k M2)) by (unfold lift; auto). 
replace(fix map (l : list SF) : list SF :=
            match l with
            | nil => nil
            | a :: t => lift (length sigma1) a :: map t
            end) with (map (lift (length sigma1))) by auto.
replace (fix map (l : list SF) : list SF :=
         match l with
         | nil => nil
         | a :: t => lift k a :: map t
         end) with (map (lift k)) by auto. 
rewrite map_app.
replace (map (lift k) (map (lift (length sigma1)) sigma2)) with
         (map (lift (length (map (lift k) sigma1))) (map (lift k) sigma2)).
eapply2 match_app. 
replace (App (lift k M1) (lift k M2)) with  (lift k (App M1 M2)) by (unfold lift; auto). 
unfold lift. eapply2 lift_rec_preserves_compound. 
clear. induction sigma2; split_all. rewrite IHsigma2. rewrite map_length. 
unfold lift; repeat rewrite lift_rec_lift_rec; try omega. 
replace (length sigma1 + k) with (k+ length sigma1) by omega. auto.
Qed.


Lemma program_matching: forall M, program M -> matching M M nil. 
Proof.
  induction M; split_all.
  inversion H; split_all. simpl in *; noway. 
  inversion H; split_all. inversion H0.
  assert(status (App M1 M2) = Passive) by eapply2 closed_implies_passive.
  rewrite H6 in H7; discriminate.
  replace (nil: list SF)
  with (List.map (lift (length (nil: list SF))) (nil: list SF) ++ (nil: list SF))
    by split_all.
  eapply2 match_app. simpl in *. max_out. eapply2 IHM1. unfold program; auto.
  simpl in *. max_out. eapply2 IHM2. unfold program; auto.
Qed. 


Lemma pattern_normal: forall p M sigma, matching p M sigma -> normal p.
Proof. induction p; split_all. inversion H; subst; split_all. Qed.

Hint Resolve pattern_normal. 



Lemma app_comb_matching:
  forall p1 p2 M1 M2 sigma1 sigma2,
    matching p1 M1 sigma1 -> matching p2 M2 sigma2 ->
    matching (app_comb p1 p2) (app_comb M1 M2) (map (lift (length sigma1)) sigma2 ++ sigma1).
Proof.
  intros; unfold app_comb; unfold_op.
  replace (map (lift (length sigma1)) sigma2 ++ sigma1)
  with (map (lift (length (map (lift (length sigma1)) sigma2 ++ sigma1))) nil ++
            (map (lift (length sigma1)) sigma2 ++ sigma1))
    by split_all.   
  eapply2 match_app. repeat eapply2 nf_compound.
  2: eapply2 program_matching; unfold program; auto.
  replace (map (lift (length sigma1)) sigma2 ++ sigma1)
  with (map (lift (length (nil: list SF)))(map (lift (length sigma1)) sigma2 ++ sigma1) ++ nil)
    by (split_all; rewrite map_lift0; rewrite append_nil; auto). 
  eapply2 match_app. repeat eapply2 nf_compound.
  eapply2 match_app. repeat eapply2 nf_compound.
  replace sigma1 with (map (lift (length (nil : list SF))) sigma1 ++ nil)
     by (split_all; rewrite map_lift0; rewrite append_nil; auto). 
  eapply2 match_app.
  replace sigma1 with (map (lift (length (nil : list SF))) sigma1 ++ nil)
     by (split_all; rewrite map_lift0; rewrite append_nil; auto). 
  eapply2 match_app.
  eapply2 program_matching; unfold program; auto.
  replace sigma2 with (map (lift (length (nil : list SF))) sigma2 ++ nil)
     by (split_all; rewrite map_lift0; rewrite append_nil; auto). 
  eapply2 match_app.
  eapply2 program_matching; unfold program; auto.
Qed.

  
Lemma var_matching:
    forall p1 p2 M1 M2 sigma1 sigma2,
    matching p1 M1 sigma1 -> matching p2 M2 sigma2 ->
    matching (var p1 p2) (var M1 M2) (map (lift (length sigma1)) sigma2 ++ sigma1).
Proof.
  intros; unfold var; unfold_op. eapply2 app_comb_matching.
  replace sigma1 with (map (lift (length (nil: list SF))) sigma1 ++ nil)
    by (split_all; rewrite map_lift0; rewrite append_nil; auto). 
  eapply2 app_comb_matching.
eapply2 program_matching. unfold program; split_all. eapply2 vee_normal.
Qed.



Lemma pattern_is_program: 
forall P, program P -> forall M sigma, matching P M sigma -> M = P /\ sigma = nil. 
Proof. 
induction P; intros; inversion H; subst.  
(* 3 *) 
simpl in *; discriminate. 
(* 2 *) 
inversion H0; auto. 
(* 1 *) 
simpl in *; max_out. inversion H0; inversion H1; subst.  
(* 2 *) 
assert(M1 = P1 /\ sigma1 = nil). 
eapply2 IHP1 . unfold program; auto. 
assert(M2 = P2 /\ sigma2 = nil). 
eapply2 IHP2 . unfold program; auto. 
split_all; subst. 
auto. 
(* 1 *) 
assert(M1 = P1 /\ sigma1 = nil). 
eapply2 IHP1 . unfold program; auto. 
assert(M2 = P2 /\ sigma2 = nil). 
eapply2 IHP2 . unfold program; auto. 
split_all; subst. 
auto. 
Qed. 


Lemma matching_app_comb: 
forall P1 P2 N sigma, matching (app_comb P1 P2) N sigma -> 
exists N1 N2 sigma1 sigma2, N = app_comb N1 N2 /\ matching P1 N1 sigma1 /\ 
matching P2 N2 sigma2 /\ sigma = (map (lift (length sigma1)) sigma2) ++ sigma1. 
Proof. 
intros. 
inversion H; subst.
assert(M2 = i_op /\ sigma2 = nil). eapply2 pattern_is_program. 
unfold_op; split_all. 
split_all; subst. 
inversion H4; subst. 
assert(M0 = s_op /\ sigma0 = nil). eapply2 pattern_is_program. 
unfold_op; split_all. split_all; subst. 
unfold length at 1. unfold length in H4. 
clear - H11 ;  inversion H11; subst. 
inversion H6; subst. 
assert(M2 = k_op /\ sigma2 = nil). eapply2 pattern_is_program. 
unfold_op; split_all. split_all; subst.
clear - H3 H10. 
inversion H3; subst. 
assert(M0 = s_op /\ sigma0 = nil). eapply2 pattern_is_program. 
unfold_op; split_all. split_all; subst. 
inversion H7; subst. 
assert(M1 = k_op /\ sigma1 = nil). eapply2 pattern_is_program. 
unfold_op; split_all. split_all; subst. 
exist M0; exist M3; exist sigma0; exist sigma3. 
repeat rewrite map_lift0. 

Lemma aux: forall (sigma : list SF), sigma ++ nil = sigma. 
Proof. induction sigma; split_all. Qed. 

repeat rewrite aux. auto. 
Qed. 


Lemma matching_var: 
forall N sigma, matching (var (Ref 1) (Ref 0)) N sigma -> 
exists N1 N2, N = var N1 N2 /\ sigma = (lift_rec N2 0 1 :: N1 :: nil).
Proof. 
intros. 
inversion H; subst.
assert(M2 = i_op /\ sigma2 = nil). eapply2 pattern_is_program. 
unfold_op; split_all. 
split_all; subst. 
inversion H4; subst. 
assert(M0 = s_op /\ sigma0 = nil). eapply2 pattern_is_program. 
unfold_op; split_all. split_all; subst. 
clear - H11. inversion H11; subst. 
inversion H6; subst. 
assert(M2 = k_op /\ sigma2 = nil). eapply2 pattern_is_program. 
unfold_op; split_all. split_all; subst. 
inversion H10; subst. 
clear - H3. 
inversion H3; subst. 
assert(M0 = s_op /\ sigma0 = nil). eapply2 pattern_is_program. 
unfold_op; split_all. split_all; subst. 
clear - H7. 
inversion H7; subst. 
assert(M1 = k_op /\ sigma1 = nil). eapply2 pattern_is_program. 
unfold_op; split_all. split_all; subst. 
clear - H6. 
unfold app_comb in H6. 
inversion H6; subst. 
assert(M2 = i_op /\ sigma2 = nil). eapply2 pattern_is_program. 
unfold_op; split_all. split_all; subst. 
clear - H3. 
inversion H3; subst. 
assert(M0 = s_op /\ sigma0 = nil). eapply2 pattern_is_program. 
unfold_op; split_all. split_all; subst. 
clear - H7. 
inversion H7; subst. 
assert(M1 = (App s_op (App k_op vee)) /\ sigma1 = nil). eapply2 pattern_is_program. 
unfold_op; split_all. 
eapply2 nf_compound. eapply2 nf_compound. eapply2 vee_normal. 
split_all; subst. 
clear - H6. 
inversion H6; subst. 
assert(M1 = k_op /\ sigma1 = nil). eapply2 pattern_is_program. 
unfold_op; split_all. 
split_all; subst. 
clear - H7. 
inversion H7; subst. 
exist M2; exist M3. 
unfold lift. repeat rewrite lift_rec_null. auto.  
Qed. 



Lemma maxvar_case : forall P M, maxvar (case P M) = maxvar M - (pattern_size P).
Proof.
  induction P; split_all. rewrite maxvar_star. omega. 
  rewrite maxvar_star. repeat rewrite max_zero.
  replace (pred(maxvar (lift 1 M))) with (maxvar (lift 1 M) -1) by omega. 
  rewrite lift_preserves_maxvar2. omega. 
  repeat rewrite lift_rec_preserves_star. repeat rewrite maxvar_star. 
  repeat rewrite max_zero.
  unfold lift; rewrite lift_rec_lift_rec; try omega.  simpl. 
  replace (pred
     (pred
        (pred
           (maxvar (lift_rec (case P1 (case P2 (App k_op (App k_op M)))) 0 3)))))
  with  (maxvar (lift 3 (case P1 (case P2 (App k_op (App k_op M))))) - 3)
    by (unfold lift; auto;omega).  
  rewrite lift_preserves_maxvar2. 
  rewrite IHP1. rewrite IHP2. unfold_op; split_all. omega. 
Qed.

Lemma case_by_matching:
  forall P N sigma,  matching P N sigma ->
                     forall M, sf_red (App (case P M) N) (App k_op (fold_left subst sigma M)). 
Proof.
  induction P; intros.
  (* 3 *)
  eval_SF0. eval_SF0. eval_SF0. eval_SF0. eapply2 preserves_app_sf_red.
  inversion H; subst. simpl. eapply2 star_beta.
  (* 2 *)
  inversion H; subst. simpl; case o; repeat eval_SF0. eapply2 preserves_app_sf_red;
  eapply transitive_red. eapply2 star_beta. 
  unfold subst, lift; rewrite subst_rec_lift_rec; try omega.   rewrite lift_rec_null.  auto.
  eapply2 preserves_app_sf_red; eapply transitive_red. eapply2 star_beta. 
  unfold subst, lift; rewrite subst_rec_lift_rec; try omega.   rewrite lift_rec_null.  auto.
  (* 1 *) 
  inversion H; subst. 
  unfold case; fold case. eapply transitive_red. eapply2 star_beta.   
  unfold subst, subst_rec; fold subst_rec. insert_Ref_out. repeat rewrite lift_rec_null. 
  eapply transitive_red. eapply preserves_app_sf_red. eapply succ_red. eapply2 f_compound_red. 
  rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null.  
  eapply2 star_beta2. 
  unfold swap; unfold_op.  unfold subst_rec; fold subst_rec. insert_Ref_out. 
  repeat rewrite lift_rec_null. auto. 
  unfold subst, lift, subst_rec; fold subst_rec; repeat (rewrite subst_rec_lift_rec; try omega). 
  rewrite lift_rec_null. 
  insert_Ref_out. unfold_op. 
  unfold subst_rec; fold subst_rec; repeat (rewrite subst_rec_lift_rec; try omega). 
  unfold left_component, right_component.   insert_Ref_out. repeat rewrite lift_rec_null. 
  repeat (rewrite subst_rec_lift_rec; try omega). repeat rewrite lift_rec_null. 
(* 1 *)
eapply transitive_red. eapply preserves_app_sf_red.
eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply preserves_app_sf_red. auto. auto. auto. auto. auto. auto. 
eapply transitive_red. eapply preserves_app_sf_red.
eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 IHP1. auto. auto. auto. auto.
eapply transitive_red. eapply preserves_app_sf_red.
eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eval_SF0. auto. auto. auto. 
rewrite fold_left_app. 
rewrite fold_subst_list. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply list_subst_preserves_sf_red.
eapply2 IHP2. eapply2 matching_lift. auto. auto. 
eapply transitive_red. eapply preserves_app_sf_red.
rewrite fold_subst_list.
eapply list_subst_preserves_sf_red.
eval_SF0. auto. 
rewrite fold_subst_list.
rewrite fold_subst_list.
fold sf_red.
eapply transitive_red. eapply list_subst_preserves_sf_red. eapply list_subst_preserves_sf_red.
eval_SF0.

  repeat rewrite list_subst_preserves_app. repeat rewrite list_subst_preserves_op. 
  repeat eapply2 preserves_app_sf_red.
Qed.



Definition extension P M R := App (App s_op (case P M)) (App k_op R). 

Proposition extensions_by_matching:
  forall P N sigma,  matching P N sigma ->
                     forall M R, sf_red (App (extension P M R) N) (fold_left subst sigma M) .
Proof.
  intros. unfold extension. eapply succ_red. eapply2 s_red.
  eapply transitive_red. eapply preserves_app_sf_red. eapply2 case_by_matching. eval_SF0. eval_SF0.
Qed.



Lemma lift_rec_preserves_extension: 
  forall P M R n k, lift_rec (extension P M R) n k =
                    extension P (lift_rec M (n+ pattern_size P) k) (lift_rec R n k).
Proof.
  intros. unfold extension. unfold_op. unfold lift_rec; fold lift_rec.
rewrite lift_rec_preserves_case. auto. 
Qed.



Lemma maxvar_extension : 
forall P M R, maxvar (extension P M R) = max (maxvar M - (pattern_size P)) (maxvar R).
Proof.  intros. unfold extension; simpl. rewrite maxvar_case. auto. Qed. 


Lemma extension_ref: forall i M R N, sf_red (App (extension (Ref i) M R) N) (App (star M) N).
Proof. split_all. unfold extension.  repeat eval_SF0. Qed. 

Lemma extension_op : forall o M R, sf_red (App (extension (Op o) M R) (Op o)) M.
Proof.
  intros. unfold extension. eapply transitive_red.  eapply succ_red. eapply2 s_red.
  unfold case. eapply preserves_app_sf_red. eapply2 star_beta. eval_SF0. 
  unfold subst, subst_rec; fold subst_rec. insert_Ref_out.
  unfold swap; unfold_op.  unfold subst_rec; fold subst_rec. 
  rewrite subst_rec_closed; auto. eval_SF0. rewrite subst_rec_lift_rec; try omega. 
  insert_Ref_out. repeat rewrite lift_rec_null. 
  eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
  eapply preserves_app_sf_red. eapply2 eq_op_true. auto. auto. auto. eval_SF0. 
Qed. 


Lemma extension_op_fail : 
forall o M R N, factorable N -> Op o <> N -> sf_red (App (extension (Op o) M R) N) (App R N).
Proof.
  intros. unfold extension. eapply transitive_red.  eapply succ_red. eapply2 s_red.
  unfold case. eapply preserves_app_sf_red. eapply2 star_beta. eval_SF0. 
  unfold subst, subst_rec; fold subst_rec. insert_Ref_out.
  unfold swap; unfold_op.  unfold subst_rec; fold subst_rec. 
  rewrite subst_rec_closed; auto. rewrite subst_rec_lift_rec; try omega. 
  insert_Ref_out. repeat rewrite lift_rec_null. 
  inversion H; split_all; subst. 
  (* 2 *) 
  eapply transitive_red. eapply preserves_app_sf_red.  eval_SF0. auto. 
  eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
  eapply preserves_app_sf_red. 
  eapply2 eq_op_false. intro; subst; eapply2 H0. auto. auto. auto. eval_SF0. eval_SF0. 
  eval_SF0. eapply2 preserves_app_sf_red; eval_SF0. 
  (* 1 *) 
  eapply transitive_red. eapply preserves_app_sf_red.  
  eapply succ_red. eapply2 f_compound_red. eval_SF0. auto. eval_SF0. eval_SF0. 
  eapply2 preserves_app_sf_red; eval_SF0. 
Qed. 

Lemma extension_compound_op: forall P1 P2 M R o, 
sf_red (App (extension (App P1 P2) M R) (Op o)) (App R (Op o)). 
Proof. 
  intros. unfold extension, case; fold case. unfold_op. 
eapply transitive_red. eapply succ_red. eapply2 s_red. 
eapply preserves_app_sf_red. eapply2 star_beta. eval_SF0. 
unfold subst, subst_rec; fold subst_rec. insert_Ref_out. 
eval_SF0. eval_SF0. eval_SF0. eapply2 preserves_app_sf_red;  eval_SF0. 
Qed. 


Inductive matchfail : SF -> SF -> Prop :=
| matchfail_op: forall o M, factorable M -> Op o <> M -> matchfail (Op o) M
| matchfail_app_op: forall p1 p2 o, normal (App p1 p2) -> matchfail (App p1 p2) (Op o)
| matchfail_app_l: forall p1 p2 M1 M2, normal (App p1 p2) -> compound (App M1 M2) ->
               matchfail p1 M1 -> matchfail (App p1 p2) (App M1 M2)
| matchfail_app_r: forall p1 p2 M1 M2 sigma1, normal (App p1 p2) -> compound (App M1 M2) ->
               matching p1 M1 sigma1 -> matchfail p2 M2 -> matchfail (App p1 p2) (App M1 M2)
.

Hint Constructors matchfail. 


Lemma matchfail_lift: forall P M, matchfail P M -> forall k, matchfail P (lift k M).
Proof.
  induction P; split_all; inversion H; subst. 
  gen2_case H1 H2 M. inversion H1; split_all. inv1 compound.
  eapply2 matchfail_op. unfold lift. inversion H1; split_all. unfold factorable. right.
  replace (App (lift_rec s 0 k) (lift_rec s0 0 k)) with (lift_rec (App s s0) 0 k) by auto. 
  eapply2 lift_rec_preserves_compound. discriminate. 
unfold lift; split_all. 
(* 2 *)
replace (lift k (App M1 M2)) with (App (lift k M1) (lift k M2)) by auto.
eapply2 matchfail_app_l.
replace (App (lift k M1) (lift k M2)) with (lift k (App M1 M2)) by auto.
unfold lift. eapply2 lift_rec_preserves_compound.
(* 1 *)
replace (lift k (App M1 M2)) with (App (lift k M1) (lift k M2)) by auto.
eapply2 matchfail_app_r.
replace (App (lift k M1) (lift k M2)) with (lift k (App M1 M2)) by auto.
unfold lift. eapply2 lift_rec_preserves_compound.
eapply2 matching_lift. 
Qed.


Lemma case_by_matchfail:
  forall P N,  matchfail P N  -> forall M, sf_red (App (case P M) N) (swap N). 
Proof.
  induction P; intros; inversion H; subst.
  (* 4 *)
  unfold case. eapply transitive_red. eapply star_beta. 
  unfold swap; unfold_op; unfold subst, subst_rec; fold subst_rec.  insert_Ref_out. 
  repeat rewrite lift_rec_null. rewrite subst_rec_closed. 2: rewrite maxvar_eq_op; omega. 
  inversion H1; split_all; subst. 
  eval_SF0. eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
  eapply2 eq_op_false. intro; subst. eapply2 H2. 
  rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null. auto. auto. eval_SF0. eval_SF0. 
  eapply succ_red. eapply2 f_compound_red. eval_SF0. 
  (* 3 *) 
  unfold case; fold case. eapply transitive_red. eapply star_beta. 
  unfold swap; unfold_op; unfold subst, subst_rec; fold subst_rec.  insert_Ref_out. 
  eval_SF0. eval_SF0. 
  (* 2 *) 
  unfold case; fold case. eapply transitive_red. eapply star_beta. 
  unfold swap; unfold_op; unfold subst, subst_rec; fold subst_rec.  insert_Ref_out. 
  repeat rewrite lift_rec_null. 
  eapply transitive_red. eapply preserves_app_sf_red. 
  eapply succ_red. eapply2 f_compound_red. unfold left_component, right_component. 
  rewrite subst_rec_lift_rec; try omega.   rewrite lift_rec_null. eapply2 star_beta2. auto. 
  unfold subst, subst_rec; fold subst_rec. 
  repeat rewrite (subst_rec_lift_rec); try omega. insert_Ref_out. 
  repeat rewrite lift_rec_null. 
  repeat rewrite (subst_rec_lift_rec); try omega. 
  unfold subst_rec; fold subst_rec;   repeat rewrite lift_rec_null. 
  insert_Ref_out.   repeat rewrite lift_rec_null. 
  eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
  eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
  eapply2 IHP1. auto. auto. auto. auto. unfold swap. eval_SF0.  eval_SF0.  eval_SF0.  eval_SF0. 
  (* 1 *) 
  unfold case; fold case. eapply transitive_red. eapply star_beta. 
  unfold swap; unfold_op; unfold subst, subst_rec; fold subst_rec.  insert_Ref_out. 
  repeat rewrite lift_rec_null. 
  eapply transitive_red. eapply preserves_app_sf_red. 
  eapply succ_red. eapply2 f_compound_red. unfold left_component, right_component. 
  rewrite subst_rec_lift_rec; try omega.   rewrite lift_rec_null. eapply2 star_beta2. auto. 
  unfold subst, subst_rec; fold subst_rec. 
  repeat rewrite (subst_rec_lift_rec); try omega. insert_Ref_out. 
  repeat rewrite lift_rec_null. 
  repeat rewrite (subst_rec_lift_rec); try omega. 
  unfold subst_rec; fold subst_rec;   repeat rewrite lift_rec_null. 
  insert_Ref_out.   repeat rewrite lift_rec_null. 
  eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
  eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
  eapply2 case_by_matching. auto. auto. auto. auto. unfold swap.
  eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
  eapply preserves_app_sf_red. eval_SF0. auto. auto. auto. 
  rewrite fold_subst_list. 
  eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
  eapply list_subst_preserves_sf_red. eapply2 IHP2. eapply2 matchfail_lift. auto. auto.
  rewrite fold_subst_list. rewrite fold_subst_list. 
  eapply transitive_red. eapply list_subst_preserves_sf_red. 
  unfold swap. 
eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0.
eapply transitive_red. eval_SF0. 
unfold lift; simpl. auto. 
repeat rewrite list_subst_preserves_app.
repeat rewrite list_subst_preserves_op.
eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red.
replace(lift_rec M1 0 (length sigma1)) with (lift (length sigma1) M1) by auto. 
replace(lift_rec M2 0 (length sigma1)) with (lift (length sigma1) M2) by auto.
eapply2 preserves_app_sf_red; rewrite list_subst_lift; auto. 
Qed.


Proposition extensions_by_matchfail:
  forall P N,  matchfail P N -> forall M R, sf_red (App (extension P M R) N) (App R N).
Proof.
  intros. inversion H; subst. 
  (* 4 *) 
  eapply2 extension_op_fail. 
  (* 3 *) 
  eapply2 extension_compound_op. 
  (* 2 *) 
  unfold extension, swap.   unfold case at 1; fold case.
  eapply succ_red. eapply2 s_red. 
  eapply transitive_red. eapply preserves_app_sf_red. eapply2 star_beta. eval_SF0. 
  unfold subst, subst_rec; fold subst_rec. insert_Ref_out. repeat rewrite lift_rec_null_term. 
  unfold_op. rewrite subst_rec_lift_rec; auto; try omega. repeat rewrite lift_rec_null_term. 
  eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
  eapply succ_red. eapply2 f_compound_red. unfold left_component, right_component.  
  eapply2 star_beta2. 
  unfold swap; simpl; insert_Ref_out; rewrite lift_rec_null.  auto. auto.
  unfold subst, subst_rec; fold subst_rec.
  repeat rewrite subst_rec_lift_rec; try omega. repeat rewrite lift_rec_null. 
  insert_Ref_out; rewrite lift_rec_null. unfold subst, subst_rec; fold subst_rec.
  insert_Ref_out; rewrite lift_rec_null. repeat rewrite subst_rec_lift_rec; try omega. 
  repeat rewrite lift_rec_null. 
  eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
  eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
  eapply2 case_by_matchfail. auto. auto. auto. auto. auto. 
  unfold swap. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. 
  eapply preserves_app_sf_red; eval_SF0. 
  (* 1 *) 
  unfold extension, swap.   unfold case at 1; fold case.
  eapply succ_red. eapply2 s_red. 
  eapply transitive_red. eapply preserves_app_sf_red. eapply2 star_beta. eval_SF0. 
  unfold subst, subst_rec; fold subst_rec. insert_Ref_out. repeat rewrite lift_rec_null_term. 
  unfold_op. rewrite subst_rec_lift_rec; auto; try omega. repeat rewrite lift_rec_null_term. 
  eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
  eapply succ_red. eapply2 f_compound_red. unfold left_component, right_component.  
  eapply2 star_beta2. 
  unfold swap; simpl; insert_Ref_out; rewrite lift_rec_null.  auto. auto.
  unfold subst, subst_rec; fold subst_rec.
  repeat rewrite subst_rec_lift_rec; try omega. repeat rewrite lift_rec_null. 
  insert_Ref_out; rewrite lift_rec_null. unfold subst, subst_rec; fold subst_rec.
  insert_Ref_out; rewrite lift_rec_null. repeat rewrite subst_rec_lift_rec; try omega. 
  repeat rewrite lift_rec_null. 
  eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
  eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
  eapply2 case_by_matching. auto. auto. auto. auto. auto. 
  eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
  eapply preserves_app_sf_red. eapply preserves_app_sf_red. eval_SF0. auto. auto. auto. auto.
  eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
  eapply preserves_app_sf_red.   rewrite fold_subst_list. eapply list_subst_preserves_sf_red.
  eapply2 case_by_matchfail. eapply2 matchfail_lift. auto. auto. auto. 
  repeat rewrite fold_subst_list.  
  eapply transitive_red. eapply list_subst_preserves_sf_red. 
  unfold swap. 
  eapply transitive_red. eval_SF0.
  eapply transitive_red. eval_SF0.
  eapply transitive_red. eval_SF0.
  eapply transitive_red. eval_SF0. 
  eapply transitive_red. eval_SF0.
  eapply transitive_red. eapply preserves_app_sf_red. eval_SF0. eval_SF0. auto. 
  rewrite list_subst_preserves_app. eapply2 preserves_app_sf_red. 
  rewrite list_subst_lift. auto. 
  replace(lift_rec M1 0 (length sigma1)) with (lift (length sigma1) M1) by auto. 
  replace(lift_rec M2 0 (length sigma1)) with (lift (length sigma1) M2) by auto.
    rewrite list_subst_preserves_app. eapply2 preserves_app_sf_red; rewrite list_subst_lift; auto. 
Qed. 



Lemma match_program: 
forall P M, normal P -> program M -> matchfail P M \/ exists sigma, matching P M sigma.
Proof. 
induction P; split_all. 
(* 3 *) 
right. exist (cons M nil). 
(* 2 *) 
gen_case H0 M. inversion H0; split_all. simpl in *; discriminate. 
case o; case o0; split_all. 
right.  exist (nil: list SF). 
left; auto. eapply2 matchfail_op. unfold factorable; split_all. left; eauto. discriminate. 
left; auto. eapply2 matchfail_op. unfold factorable; split_all. left; eauto. discriminate. 
right.  exist (nil: list SF). 
left; auto. eapply2 matchfail_op. eapply2 programs_are_factorable.  discriminate. 
(* 1 *) 
gen_case H0 M; inversion H0; auto. simpl in *; discriminate. 
inversion H1; subst.  
assert(status (App s s0) = Passive) by eapply2 closed_implies_passive. 
rewrite H7 in H3; discriminate. 
simpl in *; max_out.  
assert(normal P1 /\ normal P2) by (inversion H; auto). inversion H2. 
assert(matchfail P1 s \/ (exists sigma : list SF, matching P1 s sigma))
by (eapply2 IHP1; unfold program; auto). 
assert(matchfail P2 s0 \/ (exists sigma : list SF, matching P2 s0 sigma))
by (eapply2 IHP2; unfold program; auto). 
inversion H10. left; eapply2 matchfail_app_l. 
split_all. 
inversion H11. left; eapply2 matchfail_app_r. 
split_all. 
right; eauto. 
Qed. 


Lemma pattern_is_program2: 
forall P, program P -> forall M, matchfail P M  -> M <> P. 
Proof. 
induction P; intros; inversion H; subst.  
(* 3 *) 
simpl in *; discriminate. 
(* 2 *) 
inversion H0; auto. 
(* 1 *) 
simpl in *; max_out. inversion H0; inversion H1; subst.
intro; discriminate.  
intro; discriminate.  
assert(status (App P1 P2) = Passive). eapply2 closed_implies_passive. inversion H; auto. 
rewrite H14 in H2; discriminate. 
assert(M1 <> P1). eapply2 IHP1. unfold program; auto. intro. inversion H5. eapply2 H2. 
assert(status (App P1 P2) = Passive). eapply2 closed_implies_passive. inversion H; auto. 
rewrite H15 in H2; discriminate. 
assert(M2 <> P2). eapply2 IHP2. unfold program; auto. intro. inversion H5. eapply2 H2. 
Qed.


Lemma app_comb_matchfail : 
  forall P1 P2 M1 M2, matchfail (App (App (Op Sop) P1) P2)  (App (App (Op Sop) M1) M2)  -> 
                      matchfail (app_comb P1 P2)  (app_comb M1 M2)  . 
Proof. 
unfold app_comb; unfold_op. intros. inv matchfail.
(* 2 *) 
assert (normal P1 /\ normal P2) by inv1 normal. inversion H. 
eapply2 matchfail_app_l; repeat eapply2 nf_compound. 
eapply2 matchfail_app_r; repeat eapply2 nf_compound. 
eapply2 matchfail_app_l; repeat eapply2 nf_compound. 
eapply2 matchfail_app_r; repeat eapply2 nf_compound. 
eapply2 matchfail_app_r; repeat eapply2 nf_compound.
(* 1 *) 
assert (normal P1 /\ normal P2) by inv1 normal. inversion H. 
eapply2 matchfail_app_l; repeat eapply2 nf_compound. 
eapply2 matchfail_app_r; repeat eapply2 nf_compound. 
inversion H6.
eapply2 matchfail_app_r; repeat eapply2 nf_compound. 
repeat (eapply2 match_app; repeat eapply2 nf_compound).
eapply2 matchfail_app_r; repeat eapply2 nf_compound. 
Qed. 


Lemma pattern_is_program3: 
forall P, program P -> forall M, program M -> M<>P -> matchfail P M .
Proof. 
induction P; intros; inversion H; subst.  
(* 3 *) 
simpl in *; discriminate. 
(* 2 *) 
inversion H0. eapply2 matchfail_op.  eapply2 programs_are_factorable. 
(* 1 *) 
gen2_case H0 H1 M. inversion H0; simpl in *; discriminate. 
assert(s = P1 \/ s<> P1) by eapply decidable_term_equality.  
inversion H4. subst. 
eapply2 matchfail_app_r. 
assert(factorable (App P1 P2)) by eapply2 programs_are_factorable. 
inversion H5; split_all. gen_case H6 P1. 
inversion H6. gen_case H6 s; inversion H6. 
eapply2 program_matching. 
simpl in *; max_out; inversion H2; split_all. 
eapply2 IHP2. simpl in *; max_out; inversion H2; split_all. 
inversion H0; inversion H5; simpl in *; max_out; split_all. 
intro; subst; eapply2 H1. 
eapply2 matchfail_app_l. 
assert(factorable (App s l0)) by eapply2 programs_are_factorable. 
inversion H6; split_all; subst. 
eapply2 IHP1. simpl in *; max_out; inversion H2; split_all. 
inversion H0. simpl in *; max_out.  inversion H6; split_all. 
Qed. 

Lemma matchfail_lift_rec: forall P M k, matchfail P M -> matchfail P (lift k M).
Proof. 
induction P; split_all; inversion H; auto.
eapply matchfail_op. inversion H1; split_all; subst; split_all.
unfold factorable.  right. unfold lift; inversion H4; split_all. 
unfold lift; intro. gen2_case H2 H4 M. 
subst; split_all. 
unfold lift; split_all. 
inversion H; subst. discriminate. 
eapply2 matchfail_app_l. 
inversion H3; simpl; auto. 
eapply2 matchfail_app_r. 
inversion H3; simpl; auto. 
inversion H11; subst. eapply matching_lift. eexact H10. 
inversion H11; subst. eapply2 IHP2. 
unfold lift; simpl. 
eapply2 matchfail_app_r. inversion H3; split_all. 
eapply matching_lift. eexact H4. 
Qed.


Lemma matchfail_app_comb: 
forall P1 P2 M1 M2, matchfail (App (App (Op Sop) P1) P2) (App (App (Op Sop) M1) M2) -> 
matchfail (app_comb P1 P2) (app_comb M1 M2).
Proof. 
intros. unfold app_comb; unfold_op.
inversion H; subst; split_all.  inversion H6; subst. inversion H9. 
assert False by eapply2 H2. noway. 
(* 2 *) 
assert(normal P1 /\ normal P2) by (inversion H4; inversion H7; split_all). 
inversion H0. 
eapply2 matchfail_app_l. repeat eapply2 nf_compound. 
eapply2 matchfail_app_r. repeat eapply2 nf_compound. 
eapply2 matchfail_app_l. repeat eapply2 nf_compound. 
eapply2 matchfail_app_r. repeat eapply2 nf_compound. 
eapply2 matchfail_app_r. 
 assert(normal P1 /\ normal P2) by (inversion H4; inversion H2; split_all). inversion H0.
 inversion H6. subst. 
eapply2 matchfail_app_l.  repeat eapply2 nf_compound. 
eapply2 matchfail_app_r. repeat eapply2 nf_compound. 
eapply2 matchfail_app_r. repeat eapply2 nf_compound. 
eapply2 match_app. eapply2 match_app. 
eapply2 matchfail_app_r. 
Qed. 


Lemma matchfail_app_comb2: 
forall P1 P2 M1 M2, matchfail (app_comb P1 P2) (app_comb M1 M2) -> 
matchfail (App (App (Op Sop) P1) P2) (App (App (Op Sop) M1) M2).
Proof. 
intros. unfold app_comb; unfold_op.
inversion H; subst; split_all.  inversion H6; subst. inversion H9. 
assert False by eapply2 H2. noway. 
(* 2 *) 
inversion H10; subst. inversion H13; subst. inversion H16; subst. 
assert False by eapply2 H2. noway. 
inversion H17; subst. inversion H20; subst. inversion H23. 
assert False by eapply2 H2. noway. inversion H24. 
assert False by eapply2 H2. noway. 
eapply2 matchfail_app_l. repeat eapply2 nf_compound; inversion H18; auto. 
inversion H11; inversion H26; auto. 
inversion H11; inversion H26; auto. 
eapply2 matchfail_app_r. repeat eapply2 nf_compound. inversion H18; auto. 
inversion H13.  inversion H19. subst. 
inversion H14. inversion H21. inversion H32. assert False by eapply2 H35. noway. 
inversion H33. assert False by eapply2 H36. noway. 
eapply2 matchfail_app_r. repeat eapply2 nf_compound. 
inversion H11; inversion H21; inversion H27; auto. 
inversion H17; auto. inversion H17; auto. 
inversion H7 .  inversion H10. 
inversion H17. assert False by eapply2 H20. noway. 
inversion H18. inversion H25. assert False by eapply2 H28. noway. 
inversion H26. assert False by eapply2 H29. noway. 
inversion H11. inversion H18. assert False by eapply2 H21. noway. 
inversion H19. assert False by eapply2 H22. noway. 
Qed. 



Lemma matchfail_fix_comb: forall P M, matchfail P M -> matchfail (fix_comb P) (fix_comb M).
Proof. 
intros. unfold fix_comb.
eapply2 matchfail_app_comb. 
eapply2 matchfail_app_r. repeat eapply2 nf_compound. inversion H; auto. 
eapply2 program_matching. split_all. 
Qed. 
