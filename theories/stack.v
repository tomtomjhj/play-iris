From stdpp Require Import sorting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl auth list frac_auth gmap gset.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode notation.
From iris_examples Require Import treiber2.
From play Require Import history.

Instance to_val_inj : Inj (=) (=) to_val.
Proof. intros l1 l2 H. case l1, l2; try done. by inversion H. Qed.

Local Hint Extern 0 (environments.envs_entails _ (phys_stack _ [])) => iExists None : core.
Local Hint Extern 0 (environments.envs_entails _ (phys_stack _ (_ :: _))) => iExists (Some _) : core.
Local Hint Extern 10 (environments.envs_entails _ (phys_stack _ _)) => unfold phys_stack : core.
Local Hint Extern 0 (environments.envs_entails _ (phys_list None [])) => simpl : core.
Local Hint Extern 0 (environments.envs_entails _ (phys_list (Some _) (_ :: _))) => simpl : core.

(* NOTE: iFrame may fail for Opaque definitions  *)
Typeclasses Transparent hist hist_snap.
Section spec.
  Inductive stack_op := Push of val | Pop of val.
  Canonical Structure stack_opO := leibnizO stack_op.
  Definition Hist := @Hist stack_opO.

  Context `{!heapG Σ, !@histG stack_opO Σ} (N : namespace).

  Definition stack_hist_entry_le : relation (nat * excl stack_op) :=
    λ (x y : (nat * excl stack_op)), x.1 <= y.1.
  Instance stack_hist_entry_le_dec : RelDecision stack_hist_entry_le.
  Proof. refine (λ (x y : (nat * excl stack_op)), decide ((x.1 ?= y.1) ≠ Gt)). Qed.

  Fixpoint stack_hist_cont_aux s (hs : list (nat * excl stack_op)) : option (list val) :=
    match hs with
    | [] => Some s
    | (_, ExclBot) :: _ => None
    | (_, Excl (Push v)) :: hs' => stack_hist_cont_aux (v :: s) hs'
    | (_, Excl (Pop v)) :: hs' =>
      match s with
      | [] => None
      | v' :: s' => if decide (v = v') then stack_hist_cont_aux s' hs' else None
      end
    end.

  Definition stack_hist_cont (hs : Hist) : option (list val) :=
    stack_hist_cont_aux [] $ merge_sort stack_hist_entry_le $ gmap_to_list hs .

  (* TODO: use relation? *)

  (* Fixpoint stack_hist_cont_aux (hs : Hist) s l : option (list val) :=
       match l with
       | O => Some s
       | S l' =>
         match hs !! l' with
         | None => None
         | Some ExclBot => None
         | Some (Excl (Push v)) => stack_hist_cont_aux hs (v :: s) l'
         | Some (Excl (Pop v)) =>
           match s with
           | [] => None
           | v' :: s' => if decide (v = v') then stack_hist_cont_aux hs s' l' else None
           end
         end
       end.

     Definition stack_hist_cont hs l : option (list val) :=
       stack_hist_cont_aux hs [] l. *)

  Lemma stack_hist_cont_empty : stack_hist_cont ε = Some [].
  Proof. by vm_compute. Qed.

  Lemma stack_hist_cont_push t hs v xs:
    hist_gapless t hs ->
    stack_hist_cont hs = Some xs ->
    stack_hist_cont (<[t:=Excl (Push v)]> hs) = Some (v::xs).
  Proof.
  Admitted.

  Lemma stack_hist_cont_pop t hs v xs:
    hist_gapless t hs ->
    stack_hist_cont hs = Some (v::xs) ->
    stack_hist_cont (<[t:=Excl (Pop v)]> hs) = Some xs.
  Proof.
  Admitted.

  (* NOTE: the client with full ownership should be able to assemble the history
     into a valid stack representation *)
  Definition stack_hist γh l :=
    inv N (∃ hs t xs, phys_stack l xs ∗ hist γh hs t ∗ ⌜stack_hist_cont hs = Some xs⌝).

  Lemma new_stack_spec_hist :
    {{{ True }}}
      new_stack #()
    {{{ l γh, RET #l; stack_hist γh l ∗ hist_snap γh 1 ε }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iApply wp_fupd.
    wp_lam. wp_alloc l as "Hl".
    iMod hist_alloc as (γh) "[Hh● Hh◯]".
    iMod (inv_alloc
            N _ (∃ (hs : Hist) t xs,
                    phys_stack l xs ∗ hist γh hs t ∗ ⌜stack_hist_cont hs = Some xs⌝)
            with "[Hl Hh●]").
    { iNext; iExists ε, O, []. iFrame. iSplitL "Hl". eauto with iFrame.
      iPureIntro. apply stack_hist_cont_empty. }
    iModIntro. iApply "HΦ". iFrame.
  Qed.


  Lemma push_stack_spec_hist (l : loc) (γh : gname) (v : val) :
    stack_hist γh l -∗
    <<< ∀ q hs, hist_snap γh q hs >>>
      push_stack v #l @ ⊤ ∖ ↑N
    <<< ∃ (t:nat), hist_snap γh q (<[t := Excl (Push v)]> hs) ∗
                 ⌜∀ (t':nat), t' ∈ (dom (gset nat) hs) → t' < t⌝,
        RET #() >>>.
  Proof.
    iIntros "#SH" (Φ) "AU". iLöb as "IH".
    wp_lam; wp_let; wp_bind (! _)%E.
    iInv "SH" as (hsM tM xs) ">(HPhys & Hh● & %)". rename H0 into Hcont.
    iDestruct "HPhys" as (w) "[Hl HPhys]".
    wp_load. iModIntro. iSplitR "AU"; first by eauto 10 with iFrame.
    clear Hcont hsM tM xs.

    wp_alloc r as "Hr". wp_inj. wp_bind (CmpXchg _ _ _)%E.
    iInv "SH" as (hsM tM xs) ">(HPhys & Hh● & %)". rename H0 into Hcont.
    iDestruct "HPhys" as (u) "[Hl HPhys]".
    destruct (decide (u = w)) as [[= ->]|NE].
    - wp_cmpxchg_suc; first by case w; left. (* TODO: solve_vals_compare_safe doesn't work *)
      iMod "AU" as (q hs) "[Hh◯ [_ CloseAU]]".

      (* TODO: just to extract pure stuff. simpler solution? *)
      iDestruct "Hh●" as "[Hh● Hg]". iDestruct "Hg" as %Hg.
      iAssert (⌜hist_gapless tM hsM⌝)%I as "Hg"; first done.
      iDestruct (own_valid_2 with "Hh● Hh◯") as %Hincl%frac_auth_included_total.
      iCombine "Hh●" "Hg" as "Hh●". iClear "Hg".

      iMod (hist_update γh q hsM hs tM (Push v) with "Hh● Hh◯") as "[Hh● Hh◯]".
      iDestruct "Hh●" as "[Hh● %]". rename H0 into Hg'.
      set hsM' := <[tM:=Excl (Push v)]> hsM.
      iMod ("CloseAU" with "[Hh◯]") as "HΦ".
      { assert (∀ t' : nat, t' ∈ dom (gset nat) hs → t' < tM).
        inversion Hg as [_ Hdom_hsM]. apply (dom_included hs hsM) in Hincl. intros t' Ht'.
        rewrite ->(elem_of_subseteq) in Hincl. specialize (Hincl t' Ht'). apply Hdom_hsM in Hincl. lia.
        by iFrame "∗ %". }
      iModIntro. iSplitR "HΦ". (* close the invariant *)
      { iExists hsM', (S tM), (v::xs).
        assert (stack_hist_cont hsM' = Some (v :: xs)) as Hcont' by by apply stack_hist_cont_push.
        eauto 10 with iFrame. }
      by wp_pures.
    - wp_cmpxchg_fail.
      { exact: not_inj. }
      { case u, w; simpl; eauto. }
      iModIntro. iSplitL "Hh● Hl HPhys"; first by eauto 10 with iFrame.
      wp_pures. iApply "IH". iExact "AU".
  Qed.

  Lemma pop_stack_spec (l : loc) (γh : gname) :
    stack_hist γh l -∗
    <<< ∀ q hs, hist_snap γh q hs >>>
      pop_stack #l @ ⊤ ∖ ↑N
    <<< ∃ hsM xs,
            (* TODO: the client should be able to know that hsM is the full history *)
            ⌜hs ≼ hsM ∧ stack_hist_cont hsM = Some xs⌝ ∗
            match xs with
            | [] => hist_snap γh q hs
            | v::_ => ∃ (t:nat), hist_snap γh q (<[t := Excl (Pop v)]> hs) ∗
                             ⌜∀ (t':nat), t' ∈ (dom (gset nat) hs) → t' < t⌝
            end,
        RET match xs with
            | [] => NONEV
            | v::_ => SOMEV v
            end >>>.
  Proof.
    iIntros "#SH" (Φ) "AU". iLöb as "IH". wp_lam. wp_bind (! _)%E.
    iInv "SH" as (hsM tM xs) ">(HPhys & Hh● & %)". rename H0 into Hcont.
    iDestruct "HPhys" as (w) "[Hl HPhys]".
    wp_load.
    iDestruct (phys_list_dup with "HPhys") as "[HPhys1 HPhys2]".
    destruct w as [w|], xs as [|x xs]; try done; simpl.
    - (* non-empty stack *)
      iModIntro. iSplitL "Hl Hh● HPhys1". iExists hsM, tM, (x::xs). by eauto 10 with iFrame.
      clear Hcont hsM tM.
      wp_let. wp_match. iDestruct "HPhys2" as (r wq) "[Hw HP]".
      wp_load. wp_let. wp_proj. wp_bind (CmpXchg _ _ _)%E.
      iInv "SH" as (hsM tM ys) ">(HPhys & Hh● & %)". rename H0 into Hcont.
      iDestruct "HPhys" as (u) "[Hl HPhys]".
      iClear "HP". clear xs.
      destruct (decide (u = Some w)) as [[= ->]|Hx].
      + wp_cmpxchg_suc.
        destruct ys; first done.
        iMod "AU" as (q hs) "[Hh◯ [_ CloseAU]]".

        (* TODO: extracting pure stuff *)
        iDestruct "Hh●" as "[Hh● Hg]". iDestruct "Hg" as %Hg.
        iAssert (⌜hist_gapless tM hsM⌝)%I as "Hg"; first done.
        iDestruct (own_valid_2 with "Hh● Hh◯") as %Hincl%frac_auth_included_total.
        iCombine "Hh●" "Hg" as "Hh●". iClear "Hg".

        iDestruct "HPhys" as (u wq') "[Hw' HPhys]".
        iDestruct (mapsto_agree with "Hw Hw'") as %[=-> ->%to_val_inj].

        iMod (hist_update γh q hsM hs tM (Pop v) with "Hh● Hh◯") as "[Hh● Hh◯]".
        iDestruct "Hh●" as "[Hh● %]". rename H0 into Hg'.
        set hsM' := <[tM:=Excl (Pop v)]> hsM.
        iMod ("CloseAU" $! hsM (v::ys) with "[Hh◯]") as "HΦ".
        { assert (∀ t' : nat, t' ∈ dom (gset nat) hs → t' < tM).
          inversion Hg as [_ Hdom_hsM]. apply (dom_included hs hsM) in Hincl. intros t' Ht'.
          rewrite ->(elem_of_subseteq) in Hincl. specialize (Hincl t' Ht'). apply Hdom_hsM in Hincl. lia.
          eauto with iFrame. }
        iModIntro. iSplitR "HΦ". (* close the invariant *)
        { iExists hsM', (S tM), ys.
          assert (stack_hist_cont hsM' = Some ys) as Hcont' by by apply stack_hist_cont_pop.
          eauto 10 with iFrame. }
        by wp_pures.
      + wp_cmpxchg_fail.
        { intro Heq. apply Hx. destruct u; inversion Heq; done. }
        iModIntro. iSplitR "AU"; first by eauto 10 with iFrame.
        wp_pures. iApply "IH". iExact "AU".
    - (* empty stack *)
      iClear "HPhys1 HPhys2".
      iMod "AU" as (q hs) "[Hh◯ [_ CloseAU]]".
      (* TODO: extracting pure stuff *)
      iDestruct "Hh●" as "[Hh● Hg]". iDestruct "Hg" as %Hg.
      iAssert (⌜hist_gapless tM hsM⌝)%I as "Hg"; first done.
      iDestruct (own_valid_2 with "Hh● Hh◯") as %Hincl%frac_auth_included_total.
      iCombine "Hh●" "Hg" as "Hh●". iClear "Hg".

      iMod ("CloseAU" $! hsM [] with "[Hh◯]") as "HΦ"; first by eauto with iFrame.
      iModIntro. iSplitR "HΦ".
      { iExists hsM, tM, []. eauto with iFrame. }
      by wp_pures.
  Qed.

End spec.

From iris.heap_lang Require Import lib.par.
Module client.
  Definition produce (s ap: loc) : val :=
    rec: "produce" "n" "i" :=
      if: "i" = "n" then #()
      else let: "e":= !(#ap +ₗ"i") in
           push_stack "e" #s;;
           "produce" "n" ("i" + #1).

  Definition consume (s ac: loc) : val :=
    rec: "consume" "n" "i" :=
      if: "i" = "n" then #()
      else match: pop_stack #s with
             NONE => "consume" "n" "i"
           | SOME "e" => (#ac + "i") <- "e";;
                        "consume" "n" ("i" + #1)
           end.

  Definition exchange (s ap ac : loc) : val :=
    λ: "n", (produce s ap) "n" #0 ||| (consume s ac) "n" #0.

  (* ap ↦∗ ls ∗ ∃ ls', ac ↦∗ ls' ∗ ⌜Permutation ls ls'⌝
     hist_snap γh 1 hs, pushed hs l1, popped hs l2 -> Permutation l1 l2*)

End client.
