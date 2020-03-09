From stdpp Require Import sorting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl auth list frac_auth gmap gset.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode notation.
From iris_examples Require Import treiber2.
From play Require Import history.

Section stack_stuff.
  Typeclasses Transparent is_stack stack_cont.
  Context `{!heapG Σ, !stackG Σ}.
  Global Instance is_stack_persistent N l γ : Persistent (is_stack N l γ).
  Proof. apply _. Qed.
  Global Instance stack_cont_laterable l γ : Laterable (stack_cont l γ).
  Proof. apply _. Qed.
  Global Instance stack_cont_timeless l γ : Timeless (stack_cont l γ).
  Proof. apply _. Qed.
  Global Instance to_val_inj : Inj (=) (=) to_val.
  Proof. intros l1 l2 H. case l1, l2; try done. inversion H. reflexivity. Qed.
  Typeclasses Opaque is_stack stack_cont.
End stack_stuff.
Local Hint Extern 0 (environments.envs_entails _ (phys_stack _ [])) => iExists None : core.
Local Hint Extern 0 (environments.envs_entails _ (phys_stack _ (_ :: _))) => iExists (Some _) : core.
Local Hint Extern 10 (environments.envs_entails _ (phys_stack _ _)) => unfold phys_stack : core.
Local Hint Extern 0 (environments.envs_entails _ (phys_list None [])) => simpl : core.
Local Hint Extern 0 (environments.envs_entails _ (phys_list (Some _) (_ :: _))) => simpl : core.

(* NOTE: iFrame may fail for Opaque definitions  *)
Typeclasses Transparent hist hist_snap stack_cont.
Section spec.
  Inductive stack_op := Push of val | Pop of val.
  Canonical Structure stack_opO := leibnizO stack_op.
  Definition Hist := @Hist stack_opO.

  Context `{!heapG Σ, !stackG Σ, !@histG stack_opO Σ} (N : namespace).

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

  (* TODO: need to track last timestamp? *)
  Definition stack_hist γs γh l :=
    inv N (∃ hs t xs, phys_stack l xs ∗ own γs (● Excl' xs) ∗
                      hist γh hs t ∗ ⌜stack_hist_cont hs = Some xs⌝).

  (* impossible? stack_hist γs γh l -∗ is_stack γs l. *)

  (* TODO: what rel for stack_cont and hist_snap? *)
  Definition stack_hist_snap γs γh q xs hs : iProp Σ :=
    stack_cont γs xs ∗
    hist_snap γh q hs ∗
    ⌜∃ hsM tM, hs ≼ hsM ∧ hist_gapless tM hsM ∧ stack_hist_cont hsM = Some xs⌝.

  Lemma new_stack_spec_hist :
    {{{ True }}}
      new_stack #()
    {{{ l γs γh, RET #l; stack_hist γs γh l ∗ stack_hist_snap γs γh 1 [] ε }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iApply wp_fupd.
    wp_lam. wp_alloc l as "Hl".
    iMod (own_alloc (● (Excl' []) ⋅ ◯ (Excl' []))) as (γs) "[Hs● Hs◯]";
      first by apply auth_both_valid.
    iMod hist_alloc as (γh) "[Hh● Hh◯]".
    iMod (inv_alloc N _
                    (∃ (hs : Hist) t xs,
                        phys_stack l xs ∗ own γs (● Excl' xs) ∗
                        hist γh hs t ∗ ⌜stack_hist_cont hs = Some xs⌝)
            with "[Hl Hs● Hh●]").
    { iNext; iExists ε, O, []. iFrame. iSplitL "Hl". eauto with iFrame.
      iPureIntro. apply stack_hist_cont_empty. }
    iModIntro. iApply "HΦ". iFrame. iPureIntro. by exists ε, O.
  Qed.


  Lemma push_stack_spec_hist (l : loc) (γs γh : gname) (v : val) :
    stack_hist γs γh l -∗
    <<< ∀ xs q hs, stack_hist_snap γs γh q xs hs >>>
      push_stack v #l @ ⊤ ∖ ↑N
    <<< ∃ (t:nat), stack_hist_snap γs γh q (v::xs) (<[t := Excl (Push v)]> hs) ∗
                 ⌜∀ (t':nat), t' ∈ (dom (gset nat) hs) → t' < t⌝,
        RET #() >>>.
  Proof.
    iIntros "#SH" (Φ) "AU". iLöb as "IH".
    wp_lam; wp_let; wp_bind (! _)%E.
    iInv "SH" as (hsM tM xs) ">(HPhys & Hs● & Hh● & %)". rename H0 into Hcont.
    iDestruct "HPhys" as (w) "[Hl HPhys]".
    wp_load. iModIntro. iSplitR "AU"; first by eauto 10 with iFrame.
    clear Hcont hsM tM xs.

    wp_alloc r as "Hr". wp_inj. wp_bind (CmpXchg _ _ _)%E.
    iInv "SH" as (hsM tM ys) ">(HPhys & Hs● & Hh● & %)". rename H0 into Hcont.
    iDestruct "HPhys" as (u) "[Hl HPhys]".
    destruct (decide (u = w)) as [[= ->]|NE].
    - wp_cmpxchg_suc; first by case w; left. (* TODO: solve_vals_compare_safe doesn't work *)
      iMod "AU" as (zs q hs) "[(Hs◯ & Hh◯ & %) [_ HClose]]". rename H0 into Hcont_frag.
      iDestruct (auth_agree with "Hs● Hs◯") as %->.

      (* TODO: just to extract pure stuff. simpler solution? *)
      iDestruct "Hh●" as "[Hh● Hg]". iDestruct "Hg" as %Hg.
      iAssert (⌜hist_gapless tM hsM⌝)%I as "Hg"; first done.
      iDestruct (own_valid_2 with "Hh● Hh◯") as %Hincl%frac_auth_included_total.
      iCombine "Hh●" "Hg" as "Hh●". iClear "Hg".

      iMod (auth_update γs (v::zs) with "Hs● Hs◯") as "[Hs● Hs◯]".
      iMod (hist_update γh q hsM hs tM (Push v) with "Hh● Hh◯") as "[Hh● Hh◯]".
      rewrite /stack_hist_snap /hist /hist_snap.
      iDestruct "Hh●" as "[Hh● %]". rename H0 into Hg'.
      set hsM' := <[tM:=Excl (Push v)]> hsM.
      set hs' := <[tM:=Excl (Push v)]> hs.
      (* pure assertions to close AU *)
      iDestruct (own_valid_2 with "Hh● Hh◯") as %Hincl'%frac_auth_included_total.
      assert (stack_hist_cont hsM' = Some (v :: zs)) as Hcont' by by apply stack_hist_cont_push.
      assert (∀ t' : nat, t' ∈ dom (gset nat) hs → t' < tM).
      { inversion Hg as [_ Hdom_hsM]. apply (dom_included hs hsM) in Hincl. intros t' Ht'.
        rewrite ->(elem_of_subseteq) in Hincl. specialize (Hincl t' Ht'). apply Hdom_hsM in Hincl. lia. }
      iMod ("HClose" with "[Hs◯ Hh◯]") as "HΦ".
      iFrame. iPureIntro. split; [by exists hsM', (S tM) | done].
      iModIntro. iSplitR "HΦ". (* TODO: cleanup *)
      + iModIntro. iExists hsM', (S tM), (v::zs). iFrame "∗ %". iExists (Some r). iFrame. simpl.
        iExists w. iFrame. iExists 1%Qp. iFrame.
      + by wp_pures.
    - wp_cmpxchg_fail.
      { exact: not_inj. }
      { case u, w; simpl; eauto. }
      iModIntro. iSplitL "Hs● Hh● Hl HPhys"; first by eauto 10 with iFrame.
      wp_pures. iApply "IH". iExact "AU".
  Qed.

  Lemma pop_stack_spec (l : loc) (γs γh : gname) :
    stack_hist γs γh l -∗
    <<< ∀ xs q hs, stack_hist_snap γs γh q xs hs >>>
      pop_stack #l @ ⊤ ∖ ↑N
    <<< match xs with
        | [] => stack_hist_snap γs γh q [] hs
        | v::xs' => ∃ (t:nat), stack_hist_snap γs γh q (xs') (<[t := Excl (Pop v)]> hs) ∗
                 ⌜∀ (t':nat), t' ∈ (dom (gset nat) hs) → t' < t⌝
        end,
        RET match xs with
            | [] => NONEV
            | v::_ => SOMEV v
            end >>>.
  Proof.
    iIntros "#SH" (Φ) "AU". iLöb as "IH". wp_lam. wp_bind (! _)%E.
    iInv "SH" as (hsM tM xs) ">(HPhys & Hs● & Hh● & %)". rename H0 into Hcont.
    iDestruct "HPhys" as (w) "[Hl HPhys]".
    wp_load.
    iDestruct (phys_list_dup with "HPhys") as "[HPhys1 HPhys2]".
    destruct w as [w|], xs as [|x xs]; try done; simpl.
    - (* non-empty stack *)
      iModIntro. iSplitL "Hl Hs● Hh● HPhys1"; first by eauto 10 with iFrame.
      clear Hcont hsM tM.
      wp_let. wp_match. iDestruct "HPhys2" as (r wq) "[Hw HP]".
      wp_load. wp_let. wp_proj. wp_bind (CmpXchg _ _ _)%E.
      iInv "SH" as (hsM tM ys) ">(HPhys & Hs● & Hh● & %)". rename H0 into Hcont.
      iDestruct "HPhys" as (u) "[Hl HPhys]".
      iClear "HP". clear xs.
      destruct (decide (u = Some w)) as [[= ->]|Hx].
      + wp_cmpxchg_suc.
        destruct ys; first done.
        iMod "AU" as (zs q hs) "[(Hs◯ & Hh◯ & %) [_ HClose]]". rename H0 into Hcont_frag.

        (* TODO: extracting pure stuff *)
        iDestruct "Hh●" as "[Hh● Hg]". iDestruct "Hg" as %Hg.
        iAssert (⌜hist_gapless tM hsM⌝)%I as "Hg"; first done.
        iDestruct (own_valid_2 with "Hh● Hh◯") as %Hincl%frac_auth_included_total.
        iCombine "Hh●" "Hg" as "Hh●". iClear "Hg".

        iDestruct (auth_agree with "Hs● Hs◯") as %<-.
        iMod (auth_update γs ys with "Hs● Hs◯") as "[Hs● Hs◯]".
        iDestruct "HPhys" as (u wq') "[Hw' HPhys]".
        iDestruct (mapsto_agree with "Hw Hw'") as %[=-> ->%to_val_inj].

        iMod (hist_update γh q hsM hs tM (Pop v) with "Hh● Hh◯") as "[Hh● Hh◯]".
        iDestruct "Hh●" as "[Hh● %]". rename H0 into Hg'.
        set hsM' := <[tM:=Excl (Pop v)]> hsM.
        set hs' := <[tM:=Excl (Pop v)]> hs.

        (* pure assertions to close AU *)
        rewrite /stack_hist_snap /hist /hist_snap /stack_cont.
        iDestruct (own_valid_2 with "Hh● Hh◯") as %Hincl'%frac_auth_included_total.
        assert (stack_hist_cont hsM' = Some ys) as Hcont' by by apply stack_hist_cont_pop.
        assert (∀ t' : nat, t' ∈ dom (gset nat) hs → t' < tM).
        { inversion Hg as [_ Hdom_hsM]. apply (dom_included hs hsM) in Hincl. intros t' Ht'.
          rewrite ->(elem_of_subseteq) in Hincl. specialize (Hincl t' Ht'). apply Hdom_hsM in Hincl. lia. }

        iMod ("HClose" with "[Hs◯ Hh◯]") as "HΦ".
        iExists tM. iFrame. iPureIntro. split; [by exists hsM', (S tM) | done].
        iModIntro. iSplitR "HΦ". (* TODO: cleanup *)
        * iModIntro. iExists hsM', (S tM), ys. iFrame "∗ %". unfold phys_stack. iExists u. iFrame.
        * by wp_pures.
      + wp_cmpxchg_fail.
        { intro Heq. apply Hx. destruct u; inversion Heq; done. }
        iModIntro. iSplitR "AU"; first by eauto 10 with iFrame.
        wp_pures. iApply "IH". iExact "AU".
    - (* empty stack *)
      iClear "HPhys1 HPhys2".
      iMod "AU" as (zs q hs) "[(Hs◯ & Hh◯ & %) [_ HClose]]". rename H0 into Hcont_frag. (* TODO: Hcont_frag not needed? *)
      (* TODO: extracting pure stuff *)
      iDestruct "Hh●" as "[Hh● Hg]". iDestruct "Hg" as %Hg.
      iAssert (⌜hist_gapless tM hsM⌝)%I as "Hg"; first done.
      iDestruct (own_valid_2 with "Hh● Hh◯") as %Hincl%frac_auth_included_total.
      iCombine "Hh●" "Hg" as "Hh●". iClear "Hg".

      iDestruct (auth_agree with "Hs● Hs◯") as %<-.
      iMod ("HClose" with "[Hs◯ Hh◯]") as "HΦ".
      { iFrame. by iExists hsM, tM. }
      iModIntro. iSplitR "HΦ"; first by eauto 10 with iFrame.
      wp_pures. iExact "HΦ".
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
