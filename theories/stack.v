From iris_examples Require Import treiber2.
From iris.program_logic Require Import atomic.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import excl auth list frac_auth gmap gset.

Inductive op := Push of valO | Pop of valO.
(* TODO: vs. (before, after) *)
Canonical Structure opO := leibnizO op.

Class histG Σ := HistG {
  hist_inG :> inG Σ (frac_authR (gmapUR nat (exclR opO)))
}.

Definition histΣ : gFunctors :=
  (* #[GFunctor (frac_authR (gmapUR nat (exclR (listO valO))))]. *)
  #[GFunctor (frac_authR (gset_disjUR nat))].

Instance subG_histΣ {Σ} : subG histΣ Σ → histG Σ.
Proof. solve_inG. Qed.

Section spec.
  Context `{!heapG Σ, !stackG Σ, !histG Σ}.

  Definition stackN := nroot .@ "stack".
  Notation is_stack := (is_stack stackN).

  (* TODO apply _ doesn't work? *)
  Global Instance is_stack_persistent l γ : Persistent (is_stack l γ).
  Proof. apply inv_persistent. Qed.
  Global Instance stack_cont_laterable l γ : Laterable (stack_cont l γ).
  Proof.
    apply timeless_laterable. apply own_timeless. apply auth_frag_discrete.
    apply Some_discrete. apply Excl_discrete. apply ofe_discrete_discrete.
  Qed.

  Definition histN := nroot .@ "hist".
  Definition hist_frag γh q ts := own γh (◯F{q} ts).
  Definition hist_master γh ts := own γh (●F ts).

  (* is_stack : stack_cont = auth mapsto : frag mapsto *)
  Definition hist_inv γs γh : iProp Σ :=
    (∃ ls, stack_cont γs ls) ∗ (∃ ts, hist_master γh ts).

  Definition is_hist γs γh := inv histN (hist_inv γs γh).

  Global Instance is_hist_persistent γs γh  : Persistent (is_hist γs γh).
  Proof. apply _. Qed.
  Global Instance hist_frag_laterable γh q ts : Laterable (hist_frag γh q ts).
  Proof. apply _. Qed.
  Global Instance hist_master_laterable γh ts : Laterable (hist_master γh ts).
  Proof. apply _. Qed.

  Lemma new_stack_spec_hist :
    {{{ True }}}
      new_stack #()
    {{{ l γs γh, RET #l; is_stack l γs ∗ is_hist γs γh ∗ hist_frag γh 1 ε }}}.
  Proof.
    iIntros (Φ) "_ Post".
    iApply wp_fupd.
    wp_lam. wp_alloc ℓ as "Hl".

    iMod (own_alloc (● (Some (Excl [])) ⋅ ◯ (Some (Excl [])))) as (γs) "[Hγs● Hγs◯]";
      first by apply auth_both_valid.
    iMod (inv_alloc stackN _ (stack_inv ℓ γs) with "[Hl Hγs●]") as "#Stack".
    { iNext. rewrite /stack_inv /phys_stack /phys_list.
      iExists []. iFrame. iExists None. by iFrame. }

    iMod (own_alloc (●F ε ⋅ ◯F{1} ε)) as (γh) "[Hγh● Hγh◯]"; first by apply frac_auth_valid.
    iMod (inv_alloc histN _ (hist_inv γs γh) with "[Hγs◯ Hγh●]") as "#Hist".
    { iNext. rewrite /hist_inv. iSplitL "Hγs◯"; eauto. }

    iModIntro. iApply "Post". eauto with iFrame.
  Qed.


  Lemma push_stack_spec_hist (l : loc) (γs γh : gname) (v : val) :
    is_stack l γs -∗ is_hist γs γh -∗
    <<< ∀ q ts, hist_frag γh q ts >>>
      push_stack v #l @ ⊤  ∖ ↑histN (* TODO: what namespace? *)
    (* <<< hist_frag γh q (ts ⋅ {[ t := [] ]}), RET #() >>>. *)
    <<< ∃ t, hist_frag γh q (ts ⋅ GSet {[t]}), RET #() >>>.
  Proof.
    iIntros "#Stack #Hist" (Φ) "AU".
    awp_apply (push_stack_spec stackN with "Stack").
    (* TODO: stackN? *)
    iInv histN as "[Hsc >Hhm]". iDestruct "Hhm" as (ts) "Hhm".
    iAaccIntro with "Hhm".

  Admitted.

  Lemma pop_stack_spec (l : loc) (γs : gname) :
    is_stack l γs -∗
    <<< ∀ (xs : list val), stack_cont γs xs >>>
      pop_stack #l @ ⊤ ∖ ↑stackN
    <<< stack_cont γs (match xs with [] => [] | _::xs => xs end)
      , RET (match xs with [] => NONEV | v::_ => SOMEV v end) >>>.
  Proof.
  Admitted.
End spec.
