Section history.
  Definition Hist := (gmapUR nat (exclR A)).
  Definition hist γh (hs : Hist) t : iProp Σ := own γh (●F hs) ∗ ⌜hist_gapless t hs⌝.
  Definition hist_snap γh q (hs : Hist) : iProp Σ := own γh (◯F{q} hs).
End history.

Section stack.
  Inductive stack_op := Push of val | Pop.
  Canonical Structure stack_opO := leibnizO stack_op.
  Definition Hist := @history.Hist stack_opO.
  Definition Rets := @history.Hist valO.

  Context `{!heapG Σ, !@histG stack_opO Σ, !@histG valO Σ} (N : namespace).

  Definition stack_hist_entry_le : relation (nat * excl stack_op) :=
    λ (x y : (nat * excl stack_op)), x.1 <= y.1.
  Instance stack_hist_entry_le_dec : RelDecision stack_hist_entry_le.
  Proof. refine (λ (x y : (nat * excl stack_op)), decide ((x.1 ?= y.1) ≠ Gt)). Qed.

  (** interpretation of the history (stack content). None indicates that the history is not valid/not full. *)
  Fixpoint stack_hist_cont_aux s (hs : list (nat * excl stack_op)) : option (list val) :=
    match hs with
    | [] => Some s
    | (_, ExclBot) :: _ => None
    | (_, Excl (Push v)) :: hs' => stack_hist_cont_aux (v :: s) hs'
    | (_, Excl Pop) :: hs' =>
      match s with
      | [] => stack_hist_cont_aux [] hs'
      | v' :: s' => stack_hist_cont_aux s' hs'
      end
    end.

  Definition stack_hist_cont (hs : Hist) : option (list val) :=
    stack_hist_cont_aux [] $ merge_sort stack_hist_entry_le $ gmap_to_list hs .

  Definition stack_hist_cont' (hs : Hist) (len : nat) : option (list val) :=
    stack_hist_cont_aux [] $ take len $ merge_sort stack_hist_entry_le $ gmap_to_list hs .

  (** relation between the return value of the operation at `t` and the history up to `t-1` *)
  Definition stack_hist_ret (hs : Hist) t : option valO :=
    match hs !! t with
    | None => None
    | Some ExclBot => None
    | Some (Excl (Push _)) => Some #()
    | Some (Excl Pop) =>
      match t with
      | O => Some #()
      | S t' =>
        match stack_hist_cont' hs t' with
        | None => None
        | Some [] => Some #()
        | Some (v::_) => Some v
        end end end.

  (** γh: history, γr: timestamp ↦ return value of the op *)
  Definition stack_hist γh γr l :=
    inv N (∃ (hsM : Hist) (rsM : Rets) t xs,
              phys_stack l xs ∗ hist γh hsM t ∗ hist γr rsM t ∗
              ⌜stack_hist_cont hsM = Some xs⌝ ∗
              ⌜∀ (t':nat), t' ∈ (dom (gset nat) hsM) → rsM !! t' = Excl <$> stack_hist_ret hsM t'⌝).

  Lemma stack_hist_agree_q :
    ⌜q < 1⌝ -∗
    stack_hist γh γr l -∗
    hist_snap γh q hs -∗
    hist_snap γr q rs -∗
    ⌜∃ hsM xs, hs ≼ hsM ∧ stack_hist_cont hsM = Some xs⌝.
  Admitted.

  Lemma stack_hist_agree_1 :
    stack_hist γh γr l -∗ hist_snap γh 1 hs -∗
    ⌜∃ xs, stack_hist_cont hs = Some xs⌝.
    ...
  Admitted.


  Lemma new_stack_spec :
    {{{ True }}}
      new_stack #()
    {{{ l γh γr, RET #l; stack_hist γh γr l ∗ hist_snap γh 1 ε ∗ hist_snap γr 1 ε}}}.
  Admitted.

  Lemma push_stack_spec (l : loc) (γh γr : gname) (v : val) :
    stack_hist γh γr l -∗
    <<< ∀ q hs rs, hist_snap γh q hs ∗ hist_snap γr q rs >>>
      push_stack v #l @ ⊤ ∖ ↑N
    <<< ∃ (t:nat),
            hist_snap γh q (<[t := Excl (Push v)]> hs) ∗
            hist_snap γr q (<[t := Excl #()]> rs) ∗
            ⌜∀ (t':nat), t' ∈ (dom (gset nat) hs) → t' < t⌝,
        RET #() >>>.
  Admitted.

  Lemma pop_stack_spec (l : loc) (γh γr : gname) :
    stack_hist γh γr l -∗
    <<< ∀ q hs rs, hist_snap γh q hs ∗ hist_snap γr q rs >>>
      pop_stack #l @ ⊤ ∖ ↑N
    <<< ∃ (ret:val) (t:nat),
            hist_snap γh q (<[t := Excl Pop]> hs) ∗
            hist_snap γr q (<[t := Excl ret]> rs) ∗
            ⌜∀ (t':nat), t' ∈ (dom (gset nat) hs) → t' < t⌝,
        RET ret >>>.
  Admitted.

  (* TBD *)
  Lemma drop_stack_spec (l : loc) (γh γr : gname) :
    stack_hist γh γr l -∗
    <<< ∀ q hs rs, hist_snap γh 1 hs ∗ hist_snap γr 1 rs >>>
      drop_stack #l @ ⊤ ∖ ↑N
    <<< ... >>>.
  Admitted.

End stack.
