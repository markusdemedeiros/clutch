From clutch.ub_logic Require Export ub_clutch lib.map hash lib.list.
Import Hierarchy.
Set Default Proof Using "Type*".
Open Scope nat.

Section merkle_tree.
  Context `{!ub_clutchGS Σ}.
  Variables height:nat.
  Variables val_bit_size':nat.
  Variables max_hash_size : nat.
  Definition val_bit_size : nat := S val_bit_size'.
  Definition val_size:nat := (2^val_bit_size)-1.
  Variable (Hineq: (max_hash_size <= val_size)%nat).
  Definition leaf_bit_size : nat := 2*val_bit_size.
  (* Definition identifier : nat := 2^leaf_bit_size. *)
  Definition num_of_leafs : nat := 2^height.
  
  Inductive merkle_tree :=
  | Leaf (hash_value : nat) (leaf_value:nat)
  | Branch (hash_value : nat) (t1 t2:merkle_tree).

  Definition root_hash_value (t: merkle_tree) :=
    match t with
    | Leaf h _ => h
    | Branch h _ _ => h
    end.

  Inductive tree_relate: nat -> val -> merkle_tree -> Prop:=
  | tree_relate_lf (hv v:nat): tree_relate 0 (InjLV (#hv, #v)) (Leaf hv v)
  | tree_relate_br n (hv:nat) ll l lr r:
    tree_relate n ll l ->
    tree_relate n lr r ->
    tree_relate (S n) (InjRV (#hv, ll, lr)) (Branch hv l r)
  .

  Inductive tree_valid: merkle_tree -> gmap nat Z -> Prop :=
  |tree_valid_lf (h l:nat) m:
    h < 2^val_bit_size ->
    l < 2^leaf_bit_size ->
    m!!l%nat = Some (Z.of_nat h) ->
    tree_valid (Leaf h l) m
  |tree_valid_br (h:nat) l r m:
    tree_valid l m ->
    tree_valid r m ->
    h < 2^val_bit_size ->
    m!!((root_hash_value l)*2^val_bit_size + root_hash_value r)%nat=Some (Z.of_nat h) ->
    tree_valid (Branch h l r) m.
    

  Definition map_valid (m:gmap nat Z) : Prop := coll_free m.

  Definition root_hash_value_program : val :=
    λ: "ltree",
      match: "ltree" with
      | InjL "x" => Fst "x"
      | InjR "x" => let, ("a", "b", "c") := "x" in "a"
      end.

  Definition compute_hash_from_leaf : val :=
    rec: "compute_hash_from_leaf" "ltree" "lhmf" "ll" "lleaf" := 
    match: "ltree" with
    | InjL "x" => "lhmf" "lleaf"  
    | InjR "x"  => let: "b" := (match: list_head "ll" with
                               | SOME "a" => "a"
                               | NONE => #()
                               end
                              ) in
                  let: "ll'" := list_tail "ll"  in
                  let, ("notneeded", "l", "r") := "x" in
                  if: "b"
                  then "lhmf"
                         (("compute_hash_from_leaf" "l" "lhmf" "ll'" "lleaf")*#(2^val_bit_size)+
                            root_hash_value_program "r")
                  else "lhmf"
                         ((root_hash_value_program "l")*#(2^val_bit_size)+("compute_hash_from_leaf" "r" "lhmf" "ll'" "lleaf"))
    end

  .

  Inductive tree_value_match: merkle_tree -> nat -> list bool -> Prop:=
  | tree_value_match_lf h lf: tree_value_match (Leaf h lf) lf []
  | tree_value_match_left h l r xs v:
    tree_value_match l v xs ->
    tree_value_match (Branch h l r) v (true::xs)
  | tree_value_match_right h l r xs v:
    tree_value_match r v xs ->
    tree_value_match (Branch h l r) v (false::xs).

  (** Lemmas *)
  Lemma wp_root_hash_value_program n lt tree E:
    {{{ ⌜tree_relate n lt tree⌝ }}}
    root_hash_value_program lt @ E
    {{{ (retv:Z), RET #retv; ⌜retv = root_hash_value tree⌝}}}.
  Proof.
    iIntros (Φ) "%H HΦ".
    rewrite /root_hash_value_program. wp_pures.
    inversion H.
    - wp_pures. iApply "HΦ". by iPureIntro.
    - wp_pures. iApply "HΦ". by iPureIntro.
  Qed.

  (** Spec *)
  Lemma wp_compute_hash_from_leaf_correct (ltree:val) (tree:merkle_tree) (m:gmap nat Z) (v:nat) (path:list bool) llist f E:
     {{{ ⌜tree_relate height ltree tree⌝ ∗
        ⌜tree_valid tree m⌝ ∗
        hashfun_amortized (val_size-1)%nat max_hash_size f m ∗
        ⌜is_list path llist⌝ ∗
        ⌜tree_value_match tree v path⌝ ∗
        ⌜map_valid m⌝ }}}
      compute_hash_from_leaf ltree f llist (#v) @ E
      {{{ (retv:Z), RET #retv;
          hashfun_amortized (val_size-1) max_hash_size f m ∗
          ⌜retv = root_hash_value tree⌝
      }}}.
  Proof.
    iIntros (Φ) "(%Htrelate&%Htvalid&H&%Hlsit&%Hvmatch&%Hmvalid) HΦ".
    iInduction tree as [|] "IH"
                         forall (height ltree v path llist f Htrelate Htvalid Hlsit Hvmatch Hmvalid Φ).
    - rewrite /compute_hash_from_leaf.
      wp_pures. inversion Htrelate; subst. 
      wp_match.
      inversion Htrelate. inversion Htvalid. inversion Hvmatch. subst.
      wp_apply (wp_hashfun_prev_amortized with "[$]").
      + lia.
      + done. 
      + iIntros. iApply "HΦ". iFrame. by iPureIntro. 
    - rewrite /compute_hash_from_leaf.
      inversion Htrelate. inversion Htvalid. inversion Hvmatch; subst.
      + wp_pures. wp_apply wp_list_head; first done. iIntros (v') "[[%%]|(%&%&%&%)]"; first done.
        subst. inversion H; subst. wp_pures. rewrite -/compute_hash_from_leaf.
        wp_apply wp_list_tail; first done. iIntros (v') "%". wp_pures.
        wp_apply wp_root_hash_value_program; try done.
        iIntros (x) "->".
        wp_apply ("IH" with "[][][][][][H][HΦ]"); try done.
        iModIntro. iIntros (?) "[H ->]".
        wp_pures.
        replace (_*_+_)%Z with (Z.of_nat (root_hash_value tree1 * 2 ^ val_bit_size + root_hash_value tree2)); last first.
        { rewrite Nat2Z.inj_add. f_equal. rewrite Nat2Z.inj_mul. f_equal.
          apply Z2Nat.inj_pow.
        }
        wp_apply (wp_hashfun_prev_amortized with "H").
        * lia.
        * done.
        * iIntros "H". iApply "HΦ". iFrame.
          done.
      + wp_pures. wp_apply wp_list_head; first done. iIntros (v') "[[%%]|(%&%&%&%)]"; first done.
        subst. inversion H; subst. wp_pures. rewrite -/compute_hash_from_leaf.
        wp_apply wp_list_tail; first done. iIntros (v') "%". wp_pures.
        wp_apply ("IH1" with "[][][][][][H][HΦ]"); try done.
        iModIntro. iIntros (?) "[H ->]".
        wp_apply wp_root_hash_value_program; try done.
        iIntros (x) "->".
        wp_pures.
        replace (_*_+_)%Z with (Z.of_nat (root_hash_value tree1 * 2 ^ val_bit_size + root_hash_value tree2)); last first.
        { rewrite Nat2Z.inj_add. f_equal. rewrite Nat2Z.inj_mul. f_equal.
          apply Z2Nat.inj_pow.
        }
        wp_apply (wp_hashfun_prev_amortized with "H").
        * lia.
        * done.
        * iIntros "H". iApply "HΦ". iFrame.
          done.
  Qed.
  
          
  
End merkle_tree.
