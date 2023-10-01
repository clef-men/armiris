From iris.proofmode Require Import
  environments
  reduction
  coq_tactics.

From armiris Require Import
  prelude.
From armiris Require Export
  proofmode.
From armiris.language Require Export
  weakestpre.

Implicit Types i l : Z.
Implicit Types w : word.
Implicit Types lbl : label.
Implicit Types r : register.
Implicit Types cond : condition.
Implicit Types blk : block.
Implicit Types v : value.
Implicit Types fl : flags.

Section armiris_GS.
  Context `{!ArmirisProgram}.
  Context `{armiris_GS : !ArmirisGS Σ}.

  Lemma tac_wp_eval blk blk' Q Δ :
    (∀ (blk'' := blk'), blk = blk'') →
    envs_entails Δ (WP blk' {{ Q }}) →
    envs_entails Δ (WP blk {{ Q }}).
  Proof.
    move=> -> //.
  Qed.

  Lemma tac_wp_post Q Δ :
    envs_entails Δ Q →
    envs_entails Δ (WP [] {{ Q }}).
  Proof.
    rewrite envs_entails_unseal -wp_post //.
  Qed.

  Lemma tac_wp_bupd blk Q Δ :
    envs_entails Δ (WP blk {{ |==> Q }}) →
    envs_entails Δ (WP blk {{ Q }}).
  Proof.
    rewrite envs_entails_unseal wp_bupd //.
  Qed.

  Lemma tac_wp_mov r1 v1 r2 v2 blk Q id_r1 id_r2 Δ Δ' :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup id_r1 Δ = Some (false, r1 ↦ᵣ v1)%I →
    envs_lookup id_r2 Δ = Some (false, r2 ↦ᵣ v2)%I →
    match envs_simple_replace id_r1 false (Esnoc Enil id_r1 (r1 ↦ᵣ v2)) Δ' with
    | None =>
        False
    | Some Δ'' =>
        envs_entails Δ'' (WP blk {{ Q }})
    end →
    envs_entails Δ (WP MOV r1 r2 :: blk {{ Q }}).
  Proof.
  Admitted.

  Lemma tac_wp_add r1 v1 r2 i2 i blk Q id_r1 id_r2 Δ Δ' :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup id_r1 Δ = Some (false, r1 ↦ᵣ v1)%I →
    envs_lookup id_r2 Δ = Some (false, r2 ↦ᵣ i2)%I →
    match envs_simple_replace id_r1 false (Esnoc Enil id_r1 (r1 ↦ᵣ (i2 + i))) Δ' with
    | None =>
        False
    | Some Δ'' =>
        envs_entails Δ'' (WP blk {{ Q }})
    end →
    envs_entails Δ (WP ADD r1 [[r2, i]] :: blk {{ Q }}).
  Proof.
  Admitted.

  Lemma tac_wp_sub r1 v1 r2 i2 i blk Q id_r1 id_r2 Δ Δ' :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup id_r1 Δ = Some (false, r1 ↦ᵣ v1)%I →
    envs_lookup id_r2 Δ = Some (false, r2 ↦ᵣ i2)%I →
    match envs_simple_replace id_r1 false (Esnoc Enil id_r1 (r1 ↦ᵣ (i2 - i))) Δ' with
    | None =>
        False
    | Some Δ'' =>
        envs_entails Δ'' (WP blk {{ Q }})
    end →
    envs_entails Δ (WP SUB r1 [[r2, i]] :: blk {{ Q }}).
  Proof.
  Admitted.

  Lemma tac_wp_ldr r1 v' r2 l i v blk Q id_r1 id_r2 id_l Δ Δ' Δ1 Δ2 :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup_delete false id_r1 Δ = Some (false, r1 ↦ᵣ v', Δ1)%I →
    envs_lookup_delete false id_r2 Δ1 = Some (false, r2 ↦ᵣ l, Δ2)%I →
    envs_lookup id_l Δ2 = Some (false, (l + i) ↦ₕ v)%I →
    match envs_simple_replace id_r1 false (Esnoc Enil id_r1 (r1 ↦ᵣ v)) Δ' with
    | None =>
        False
    | Some Δ'' =>
        envs_entails Δ'' (WP blk {{ Q }})
    end →
    envs_entails Δ (WP LDR r1 [[r2, i]] :: blk {{ Q }}).
  Proof.
  Admitted.

  Lemma tac_wp_str r1 v r2 l i v' blk Q id_r1 id_r2 id_l Δ Δ' Δ1 Δ2 :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup_delete false id_r1 Δ = Some (false, r1 ↦ᵣ v, Δ1)%I →
    envs_lookup_delete false id_r2 Δ1 = Some (false, r2 ↦ᵣ l, Δ2)%I →
    envs_lookup id_l Δ2 = Some (false, (l + i) ↦ₕ v')%I →
    match envs_simple_replace id_l false (Esnoc Enil id_l ((l + i) ↦ₕ v)) Δ' with
    | None =>
        False
    | Some Δ'' =>
        envs_entails Δ'' (WP blk {{ Q }})
    end →
    envs_entails Δ (WP STR r1 [[r2, i]] :: blk {{ Q }}).
  Proof.
  Admitted.

  Lemma tac_wp_cmp r1 w1 r2 w2 fl blk Q id_r1 id_r2 id_fl Δ Δ' :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup id_r1 Δ = Some (false, r1 ↦ᵣ w1)%I →
    envs_lookup id_r2 Δ = Some (false, r2 ↦ᵣ w2)%I →
    envs_lookup id_fl Δ = Some (false, flags↦ fl)%I →
    match envs_simple_replace id_fl false (Esnoc Enil id_fl (flags↦ (w1, w2))) Δ' with
    | None =>
        False
    | Some Δ'' =>
        envs_entails Δ'' (WP blk {{ Q }})
    end →
    envs_entails Δ (WP CMP r1 r2 :: blk {{ Q }}).
  Proof.
  Admitted.

  Lemma tac_wp_b lbl blk' blk Q Δ Δ' :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    armiris_prog !! lbl = Some blk' →
    envs_entails Δ' (WP blk' {{ Q }}) →
    envs_entails Δ (WP B lbl :: blk {{ Q }}).
  Proof.
  Admitted.

  Lemma tac_wp_bcond cond lbl blk' fl blk Q id Δ Δ' :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    armiris_prog !! lbl = Some blk' →
    envs_lookup id Δ = Some (false, flags↦ fl)%I →
    envs_entails Δ' (WP if condition_eval cond fl then blk' else blk {{ Q }}) →
    envs_entails Δ (WP BCOND cond lbl :: blk {{ Q }}).
  Proof.
  Admitted.

  Lemma tac_wp_br r blk' blk Q id Δ Δ' :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup id Δ = Some (false, r ↦ᵣ blk')%I →
    envs_entails Δ' (WP blk' {{ Q }}) →
    envs_entails Δ (WP BR r :: blk {{ Q }}).
  Proof.
  Admitted.

  Lemma tac_wp_bl lbl blk' v blk Q id Δ Δ' :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    armiris_prog !! lbl = Some blk' →
    envs_lookup id Δ = Some (false, X30 ↦ᵣ v)%I →
    match envs_simple_replace id false (Esnoc Enil id (X30 ↦ᵣ blk)) Δ' with
    | None =>
        False
    | Some Δ'' =>
        envs_entails Δ'' (WP blk' {{ Q }})
    end →
    envs_entails Δ (WP BL lbl :: blk {{ Q }}).
  Proof.
  Admitted.

  Lemma tac_wp_blr r blk' v blk Q id_r id_x30 Δ Δ' :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup id_r Δ = Some (false, r ↦ᵣ blk')%I →
    envs_lookup id_x30 Δ = Some (false, X30 ↦ᵣ v)%I →
    match envs_simple_replace id_x30 false (Esnoc Enil id_x30 (X30 ↦ᵣ blk)) Δ' with
    | None =>
        False
    | Some Δ'' =>
        envs_entails Δ'' (WP blk' {{ Q }})
    end →
    envs_entails Δ (WP BLR r :: blk {{ Q }}).
  Proof.
  Admitted.
End armiris_GS.

#[local] Ltac on_wp tac :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?blk ?Q) =>
      tac blk Q
  | _ =>
      fail "not a 'wp'"
  end.

Tactic Notation "wp_eval" tactic3(tac) :=
  on_wp ltac:(fun blk _ =>
    notypeclasses refine (tac_wp_eval blk _ _ _ _ _);
    [ let x := fresh in intros x; tac; unfold x; notypeclasses refine eq_refl
    | idtac
    ]
  ).

Ltac wp_simpl :=
  wp_eval simpl.

Ltac wp_bupd :=
  on_wp ltac:(fun _ Q =>
    tryif assert (∀ P, AddModal (|==> P) P Q) as _ by tc_solve then (
      idtac
    ) else (
      eapply tac_wp_bupd
    )
  ).

Ltac wp_post :=
  wp_bupd;
  eapply tac_wp_post;
  try iSmash+.

Ltac wp_finish :=
  wp_simpl;
  try wp_post;
  pm_prettify.

Ltac wp_mov :=
  on_wp ltac:(fun _ _ =>
    tryif eapply tac_wp_mov then idtac else (
      fail "wp_mov: not a 'MOV'"
    );
    [ tc_solve
    | iAssumptionCore ||
      let r := match goal with |- _ = Some (_, registers_mapsto ?r _) => r end in
      fail "wp_mov: cannot find" r "↦ᵣ ?"
    | iAssumptionCore ||
      let r := match goal with |- _ = Some (_, registers_mapsto ?r _) => r end in
      fail "wp_mov: cannot find" r "↦ᵣ ?"
    | pm_reduce;
      wp_finish
    ]
  ).

Ltac wp_add :=
  on_wp ltac:(fun _ _ =>
    tryif eapply tac_wp_add then idtac else (
      fail "wp_add: not a 'ADD'"
    );
    [ tc_solve
    | iAssumptionCore ||
      let r := match goal with |- _ = Some (_, registers_mapsto ?r _) => r end in
      fail "wp_add: cannot find" r "↦ᵣ ?"
    | iAssumptionCore ||
      let r := match goal with |- _ = Some (_, registers_mapsto ?r _) => r end in
      fail "wp_add: cannot find" r "↦ᵣ ?"
    | pm_reduce;
      wp_finish
    ]
  ).

Ltac wp_sub :=
  on_wp ltac:(fun _ _ =>
    tryif eapply tac_wp_sub then idtac else (
      fail "wp_sub: not a 'ADD'"
    );
    [ tc_solve
    | iAssumptionCore ||
      let r := match goal with |- _ = Some (_, registers_mapsto ?r _) => r end in
      fail "wp_sub: cannot find" r "↦ᵣ ?"
    | iAssumptionCore ||
      let r := match goal with |- _ = Some (_, registers_mapsto ?r _) => r end in
      fail "wp_sub: cannot find" r "↦ᵣ ?"
    | pm_reduce;
      wp_finish
    ]
  ).

Ltac wp_ldr :=
  on_wp ltac:(fun _ _ =>
    tryif eapply tac_wp_ldr then idtac else (
      fail "wp_ldr: not a 'LDR'"
    );
    [ tc_solve
    | iAssumptionCore ||
      let r := match goal with |- _ = Some (_, registers_mapsto ?r _, _) => r end in
      fail "wp_ldr: cannot find" r "↦ᵣ ?"
    | iAssumptionCore ||
      let r := match goal with |- _ = Some (_, registers_mapsto ?r _, _) => r end in
      fail "wp_ldr: cannot find" r "↦ᵣ ?"
    | iAssumptionCore ||
      let l := match goal with |- _ = Some (_, heap_mapsto ?l _) => l end in
      fail "wp_ldr: cannot find" l "↦ₕ ?"
    | pm_reduce;
      wp_finish
    ]
  ).

Ltac wp_str :=
  on_wp ltac:(fun _ _ =>
    tryif eapply tac_wp_str then idtac else (
      fail "wp_str: not a 'STR'"
    );
    [ tc_solve
    | iAssumptionCore ||
      let r := match goal with |- _ = Some (_, registers_mapsto ?r _, _) => r end in
      fail "wp_str: cannot find" r "↦ᵣ ?"
    | iAssumptionCore ||
      let r := match goal with |- _ = Some (_, registers_mapsto ?r _, _) => r end in
      fail "wp_str: cannot find" r "↦ᵣ ?"
    | iAssumptionCore ||
      let l := match goal with |- _ = Some (_, heap_mapsto ?l _) => l end in
      fail "wp_str: cannot find" l "↦ₕ ?"
    | pm_reduce;
      wp_finish
    ]
  ).

Ltac wp_cmp :=
  on_wp ltac:(fun _ _ =>
    tryif eapply tac_wp_cmp then idtac else (
      fail "wp_cmp: not a 'CMP'"
    );
    [ tc_solve
    | iAssumptionCore ||
      let r := match goal with |- _ = Some (_, registers_mapsto ?r _) => r end in
      fail "wp_cmp: cannot find" r "↦ᵣ ?"
    | iAssumptionCore ||
      let r := match goal with |- _ = Some (_, registers_mapsto ?r _) => r end in
      fail "wp_cmp: cannot find" r "↦ᵣ ?"
    | iAssumptionCore ||
      fail "wp_cmp: cannot find flags↦ ?"
    | pm_reduce;
      wp_finish
    ]
  ).

Ltac wp_b :=
  on_wp ltac:(fun _ _ =>
    tryif eapply tac_wp_b then idtac else (
      fail "wp_b: not a 'B'"
    );
    [ tc_solve
    | try done
    | wp_finish
    ]
  ).

Ltac wp_bcond :=
  on_wp ltac:(fun _ _ =>
    tryif eapply tac_wp_bcond then idtac else (
      fail "wp_bcond: not a 'BCOND'"
    );
    [ tc_solve
    | try done
    | iAssumptionCore ||
      fail "wp_bcond: cannot find flags↦ ?"
    | wp_finish
    ]
  ).

Ltac wp_br :=
  on_wp ltac:(fun _ _ =>
    tryif eapply tac_wp_br then idtac else (
      fail "wp_br: not a 'BR'"
    );
    [ tc_solve
    | iAssumptionCore ||
      let r := match goal with |- _ = Some (_, registers_mapsto ?r _) => r end in
      fail "wp_br: cannot find" r "↦ᵣ ?"
    | wp_finish
    ]
  ).

Ltac wp_bl :=
  on_wp ltac:(fun _ _ =>
    tryif eapply tac_wp_bl then idtac else (
      fail "wp_bl: not a 'BL'"
    );
    [ tc_solve
    | try done
    | iAssumptionCore ||
      fail "wp_bl: cannot find X30 ↦ᵣ ?"
    | pm_reduce;
      wp_finish
    ]
  ).

Ltac wp_blr :=
  on_wp ltac:(fun _ _ =>
    tryif eapply tac_wp_blr then idtac else (
      fail "wp_blr: not a 'BLR'"
    );
    [ tc_solve
    | iAssumptionCore ||
      let r := match goal with |- _ = Some (_, registers_mapsto ?r _) => r end in
      fail "wp_blr: cannot find" r "↦ᵣ ?"
    | iAssumptionCore ||
      fail "wp_blr: cannot find X30 ↦ᵣ ?"
    | pm_reduce;
      wp_finish
    ]
  ).

Ltac wp_step :=
  on_wp ltac:(fun blk _ =>
    let blk := eval hnf in blk in
    lazymatch blk with
    | [] =>
        wp_post
    | ?instr :: _ =>
        lazymatch instr with
        | MOV _ _ =>
            wp_mov
        | ADD _ _ =>
            wp_add
        | SUB _ _ =>
            wp_sub
        | LDR _ _ =>
            wp_ldr
        | STR _ _ =>
            wp_str
        | CMP _ _ =>
            wp_cmp
        | B _ =>
            wp_b
        | BCOND _ _ =>
            wp_bcond
        | BR _ =>
            wp_br
        | BL _ =>
            wp_bl
        | BLR _ =>
            wp_blr
        end
    end
  ).
Tactic Notation "wp_steps" :=
  repeat wp_step.
Tactic Notation "wp_steps" integer(n) :=
  do n wp_step.
