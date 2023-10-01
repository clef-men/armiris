From stdpp Require Import
  functions.

From armiris Require Import
  prelude.
From armiris.language Require Export
  syntax.

Implicit Types i j l : Z.
Implicit Types w : word.
Implicit Types lbl : label.
Implicit Types r : register.
Implicit Types cond : condition.
Implicit Types blk : block.
Implicit Types prog : program.

Inductive value :=
  | ValWord w
  | ValBlock blk.
Implicit Types v : value.

Coercion ValWord : word >-> value.
Coercion ValBlock : block >-> value.
Notation "# w" := (
  ValWord w%Z
)(at level 8,
  format "# w"
).

#[global] Instance value_inhabited : Inhabited value :=
  populate #0.

Definition flags : Type :=
  word * word.
Implicit Types fl : flags.

#[global] Instance flags_inhabited : Inhabited flags :=
  populate (inhabitant, inhabitant).

Record state := {
  state_registers : register → value ;
  state_heap : gmap Z value ;
  state_flags : flags ;
}.
Implicit Types σ : state.

#[global] Instance state_empty : Empty state :=
  {|state_registers := inhabitant ;
    state_heap := ∅ ;
    state_flags := inhabitant ;
  |}.

#[global] Instance state_registers_lookup_total : LookupTotal register value state :=
  λ r σ,
    σ.(state_registers) r.
#[global] Instance state_registers_insert : Insert register value state :=
  λ r v σ,
    {|state_registers := <[r := v]> σ.(state_registers) ;
      state_heap := σ.(state_heap) ;
      state_flags := σ.(state_flags) ;
    |}.

#[global] Instance state_heap_lookup : Lookup Z value state :=
  λ l σ,
    σ.(state_heap) !! l.
#[global] Instance state_heap_insert : Insert Z value state :=
  λ l v σ,
    {|state_registers := σ.(state_registers) ;
      state_heap := <[l := v]> σ.(state_heap) ;
      state_flags := σ.(state_flags) ;
    |}.

#[global] Instance state_flags_update : Update flags state :=
  λ fl σ,
    {|state_registers := σ.(state_registers) ;
      state_heap := σ.(state_heap) ;
      state_flags := fl ;
    |}.

Definition condition_eval cond fl :=
  match cond with
  | CondEq =>
      bool_decide (fl.1 = fl.2)
  | CondNe =>
      bool_decide (fl.1 ≠ fl.2)
  | CondLe =>
      bool_decide (word_to_int fl.1 <= word_to_int fl.2)%Z
  | CondLt =>
      bool_decide (word_to_int fl.1 < word_to_int fl.2)%Z
  | CondGe =>
      bool_decide (word_to_int fl.1 >= word_to_int fl.2)%Z
  | CondGt =>
      bool_decide (word_to_int fl.1 > word_to_int fl.2)%Z
  end.
#[global] Arguments condition_eval !_ _ / : assert.

Inductive prim_step prog blk σ : instruction → block → state → Prop :=
  | prim_step_mov r1 r2 v :
      σ !!! r2 = v →
      prim_step prog blk σ
        (MOV r1 r2)
        blk
        (<[r1 := v]> σ)
  | prim_step_add r1 r2 i j :
      σ !!! r2 = #j →
      prim_step prog blk σ
        (ADD r1 [[r2, i]])
        blk
        (<[r1 := #(j + i)]> σ)
  | prim_step_sub r1 r2 i j :
      σ !!! r2 = #j →
      prim_step prog blk σ
        (SUB r1 [[r2, i]])
        blk
        (<[r1 := #(j - i)]> σ)
  | prim_step_ldr r1 r2 i l v :
      σ !!! r2 = #l →
      σ !! (l + i)%Z = Some v →
      prim_step prog blk σ
        (LDR r1 [[r2, i]])
        blk
        (<[r1 := v]> σ)
  | prim_step_str r1 r2 i v l v' :
      σ !!! r1 = v →
      σ !!! r2 = #l →
      σ !! (l + i)%Z = Some v' →
      prim_step prog blk σ
        (STR r1 [[r2, i]])
        blk
        (<[(l + i)%Z := v]> σ)
  | prim_step_cmp r1 w1 r2 w2 :
      σ !!! r1 = #w1 →
      σ !!! r2 = #w2 →
      prim_step prog blk σ
        (CMP r1 r2)
        blk
        (<[(w1, w2)]> σ)
  | prim_step_b lbl blk' :
      prog !! lbl = Some blk' →
      prim_step prog blk σ
        (B lbl)
        blk'
        σ
  | prim_step_bcond cond lbl blk' fl :
      prog !! lbl = Some blk' →
      σ.(state_flags) = fl →
      prim_step prog blk σ
        (BCOND cond lbl)
        (if condition_eval cond fl then blk' else blk)
        σ
  | prim_step_br r blk' :
      σ !!! r = ValBlock blk' →
      prim_step prog blk σ
        (BR r)
        blk'
        σ
  | prim_step_bl lbl blk' :
      prog !! lbl = Some blk' →
      prim_step prog blk σ
        (BL lbl)
        blk'
        (<[X30 := ValBlock blk]> σ)
  | prim_step_blr r blk' :
      σ !!! r = ValBlock blk' →
      prim_step prog blk σ
        (BLR r)
        blk'
        (<[X30 := ValBlock blk]> σ).

Definition configuration : Type :=
  block * state.

Inductive step prog : configuration → configuration → Prop :=
  | prim_step_step instr blk σ blk' σ' :
      prim_step prog blk σ instr blk' σ' →
      step prog ((instr :: blk), σ) (blk', σ').

Definition steps prog :=
  rtc (step prog).

Definition reducible prog cfg :=
  ∃ cfg',
  step prog cfg cfg'.
Definition not_stuck prog cfg :=
  cfg.1 = [] ∨ reducible prog cfg.
Definition safe prog cfg :=
  ∀ cfg',
  steps prog cfg cfg' →
  not_stuck prog cfg'.

Lemma nobranching_prim_step_rebase blk'' prog blk σ instr blk' σ' :
  instruction_nobranching instr = true →
  prim_step prog blk σ instr blk' σ' →
    blk' = blk ∧
    prim_step prog blk'' σ instr blk'' σ'.
Proof.
  destruct instr; try done; intros _ Hstep; invert Hstep; eauto using prim_step.
Qed.
Lemma nobranching_prim_step_nobranching prog blk σ instr blk' σ' :
  instruction_nobranching instr = true →
  prim_step prog blk σ instr blk' σ' →
  blk' = blk.
Proof.
  intros Hnobranching Hstep.
  eapply proj1, (nobranching_prim_step_rebase inhabitant); done.
Qed.

Lemma prim_step_deterministic prog blk σ instr blk1 σ1 blk2 σ2 :
  prim_step prog blk σ instr blk1 σ1 →
  prim_step prog blk σ instr blk2 σ2 →
  blk1 = blk2 ∧ σ1 = σ2.
Proof.
  intros Hstep1 Hstep2.
  invert Hstep1; invert Hstep2; naive_solver congruence.
Qed.
Lemma step_deterministic prog cfg cfg1 cfg2 :
  step prog cfg cfg1 →
  step prog cfg cfg2 →
  cfg1 = cfg2.
Proof.
  move: cfg cfg1 cfg2 => [blk σ] [blk1 σ1] [blk2 σ2] Hstep1 Hstep2.
  invert Hstep1 as [? ? ? ? ? Hstep1']. invert Hstep2 as [? ? ? ? ? Hstep2'].
  efeed pose proof prim_step_deterministic; [apply Hstep1' | apply Hstep2' | naive_solver].
Qed.

Create HintDb step.
#[global] Hint Constructors prim_step
: step.
#[global] Hint Constructors step
: step.
#[global] Hint Extern 0 (
  reducible _ _
) =>
  eexists
: step.
