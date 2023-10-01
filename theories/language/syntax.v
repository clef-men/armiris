From stdpp Require Export
  strings
  finite
  gmap.

From armiris Require Import
  prelude.

Implicit Types i : Z.

Inductive word :=
  | WordNull
  | WordInt i.
Implicit Types w : word.

Coercion WordInt : Z >-> word.

#[global] Instance word_inhabited : Inhabited word :=
  populate (WordInt 0).
#[global] Instance word_eq_dec : EqDecision word :=
  ltac:(solve_decision).

Definition word_to_int w : Z :=
  match w with
  | WordNull =>
      0
  | WordInt i =>
      i
  end.
#[global] Arguments word_to_int !_ / : assert.

Definition label :=
  string.
Implicit Types lbl : label.

Inductive register :=
  | X0 | X1 | X2 | X3 | X4 | X5 | X6 | X7 | X8 | X9
  | X10 | X11 | X12 | X13 | X14 | X15 | X16 | X17 | X18 | X19
  | X20 | X21 | X22 | X23 | X24 | X25 | X26 | X27 | X28 | X29
  | X30
  | SP.
Implicit Types r : register.

#[global] Instance register_eq_dec : EqDecision register :=
  ltac:(solve_decision).
#[global] Program Instance register_finite : Finite register := {|
  enum := [
    X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
    X10; X11; X12; X13; X14; X15; X16; X17; X18; X19;
    X20; X21; X22; X23; X24; X25; X26; X27; X28; X29;
    X30;
    SP
  ] ;
|}.
Next Obligation.
  eapply bool_decide_eq_true_1. done.
Qed.
Next Obligation.
  intros []; eapply bool_decide_eq_true_1; done.
Qed.

Record operand := {
  operand_register : register ;
  operand_offset : Z ;
}.
Implicit Types opd : operand.

Notation "[[ r , ofs ]]" := (
  {| operand_register := r ; operand_offset := ofs |}
)(r, ofs at level 200
).

Inductive condition :=
  | CondEq
  | CondNe
  | CondLe
  | CondLt
  | CondGe
  | CondGt.
Implicit Types cond : condition.

Inductive instruction :=
  | MOV r1 r2
  | ADD r opd
  | SUB r opd
  | LDR r opd
  | STR r opd
  | CMP r1 r2
  | B lbl
  | BCOND cond lbl
  | BR r
  | BL lbl
  | BLR r.

Notation RET := (
  BR X30
).

Definition instruction_nobranching instr :=
  match instr with
  | MOV _ _
  | ADD _ _
  | SUB _ _
  | LDR _ _
  | STR _ _
  | CMP _ _ =>
      true
  | B _
  | BCOND _ _
  | BR _
  | BL _
  | BLR _ =>
      false
  end.
#[global] Arguments instruction_nobranching !_ / : assert.

Definition block :=
  list instruction.

Definition block_nobranching blk :=
  forallb instruction_nobranching blk.

Definition program :=
  gmap label block.
