From armiris Require Import
  prelude.
From armiris.language Require Import
  proofmode.

Section armiris_GS.
  Context `{!ArmirisProgram}.
  Context `{armirs_GS : !ArmirisGS Σ}.

  Definition reg_domain :=
    X28.
  Definition reg_trap :=
    X26.
  Definition reg_alloc :=
    X27.
  Definition reg_additional_arg :=
    X8.
  Definition reg_stack_arg_begin :=
    X20.
  Definition reg_stack_arg_end :=
    X21.
  Definition tmp1 :=
    X16.
  Definition tmp2 :=
    X17.

  Definition c_arg1 :=
    X0.
  Definition c_arg2 :=
    X1.
  Definition c_arg3 :=
    X2.
  Definition c_arg4 :=
    X3.

  Definition domain ofs :=
    [[reg_domain, ofs]].
  Definition domain_offset_young_limit :=
    0.
  Definition domain_young_limit :=
    domain domain_offset_young_limit.
  Definition domain_offset_young_ptr :=
    1.
  Definition domain_young_ptr :=
    domain domain_offset_young_ptr.
  Definition domain_offset_current_stack :=
    2.
  Definition domain_current_stack :=
    domain domain_offset_current_stack.
  Definition domain_offset_exn_handler :=
    3.
  Definition domain_exn_handler :=
    domain domain_offset_exn_handler.
  Definition domain_offset_cstack :=
    4.
  Definition domain_cstack :=
    domain domain_offset_cstack.
  Definition domain_offset_gc_buckets :=
    5.
  Definition domain_gc_buckets :=
    domain domain_offset_gc_buckets.
  Definition domain_offset_gc_regs :=
    6.
  Definition domain_gc_regs :=
    domain domain_offset_gc_regs.

  Notation "domain '.[domain_young_limit]'" :=
    (domain + domain_offset_young_ptr)%Z
  ( at level 5
  ).
  Notation "domain '.[domain_young_ptr]'" :=
    (domain + domain_offset_young_ptr)%Z
  ( at level 5
  ).
  Notation "domain '.[domain_current_stack]'" :=
    (domain + domain_offset_current_stack)%Z
  ( at level 5
  ).
  Notation "domain '.[domain_exn_handler]'" :=
    (domain + domain_offset_exn_handler)%Z
  ( at level 5
  ).
  Notation "domain '.[domain_cstack]'" :=
    (domain + domain_offset_cstack)%Z
  ( at level 5
  ).
  Notation "domain '.[domain_gc_buckets]'" :=
    (domain + domain_offset_gc_buckets)%Z
  ( at level 5
  ).
  Notation "domain '.[domain_gc_regs]'" :=
    (domain + domain_offset_gc_regs)%Z
  ( at level 5
  ).

  Definition stack_offset_sp :=
    0.
  Definition stack_sp r :=
    [[r, stack_offset_sp]].
  Definition stack_offset_exception :=
    1.
  Definition stack_exception r :=
    [[r, stack_offset_exception]].
  Definition stack_offset_handler :=
    2.
  Definition stack_handler r :=
    [[r, stack_offset_handler]].

  Notation "stack '.[stack_sp]'" :=
    (stack + stack_offset_sp)%Z
  ( at level 5
  ).
  Notation "stack '.[stack_exception]'" :=
    (stack + stack_offset_exception)%Z
  ( at level 5
  ).
  Notation "stack '.[stack_handler]'" :=
    (stack + stack_offset_handler)%Z
  ( at level 5
  ).

  Definition cstack_offset_stack :=
    0.
  Definition cstack_stack r :=
    [[r, cstack_offset_stack]].
  Definition cstack_offset_sp :=
    1.
  Definition cstack_sp r :=
    [[r, cstack_offset_sp]].
  Definition cstack_offset_prev :=
    2.
  Definition cstack_prev r :=
    [[r, cstack_offset_prev]].

  Notation "cstack '.[cstack_stack]'" :=
    (cstack + cstack_offset_stack)%Z
  ( at level 5
  ).
  Notation "cstack '.[cstack_sp]'" :=
    (cstack + cstack_offset_sp)%Z
  ( at level 5
  ).
  Notation "cstack '.[cstack_prev]'" :=
    (cstack + cstack_offset_prev)%Z
  ( at level 5
  ).

  Definition ocaml_to_c :=
    [ (* Fill in Caml_state->current_stack->sp *)
      LDR tmp1 domain_current_stack;
      MOV tmp2 SP;
      STR tmp2 (stack_sp tmp1);
      (* Fill in Caml_state->c_stack *)
      LDR tmp2 domain_cstack;
      STR tmp1 (cstack_stack tmp2);
      MOV tmp1 SP;
      STR tmp1 (cstack_sp tmp2);
      (* Switch to C stack *)
      MOV SP tmp2
    ].

  Definition c_to_ocaml :=
    [ LDR tmp1 (cstack_sp SP);
      MOV SP tmp1
    ].

  Definition save_registers :=
    [ (* First, save the young_ptr & exn_handler *)
      STR reg_alloc domain_young_ptr;
      STR reg_trap domain_exn_handler;
      (* Now, use TMP to point to the gc_regs bucket *)
      LDR tmp1 domain_gc_buckets;
      LDR tmp2 [[tmp1, 0]];
      STR tmp2 domain_gc_buckets;
      (* Save allocatable registers *)
      STR X0 [[tmp1, 2]];
      STR X1 [[tmp1, 3]];
      STR X2 [[tmp1, 4]];
      STR X3 [[tmp1, 5]];
      STR X4 [[tmp1, 6]];
      STR X5 [[tmp1, 7]];
      STR X6 [[tmp1, 8]];
      STR X7 [[tmp1, 9]];
      STR X8 [[tmp1, 10]];
      STR X9 [[tmp1, 11]];
      STR X10 [[tmp1, 12]];
      STR X11 [[tmp1, 13]];
      STR X12 [[tmp1, 14]];
      STR X13 [[tmp1, 15]];
      STR X14 [[tmp1, 16]];
      STR X15 [[tmp1, 17]];
      STR X19 [[tmp1, 18]];
      STR X20 [[tmp1, 19]];
      STR X21 [[tmp1, 20]];
      STR X22 [[tmp1, 21]];
      STR X23 [[tmp1, 22]];
      STR X24 [[tmp1, 23]];
      STR X25 [[tmp1, 24]];
      ADD tmp1 [[tmp1, 2]];
      STR tmp1 domain_gc_regs
    ].

  Definition restore_registers :=
    [ (* Restore x0, x1, freeing up the next ptr slot *)
      LDR tmp1 domain_gc_regs;
      SUB tmp1 [[tmp1, 2]];
      (* Restore registers *)
      LDR X0 [[tmp1, 2]];
      LDR X1 [[tmp1, 3]];
      LDR X2 [[tmp1, 4]];
      LDR X3 [[tmp1, 5]];
      LDR X4 [[tmp1, 6]];
      LDR X5 [[tmp1, 7]];
      LDR X6 [[tmp1, 8]];
      LDR X7 [[tmp1, 9]];
      LDR X8 [[tmp1, 10]];
      LDR X9 [[tmp1, 11]];
      LDR X10 [[tmp1, 12]];
      LDR X11 [[tmp1, 13]];
      LDR X12 [[tmp1, 14]];
      LDR X13 [[tmp1, 15]];
      LDR X14 [[tmp1, 16]];
      LDR X15 [[tmp1, 17]];
      LDR X19 [[tmp1, 18]];
      LDR X20 [[tmp1, 19]];
      LDR X21 [[tmp1, 20]];
      LDR X22 [[tmp1, 21]];
      LDR X23 [[tmp1, 22]];
      LDR X24 [[tmp1, 23]];
      LDR X25 [[tmp1, 24]];
      (* Put gc_regs struct back in bucket linked list *)
      LDR tmp2 domain_gc_buckets;
      STR tmp2 [[tmp1, 0]];
      STR tmp1 domain_gc_buckets;
      (* Reload new allocation pointer & exn handler *)
      LDR reg_alloc domain_young_ptr;
      LDR reg_trap domain_exn_handler
    ].

  Definition alloc1 :=
    [ LDR tmp1 domain_young_limit;
      SUB reg_alloc [[reg_alloc, 2]];
      CMP reg_alloc tmp1;
      BCOND CondLt "call_gc";
      RET
    ].
  Variable Halloc1 : armiris_prog !! "alloc1" = Some alloc1.

  Definition alloc2 :=
    [ LDR tmp1 domain_young_limit;
      SUB reg_alloc [[reg_alloc, 3]];
      CMP reg_alloc tmp1;
      BCOND CondLt "call_gc";
      RET
    ].
  Variable Halloc2 : armiris_prog !! "alloc2" = Some alloc2.

  Definition alloc3 :=
    [ LDR tmp1 domain_young_limit;
      SUB reg_alloc [[reg_alloc, 4]];
      CMP reg_alloc tmp1;
      BCOND CondLt "call_gc";
      RET
    ].
  Variable Halloc3 : armiris_prog !! "alloc3" = Some alloc3.

  Definition c_call :=
    [ SUB SP [[SP, 16]];
      STR X29 [[SP, 0]];
      STR X30 [[SP, 8]];
      ADD X29 [[SP, 0]]
    ] ++
      ocaml_to_c
    ++ [
      (* Make the exception handler alloc ptr available to the C code *)
      STR reg_alloc domain_young_ptr;
      STR reg_trap domain_exn_handler;
      (* Call the function *)
      BLR reg_additional_arg;
      (* Reload alloc ptr  *)
      LDR reg_alloc domain_young_ptr
    ] ++
      c_to_ocaml
    ++ [
      LDR X29 [[SP, 0]];
      LDR X30 [[SP, 8]];
      ADD SP [[SP, 16]];
      RET
    ].
  Variable Hc_call : armiris_prog !! "c_call" = Some c_call.
End armiris_GS.
