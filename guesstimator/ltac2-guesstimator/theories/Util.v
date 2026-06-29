Require Import Ltac2.Ltac2.
Require Import skylabs.guesstimator.Guesstimator.

(** [instructions_result ()] reads Rocq's platform-specific instruction
    counter. It takes only [unit]. It returns [ApiOk count] when the counter is
    available and the value fits in a Ltac2 [int], and [ApiError error] when
    the counter is unavailable or overflows the Ltac2 [int] range. Use
    [api_error_to_string] for the currently known string error case. Counter values
    are only meaningful as differences between two readings. *)
Ltac2 @ external instructions_result : unit -> int api_result :=
  "ltac2_guesstimator" "instructions_result".

(** [instructions ()] reads Rocq's platform-specific instruction counter and
    returns the count directly. It takes only [unit]. Unlike
    [instructions_result], this exception-based version fails if the counter is
    unavailable or the value does not fit in a Ltac2 [int]. Counter values are
    only meaningful as differences between two readings. *)
Ltac2 @ external instructions : unit -> int :=
  "ltac2_guesstimator" "instructions".

Ltac2 with_instructions (f : 'a -> 'b) (x : 'a) : int * 'b :=
  let before := instructions () in
  let result := f x in
  let after := instructions () in
  (Int.sub after before, result).


Ltac2 Type exn ::= [Rollback(int)].

Ltac2 with_instructions_idemp : ('a -> unit) -> 'a  -> int := fun f a =>
  Control.once_plus_bt (fun () =>
      let (instr, _) := with_instructions f a in
      Control.zero (Rollback instr)
    )
    (fun e bt =>
       match e with
       | Rollback instr => instr
       | _ => Control.zero_bt e bt
       end
    ).

Module Sampler.
  Ltac2 Type t := [
    | MinOf (int)               (* [MinOf(n)] Keep minimal sample out of [n] samples *)
    ].

  Ltac2 run (sampler : t) (f : 'a -> unit) (v : 'a) :=
    match sampler with
    | MinOf n =>
        Control.assert_true (Int.gt n 0);
        let rec go n min :=
          match n with
          | 0 => min
          | _ =>
            let data := with_instructions_idemp f v in
            go (Int.sub n 1) (if Int.lt data min then data else min)
          end
        in
        let init := with_instructions_idemp f v in
        go (Int.sub n 1) init
    end.
End Sampler.

Ltac2 sample
  (sampler : Sampler.t)
  (warmup_rounds : int)
  (setup : 'a -> 'b)
  (f : 'b -> unit)
  (inputs : (problem_size * 'a) list) : int sample list :=
  Control.assert_true (Int.ge warmup_rounds 0);
  let do_warmup k :=
    let rec go n :=
      match n with
      | 0 => ()
      | _ => k (); go (Int.sub n 1)
      end
    in
    go
  in
  List.map
    (fun (problem_size, input) =>
      let k () :=
        let b := setup input in
        let time := Sampler.run sampler f b in
        { problem_size; time }
      in
      do_warmup k warmup_rounds;
      k ()
    )
    inputs.
