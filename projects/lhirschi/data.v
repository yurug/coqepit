(* frame1 = {k1}
   frame1 = {k2}
 *)
Definition frame1 (atom:nat) : term :=
  match atom with
    | 0 => k1
    | _ => blank
  end.
Definition frame2 (atom:nat) : term :=
  match atom with
    | 0 => k2
    | _ => blank
  end.

Definition f1 (atom:nat) : term :=
  match atom with
    | 0 => k1
    | 1 => h(k1 xor n1)
    | 2 => ok
    | _ => blank
  end.
Definition f2 (atom:nat) : term :=
  match atom with
    | 0 => k1
    | 1 => h(k1 xor n2)
    | 2 => ok
    | _ => blank
  end.
