open Bigfib

let rec z_to_int n =
  match n with
  | Zpos (XI n) -> 2 * z_to_int (Zpos n) + 1
  | Zpos (XO n) -> 2 * z_to_int (Zpos n)
  | Zpos XH -> 1
  | Zneg p -> - z_to_int (Zpos p)
  | Z0 -> 0;;

let display_list = ref [1];;

let rec display_aux n =
  match Z.ltb (Zpos (XI (XO (XO XH)))) n with
    False ->
    display_list := (z_to_int n :: !display_list)
  | True ->
    (match Z.div_eucl n (Zpos (XO (XI (XO XH)))) with
       Pair(q, r) ->
        begin
          display_list := z_to_int r :: !display_list;
          display_aux q
        end
    );;

let display n =
  display_list := [];
  display_aux n;;

let rec print_display l =
  match l with
    [] -> ();
  | a :: tl -> begin print_int a; print_display tl end;;

let bigarg2 = Pos.mul (XO XH) bigarg;;

let print_int_log z = print_int (z_to_int (Z.log2 z));;

let compute_linear p =
   Stdlib.fst (Pos.iter (fun (a, b) -> (Z.add a b, a)) (Zpos XH, Z0) p);;

let pack4 = (m4lmul, m4lfib, fun l -> nth Z0 l O);;

let pack3 = (m3lmul, m3lfib, fun l -> nth Z0 l O);;

let pack2 = (m2lmul, m2lfib, fun l -> Z.add (nth Z0 l O) (nth Z0 l (S O)));;

let chainfib pack p =
  let (mul, m, pull) = pack in
  pull (fastexp4 mul m p);;

let fastfib pack p =
  let (mul, m, pull) = pack in
  pull (my_pow mul m p);;

(* let compute_chain4 p = 
  nth Z0 (fastexp4 m4lmul  *)
let test f n =
  print_int (z_to_int (f (XI (XO (XO (XI (XO XH)))))));
  print_string " ";
  print_int_log (f (if n = 1 then bigarg else bigarg2));
  print_string "\n";;
