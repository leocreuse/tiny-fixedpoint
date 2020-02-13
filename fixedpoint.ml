(* Template to write your own non relational abstract domain. *)

let name = "Fixedpoint"

let base_type = Ast.RealT

(* no option *)
let parse_param _ = ()

let fprint_help fmt = Format.fprintf fmt "Fixedpoint abstraction"
let log = true

(* To implement your own non relational abstract domain,
 * first give the type of its elements, *)
type t = Bot | Zero | Fxd of bool option * Q.t option * Q.t option * int

(* a printing function (useful for debuging), *)
let fprint ff = function
  | Bot -> Format.fprintf ff "⊥"
  | Zero -> Format.fprintf ff "0"
  | Fxd(s, msb, lsb, l) -> let print_left le = match le with
                             | None -> "2^+oo"
                             | Some x -> "2^" ^ Q.to_string x in
                           let print_right ri = match ri with
                             | None -> "2^-oo"
                             | Some x -> "2^" ^ Q.to_string x in
                           let print_sign b = match b with
                             | None -> "+-"
                             | Some x -> if x then "+" else "-" in
                           Format.fprintf ff "%s" (print_sign (s) ^" {"^(print_left msb)^ " .. "^(print_right lsb)^"}" ^ ", prefix =" ^ string_of_int l)

let sign_order s1 s2 = match s1, s2 with
  | _, None -> true
  | Some x, Some y -> x = y
  | _ -> false

(* Extension de <= à Z U {-oo}. *)
let leq_minf x y = match x, y with
  | None, _ -> true (* -oo <= y *)
  | _, None -> false (* x > -oo (x != -oo) *)
  | Some x, Some y -> x <= y

(* Extension de <= à Z U {+oo}. *)
let leq_pinf x y = match x, y with
  | _, None -> true (* x <= +oo *)
  | None, _ -> false (* +oo > y (y != +oo) *)
  | Some x, Some y -> x <= y

let equal_qt_opt x y = match x, y with
  | _, None -> true
  | Some x, Some y -> Q.equal x y
  | _ -> false

(* the order of the lattice. *)
let order x y = match x, y with
  | Bot, _ | Zero, Fxd (_, _, _, 0) -> true
  | Fxd (s1, msb1, lsb1, l1), Fxd (s2, msb2, lsb2, l2) ->
      (sign_order s1 s2) &&
      (leq_minf lsb2 lsb1) &&
      (l2 = 0 || not (leq_pinf msb1 msb2)) &&
      (equal_qt_opt msb1 msb2 || l2 > l1)
  | _ -> false
     
(* and infimums of the lattice. *)
let top = Fxd (None, None, None, 0)
let bottom = Bot
let is_bottom x = x = Bot

let mk_fxd s msb lsb l = match msb, lsb, l with
  | None, _, 0 -> Fxd (s, None, lsb, 0)
  | None, _, _ -> Bot
  | _, _, z when z < 0 -> Bot
  | _, None, _ -> Fxd (s, msb, lsb, l)
  | Some x, Some y, _ when Q.lt x y -> Bot
  | Some x, Some y, z when Q.lt (Q.add (Q.sub x y ) Q.one) (Q.of_int z) -> Bot
  | _ -> Fxd (s, msb, lsb, l)

(* All the functions below are safe overapproximations.
 * You can keep them as this in a first implementation,
 * then refine them only when you need it to improve
 * the precision of your analyses. *)

let join x y = match x, y with
  | Bot, z | z, Bot -> z
  | Zero, Fxd (s, msb, lsb, g) | Fxd (s, msb, lsb, g), Zero -> mk_fxd s msb lsb 0
  | Fxd (s1, msb1, lsb1, g1), Fxd (s2, msb2, lsb2, g2) ->
      let s = if s1 = s2 then s1 else None in
      let msb = if leq_pinf msb1 msb2 then msb2 else msb1 in
      let l = if not (equal_qt_opt msb1 msb2) then 0 else (if g1 <= g2 then g1 else g2) in
      let lsb = if leq_minf lsb1 lsb2 then lsb1 else lsb2 in
      mk_fxd s msb lsb l
  | _ -> top

let meet x y = if (order x y) then x else Bot

let widening = join  (* Ok, maybe you'll need to implement this one if your
                      * lattice has infinite ascending chains and you want
                      * your analyses to terminate. *)

let is_int x = let cmp = (Q.compare x (Q.of_int (Q.to_int x))) in cmp = 0

let find_params n =
  let msb =
    let rec aux n k =
      if Q.geq n Q.one then (let n2 = Q.div_2exp n 1 in if Q.lt n2 Q.one then k else aux n2 (k + 1))
      else (let n2 = Q.mul_2exp n 1 in if Q.geq n2 Q.one then k else aux n2 (k - 1)) in
  (if Q.equal n Q.zero then 0 else aux (Q.abs n) 0) in
  let g =
    let rec aux n msb l =
      if l = 64 then l
      else
      let n2 = Q.sub n (Q.mul_2exp Q.one msb) in
      if Q.lt n2 Q.zero
      then l 
      else aux n2 (msb - 1) (l + 1) in
  aux n msb 0 in
  let lsb = 
      let rec find_lsb n msb k = 
        if not (is_int n) then(*if number is not integer then lsb is negative *)
          (if msb - k > 64 then k (*prevent LSB from going to -oo, only check wen decreasing the lsb*)
          else find_lsb (Q.mul_2exp n 1) msb (k-1))
        else let inte = (Q.to_int n) in
          (if (inte mod 2) = 1 then k (*if number is integer and odd, then lsb = 0 *)
          else find_lsb (Q.div_2exp n 1) msb (k+1)) in
  (if Q.equal n Q.zero then 0 else find_lsb (Q.abs n) msb 0) in
  msb, lsb, g

let sem_itv n1 n2 = let (x, _), (y, _) = n1, n2 in
                      match x, y with
                        | _, _ when x > y -> bottom
                        | _, _ when x = y && x = Q.zero -> Zero
                        | _, _ when x = y ->
			  let s = Some(Q.gt x Q.zero) in
			  let msbx, lsbx, gx = find_params x in
			  let msb = Some (Q.of_int (msbx)) in
			  let lsb = Some (Q.of_int (lsbx)) in
			  mk_fxd s msb lsb gx
                        | _ ->
			  let sx = Some(Q.gt x Q.zero) in
			  let msbx, lsbx, gx = find_params x in
			  let msbxx = Some (Q.of_int (msbx)) in
			  let sy = Some(Q.gt y Q.zero) in
			  let msby, lsby, gy = find_params y in
			  let msbyy = Some (Q.of_int (msby)) in
			  join (mk_fxd sx msbxx None gx) (mk_fxd sy msbyy None gy)


let sem_plus x y = top
let sem_minus x y = top
let sem_times x y = top
let sem_div x y = top

let sem_geq0 x = meet x (Fxd (Some true, None, None, 0)) 

let sem_call _ _ = top

let backsem_plus x y r = x, y
let backsem_minus x y r = x, y
let backsem_times x y r = x, y
let backsem_div x y r = x, y
