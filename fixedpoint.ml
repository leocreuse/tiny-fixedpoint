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
                           Format.fprintf ff "%s" (print_sign (s) ^"{"^(print_left msb)^ " .. "^(print_right lsb)^"}" ^ ", prefix=" ^ string_of_int l)

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
  | Bot, _ | Zero, Fxd (_, _, _, 0) | Zero , Zero-> true
  | Fxd (s1, msb1, lsb1, l1), Fxd (s2, msb2, lsb2, l2) ->
      (sign_order s1 s2) &&
      (leq_minf lsb2 lsb1) &&
      (leq_pinf msb1 msb2) && 
      (l2 = 0 || ((equal_qt_opt msb1 msb2) && l2 <= l1))
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

let meet x y = if (order x y) then x else (if (order y x) then y else Bot)

let widening x y =match x, y with
| Bot, n | n, Bot | Zero, n | n, Zero -> n
| Fxd(sgn1, msb1, lsb1, g1), Fxd(sgn2, msb2, lsb2, g2) ->   Fxd((if sgn1 = sgn2 then sgn1 else None) ,
                                                            (if (leq_pinf msb2 msb1) then msb1 else (if leq_pinf msb2 (Some Q.zero) then (Some Q.zero) else None)) ,
                                                            (if (leq_minf lsb1 lsb2) then lsb1 else (if leq_minf (Some Q.zero) lsb2 then (Some Q.zero) else None)),
                                                            (if g1 < g2 then g1 else g2))

let is_int x = (Z.rem (Q.num x) (Q.den x) = Z.zero)

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
      let n2 = Q.sub n (if msb < 0 then (Q.div_2exp Q.one  (-msb)) else (Q.mul_2exp Q.one msb)) in
      if Q.lt n2 Q.zero
      then l 
      else aux n2 (msb - 1) (l + 1) in
  aux n msb 0 in
  let lsb = 
      let rec find_lsb n msb k =
        if not (is_int n) then(*if number is not integer then lsb is negative *)
          (if msb - k >= 63 then k (*prevent LSB from going to -oo, only check when decreasing the lsb*)
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
			  let s = Some(Q.geq x Q.zero) in
			  let msbx, lsbx, gx = find_params x in
			  let msb = Some (Q.of_int (msbx)) in
			  let lsb = Some (Q.of_int (lsbx)) in
			  mk_fxd s msb lsb gx
                        | _ ->
			  let sx = (Q.compare x Q.zero) in
			  let msbx, lsbx, gx = find_params x in
			  let msbxx = Some (Q.of_int (msbx)) in
			  let sy = (Q.compare y Q.zero) in
			  let msby, lsby, gy = find_params y in
			  let msbyy = Some (Q.of_int (msby)) in
			  join (mk_fxd (Some (if sx=0 then sy>0 else sx>0)) msbxx None gx) (mk_fxd (Some (if sy=0 then sx>0 else sy>0)) msbyy None gy)

let max_pinf q1 q2 = if leq_pinf q1 q2 then q2 else q1

let min_minf q1 q2 = if leq_minf q1 q2 then q1 else q2

let mk_opposite_fxd x = match x with
  | Bot -> bottom
  | Zero -> Zero
  | Fxd (s, msb, lsb, l) -> let sign = match s with
                              | None -> None
                              | Some b -> Some (not b) in
			    mk_fxd sign msb lsb l

let is_power_of_two x = match x with
  | Bot | Zero -> false
  | Fxd (s, msb, lsb, l) -> msb = lsb && l = 1

let incr x = match x with
  | None -> None
  | Some (t) -> Some (Q.add t Q.one)

let sem_plus x y = match x, y with
  | Bot, _ | _, Bot -> bottom
  | Zero, z | z, Zero -> Zero
  | Fxd (Some s1, Some msb1 , lsb1, l1), Fxd (Some s2, Some msb2, lsb2, l2) when l1 != 0 && l2 != 0 && s1 = not s2 ->
    	let lsb = min_minf lsb1 lsb2 in
        let msb = if Q.equal msb1 msb2
	    	  then Some (Q.sub msb1 (Q.of_int (if l1 < l2 then l1 else l2)))
		  else (if Q.gt msb1 msb2
           		then Some (msb1)
		        else Some (msb2)) in
        let l = if Q.equal msb1 msb2
	      	then 0
		else (if Q.gt msb1 msb2 then (if Q.lt msb2 (Q.sub msb1 (Q.of_int l1))
		     	      	              then l1
					      else Q.to_int (Q.sub msb1 msb2))
		      else (if Q.lt msb1 (Q.sub msb2 (Q.of_int l2))
		            then l2
			    else Q.to_int (Q.sub msb2 msb1))) in
  	let s = if Q.equal msb1 msb2
	      	then None
		else (if Q.gt msb1 msb2
		      then Some (s1)
		      else Some (s2)) in
        mk_fxd s msb lsb l
   | Fxd (Some s1, Some msb1, Some lsb1, l1), Fxd (Some s2, Some msb2, Some lsb2, l2) ->
     if Q.gt lsb1 msb2 then mk_fxd (Some s1) (Some msb1) (Some lsb2) l1
     else (if Q.gt lsb2 msb1 then mk_fxd (Some s2) (Some msb2) (Some lsb1) l2
           else mk_fxd None (Some (Q.add (Q.max msb1 msb2) Q.one)) (Some (Q.min lsb1 lsb2)) 0)
   | Fxd (s1, msb1, lsb1, l1), Fxd (s2, msb2, lsb2, l2) ->
     mk_fxd None (incr (max_pinf msb1 msb2)) (min_minf lsb1 lsb2) 0
     
let sem_minus x y = match x, y with
  | Bot, _ | _, Bot -> bottom
  | z, Zero -> z
  | Zero, z -> mk_opposite_fxd z
  | _ -> sem_plus x (mk_opposite_fxd y)

let sem_times x y = match x, y with
  | Bot, _ | _, Bot -> bottom
  | Zero, _ | _, Zero -> Zero
  | Fxd (s1, Some msb1, Some lsb1, l1), Fxd (s2, Some msb2, _, _) when is_power_of_two y ->
    	let s = match s1, s2 with
	  | None, _ | _, None -> None
	  | Some s1, Some s2 -> Some (s1 = s2) in
	mk_fxd s (Some (Q.add msb1 msb2)) (Some (Q.add lsb1 msb2)) l1
  | Fxd (s1, Some msb1, _, _), Fxd (s2, Some msb2, Some lsb2, l2) when is_power_of_two x ->
    let s = match s1, s2 with
	  | None, _ | _, None -> None
	  | Some s1, Some s2 -> Some (s1 = s2) in
	mk_fxd s (Some (Q.add msb2 msb1)) (Some (Q.add lsb2 msb1)) l2
  | Fxd (s1, msb1, lsb1, l1), Fxd (s2, msb2, lsb2, l2) ->
    let s = match s1, s2 with
      | None, _ | _, None -> None
      | Some s1, Some s2 -> Some (s1 = s2) in
    let msb = match msb1, msb2 with
      | None, _ | _, None -> None
      | Some a1, Some a2 -> Some (Q.add (Q.add a1 a2) Q.one) in
    let lsb = match lsb1, lsb2 with
      | None, _ | _, None -> None
      | Some a1, Some a2 -> Some (Q.add a1 a2) in
    let l = if l1 > 0 && l2 > 0 then 1 else 0 in
    mk_fxd s msb lsb l
    
let sem_div x y = top
	  
let sem_geq0 x = match x with
|Zero -> Zero
|Fxd(None, msb, lsb, g) 
|Fxd(Some true, msb, lsb, g) -> Fxd(Some true, msb, lsb, g)
|_ -> Bot 

let sem_call _ _ = top

let backsem_plus x y r = x, y
let backsem_minus x y r = x, y
let backsem_times x y r = x, y
let backsem_div x y r = x, y
