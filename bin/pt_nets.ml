type place = int
type transition = int
type label = int
type marking_function = place -> int  (* marking function, returns the number of tokens in a place *)
type flow = PT of place * transition | TP of transition * place  (* flow from place to transition or from transition to place, with a weight *)
type capacity_function = place -> int (* capacity function, returns true if the place can hold the given number of tokens *)
type weight_function = flow -> int  (* weight function, returns the weight of a flow *)

let take (mf: marking_function) (p: place) (amount: int): marking_function =  (* Take an amount of tokens from a place. Assumes place had enough tokens before. *)
  fun place -> if place = p then mf place - amount else mf place

let put (mf: marking_function) (p: place) (amount: int): marking_function =  (* Put an amount of tokens on a place. Assumes this does not exceed the place's capacity. *)
  fun place -> if place = p then mf place + amount else mf place

let places_of_flows (flows: flow list): place list = List.sort_uniq compare (
  List.map (fun f -> match f with PT (p, _) -> p | TP (_, p) -> p) flows
)  (* places of flow list f *)

let transitions_of_flows (flows: flow list): transition list = List.sort_uniq compare (
  List.map (fun f -> match f with PT (_, t) -> t | TP (t, _) -> t) flows
)  (* transitions of flow list f *)

let io_by_transition (flows: flow list): (transition * flow list) list =  (* input and output places of transitions in flow list f *)
  let transitions = transitions_of_flows flows in
  let io t = List.filter (function PT (_, t') -> t = t' | TP (t', _) -> t = t') flows in
  List.map (fun t -> (t, io t)) transitions

let discover_next_markings (tios: (transition * flow list) list) (c: capacity_function) (w: weight_function) (mf: marking_function): (transition * marking_function) list =  (* Attempt to fire all transitions, return the ones which succeeded along with the resulting markings *)
  let rec try_fire mf t = function
    | [] -> Some (t, mf)
    | PT (input_place, t) :: rest -> let token_cost = w (PT (input_place, t)) in if mf input_place >= token_cost then try_fire (take mf input_place token_cost) t rest else None
    | TP (t, output_place) :: rest -> let tokens_to_add = w (TP (t, output_place)) in if c output_place >= mf output_place + tokens_to_add then try_fire (put mf output_place tokens_to_add) t rest else None
  in
  List.filter_map (fun (t, ios) -> try_fire mf t ios) tios

let pt_reachability_analysis (c: capacity_function) (w: weight_function) (m0: marking_function) (flows: flow list) (depth_first: bool): (label * marking_function * (transition * label) list) list =
  let places = places_of_flows flows in  (* places in the Petri net *)
  let eq m1 m2 = List.for_all (fun p -> m1 p = m2 p) places in  (* equality of markings *)
  let transitions_io = io_by_transition flows in  (* input and output places of transitions *)
  let discover_successors = discover_next_markings transitions_io c w in  (* enabled transitions in marking *)
  let rec explore in_progress finished depth_first = match in_progress with  (* further explore the reachability graph *)
    | [] -> finished  (* no more rows to explore, we are done *)
    | ((label, marking, mappings), []) :: rest_in_progress -> explore rest_in_progress ((label, marking, List.rev mappings) :: finished) depth_first  (* no more outgoing transitions to explore from this marking, move to finished *)
    | ((label, marking, mappings), (transition, new_marking) :: rest_to_explore) :: rest_in_progress -> begin (* explore the next outgoing transition from this marking *)
      let search_for marking = match List.find_opt (fun (_, seen_marking, _) -> eq seen_marking marking) finished with
        | Some (seen_label, _, _) -> Some seen_label
        | None -> match List.find_opt (fun ((_, seen_marking, _), _) -> eq seen_marking marking) in_progress with
          | Some ((seen_label, _, _), _) -> Some seen_label
          | None -> None in
      match search_for new_marking with  (* check if we have seen this marking before *)
      | Some seen_label -> begin  (* This marking already has a label, just add a mapping and don't explore the branch further *)
        let new_mappings = (transition, seen_label) :: mappings in (* The new mapping is from the source marking, over the transition, to the already seen marking *)
        let current_row = ((label, marking, new_mappings), rest_to_explore) in  (* The row for the source marking gets an additional mapping *)
        explore (current_row :: rest_in_progress) finished depth_first  (* Continue with the rest of the rows *)
      end
      | None -> begin  (* We have not seen this marking before, need to add a new label *)
        let new_label = List.length finished + List.length in_progress in (* New label = the number of rows so far *)
        let new_row = ((new_label, new_marking, []), discover_successors new_marking) in (* The new row is for the newly discovered marking *)
        let current_row = ((label, marking, (transition, new_label) :: mappings), rest_to_explore) in (* The row for the source marking gets an additional mapping *)
        if depth_first
          then explore (new_row :: current_row :: rest_in_progress) finished depth_first  (* Continue depth-first with the new row and then the rest of the rows *)
          else explore (current_row :: new_row :: rest_in_progress) finished depth_first  (* Continue breadth-first with the current row, then the new row, and then the rest of the rows *)
      end
    end
  in
  explore [((0, m0, []), discover_successors m0)] [] depth_first  (* Start the exploration with the initial marking and the transitions it enables *)

let print_reachability_graph (c: capacity_function) (w: weight_function) (mf: marking_function) (flows: flow list) (depth_first: bool): unit =
  let places = places_of_flows flows in
  let reachability_graph = pt_reachability_analysis c w mf flows depth_first in
  let string_of_list string_of_elem l =
    "| " ^ (String.concat " | " (List.map string_of_elem l)) ^ " |" in
  let string_of_place p = "P" ^ string_of_int p in
  let string_of_transition t = "T" ^ string_of_int t in
  let string_of_label l = "M" ^ string_of_int l in
  print_endline ("   " ^ string_of_list string_of_place places ^ " Firing Transitions");
  let string_of_marking mf = string_of_list (fun p -> string_of_int (mf p) ^ " ") places in
  let string_of_mappings mappings = if mappings = [] then "deadlock" else String.concat ", " (List.map (fun (t, l) -> string_of_transition t ^ " -> " ^ string_of_label l) mappings) in
  let string_of_row (label, marking, mappings) = string_of_label label ^ " " ^ string_of_marking marking ^ " " ^ string_of_mappings mappings in
  List.iter (fun row -> print_endline (string_of_row row)) reachability_graph

let pt p t = PT (p, t)
let tp t p = TP (t, p)
let fun_of_list = List.fold_left (fun acc (p, f) -> fun place -> if place = p then f else acc place)
let m = fun_of_list (fun _ -> 0)  (* Create marking function from list with default value of 0 *)
let c = fun_of_list (fun _ -> max_int)  (* Create capacity function from list with default value of max_int *)
let w = fun_of_list (fun _ -> 1)  (* Create weight function from list with default value of 1 *)

let c_inf _ = max_int  (* All places have infinite capacity *)
let c1 _ = 1  (* All places have capacity 1, useful in EC nets *)
let w1 _ = 1  (* All flows have weight 1 *)

let ec_reachability_analysis = pt_reachability_analysis c1 w1
let print_reachability_graph_ec = print_reachability_graph c1 w1
