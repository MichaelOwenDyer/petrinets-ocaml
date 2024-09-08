type place = int
type transition = int
type label = int
type marking_function = place -> bool  (* marking function, true if place has a token *)
type flow = PT of place * transition | TP of transition * place  (* flow from place to transition or from transition to place *)

let f p t = PT (p, t)
let f' t p = TP (t, p)

let take (mf: marking_function) (p: place): marking_function =  (* Take a token from place. Assumes place had a token before. *)
  fun place -> if place = p then false else mf place

let put (mf: marking_function) (p: place): marking_function =  (* Put a token in place. Assumes place was empty before. *)
  fun place -> if place = p then true else mf place

let inputs (t: transition) (flows: flow list): place list = 
  List.fold_right (function PT (p, t') when t = t' -> fun acc -> p :: acc | _ -> fun acc -> acc) flows []  (* input places of transition t in flow list f *)

let outputs (t: transition) (flows: flow list): place list = 
  List.fold_right (function TP (t', p) when t = t' -> fun acc -> p :: acc | _ -> fun acc -> acc) flows []  (* output places of transition t in flow list f *)

let discover_next_markings (ts: (transition * place list * place list) list) (mf: marking_function): (transition * marking_function) list =  (* Attempt to fire all transitions, return the ones which succeeded along with the resulting markings *)
  let rec try_fire t mf inputs outputs = match inputs with
    | [] -> begin match outputs with
      | [] -> Some (t, mf)
      | output_place :: outputs -> if mf output_place then None else try_fire t (put mf output_place) [] outputs
    end
    | input_place :: inputs -> if mf input_place then try_fire t (take mf input_place) inputs outputs else None
  in
  List.filter_map (fun (t, inputs, outputs) -> try_fire t mf inputs outputs) ts

let places_of_flows (flows: flow list): place list = List.sort_uniq compare (
  List.map (fun f -> match f with PT (p, _) -> p | TP (_, p) -> p) flows
)  (* places of flow list f *)

let transitions_of_flows (flows: flow list): transition list = List.sort_uniq compare (
  List.map (fun f -> match f with PT (_, t) -> t | TP (t, _) -> t) flows
)  (* transitions of flow list f *)

let reachability_analysis (flows: flow list) (m0: marking_function): (label * marking_function * (transition * label) list) list =
  let places = places_of_flows flows in  (* places in the Petri net *)
  let eq m1 m2 = List.for_all (fun p -> m1 p = m2 p) places in  (* equality of markings *)
  let transitions = List.map (fun t -> (t, inputs t flows, outputs t flows)) (transitions_of_flows flows) in  (* input and output places of transitions *)
  let rec explore in_progress finished = match in_progress with  (* further explore the reachability graph *)
    | [] -> finished  (* no more rows to explore, we are done *)
    | ((label, marking, mappings), []) :: rest_in_progress -> explore rest_in_progress ((label, marking, List.rev mappings) :: finished)  (* no more outgoing transitions to explore from this marking, move to finished *)
    | ((label, marking, mappings), (transition, successor_marking) :: rest_to_explore) :: rest_in_progress ->  (* explore the next outgoing transition from this marking *)
      let search_for marking = match List.find_opt (fun (_, seen_marking, _) -> eq seen_marking marking) finished with
        | Some (seen_label, _, _) -> Some seen_label
        | None -> match List.find_opt (fun ((_, seen_marking, _), _) -> eq seen_marking marking) in_progress with
          | Some ((seen_label, _, _), _) -> Some seen_label
          | None -> None in
      match search_for successor_marking with  (* check if we have seen this marking before *)
      | Some seen_label -> begin  (* This marking already has a label, just add a mapping and don't explore the branch further *)
        let new_mappings = (transition, seen_label) :: mappings in (* The new mapping is from the source marking, over the transition, to the already seen marking *)
        let current_row = ((label, marking, new_mappings), rest_to_explore) in  (* The row for the source marking gets an additional mapping *)
        explore (current_row :: rest_in_progress) finished  (* Continue with the rest of the rows *)
      end
      | None -> begin  (* We have not seen this marking before, need to add a new label *)
        let new_label = List.length finished + List.length in_progress in (* New label = the number of rows so far *)
        let new_row = ((new_label, successor_marking, []), discover_next_markings transitions successor_marking) in (* The new row is for the newly discovered marking *)
        let current_row = ((label, marking, (transition, new_label) :: mappings), rest_to_explore) in (* The row for the source marking gets an additional mapping *)
        explore (new_row :: current_row :: rest_in_progress) finished  (* Continue with the new row and the rest of the rows *)
      end
  in
  explore [((0, m0, []), discover_next_markings transitions m0)] []  (* Start the exploration with the initial marking and the transitions it enables *)

let print_reachability_graph (flows: flow list) (mf: marking_function): unit =
  let places = places_of_flows flows in
  let reachability_graph = reachability_analysis flows mf in
  let string_of_list string_of_elem l =
    "| " ^ (String.concat " | " (List.map string_of_elem l)) ^ " |" in
  let string_of_place p = "P" ^ string_of_int p in
  let string_of_transition t = "T" ^ string_of_int t in
  let string_of_label l = "M" ^ string_of_int l in
  print_endline ("   " ^ string_of_list string_of_place places ^ " Firing Transitions");
  let string_of_marking mf = string_of_list (fun p -> if mf p then "X " else "  ") places in
  let string_of_mappings mappings = if mappings = [] then "deadlock" else String.concat ", " (List.map (fun (t, l) -> string_of_transition t ^ " -> " ^ string_of_label l) mappings) in
  let string_of_row (label, marking, mappings) = string_of_label label ^ " " ^ string_of_marking marking ^ " " ^ string_of_mappings mappings in
  List.iter (fun row -> print_endline (string_of_row row)) reachability_graph

let m0 = fun p -> p = 1