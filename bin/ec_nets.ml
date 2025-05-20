type place = Place of int
type transition = Transition of int
type flow = Input of place * transition | Output of transition * place
type marking = place -> bool

type ec_net = {
  places: place list;
  transitions: transition list;
  flows: flow list;
  initial_marking: marking;
}

let put_token (current_marking: marking) (p: place): marking =
  fun place -> if place = p then true else current_marking place

let take_token (current_marking: marking) (p: place): marking =
  fun place -> if place = p then false else current_marking place

let input_places (t: transition) (flows: flow list): place list =
  (* Go through each flow and if we find a flow which is an input to t, add it into acc *)
  List.fold_left (
    fun place_accumulator flow ->
      match flow with
      | Input (p, t') when t = t' -> p :: place_accumulator
      | _ -> place_accumulator
  ) [] flows
  |> List.sort_uniq compare

let output_places (t: transition) (flows: flow list): place list =
  List.fold_left (
    fun place_accumulator flow ->
      match flow with
      | Output (t', p) when t = t' -> p :: place_accumulator
      | _ -> place_accumulator
  ) [] flows
  |> List.sort_uniq compare

let fire_transition (t: transition) (flows: flow list) (marking: marking): marking option =
  (* Consume tokens from inputs and calculate resulting marking if possible, otherwise return None *)
  let inputs = input_places t flows in
  let marking_with_inputs_consumed =
    List.fold_left 
      (fun optional_marking input -> Option.bind optional_marking (fun marking -> if marking input then Some (take_token marking input) else None))
      (Some marking)
      inputs
  in
  (* Produce tokens on outputs and calculate resulting marking if possible, otherwise return None *)
  let outputs = output_places t flows in
  let marking_with_outputs_produced =
    List.fold_left
      (fun optional_marking output -> Option.bind optional_marking (fun marking -> if marking output then None else Some (put_token marking output)))
      marking_with_inputs_consumed
      outputs
  in
  marking_with_outputs_produced

type unexplored_branch = transition * marking
type marking_label = M of int
type row = marking_label * marking * (transition * marking_label) list
type incomplete_row = row * unexplored_branch list

let try_fire_transitions transitions flows marking: unexplored_branch list =
  (* For each transition in the net, try to fire it. 
  If it succeeds, add the new marking to the list along with the transition that fired it *)
  List.fold_left (fun (acc: unexplored_branch list) transition ->
    match fire_transition transition flows marking with
    | Some new_marking -> (transition, new_marking) :: acc
    | None -> acc
  ) [] transitions
  |> List.rev

let reachability_analysis net =
  let first_row: row = (M 0, net.initial_marking, []) in
  let first_branches: unexplored_branch list = try_fire_transitions net.transitions net.flows net.initial_marking in
  let start_queue: incomplete_row list = [(first_row, first_branches)] in
  let rec explore_branches (queue: incomplete_row list) (finished_rows: row list) = match queue with
    (* No unfinished rows left in the queue, return finished_rows *)
    | [] -> finished_rows

    (* We have explored all the branches for this row, move the row to finished_rows *)
    | (row, []) :: remaining_queue -> 
      let (marking_label, marking, continuations) = row in
      (* Reverse the continuations because we have been appending to the front of the list *)
      let finished_row = (marking_label, marking, List.rev continuations) in
      let finished_rows = (finished_row :: finished_rows) in
      explore_branches remaining_queue finished_rows

    (* The next row in the queue has at least one unexplored branch *)
    | ((marking_label, marking, continuations), (enabled_transition, result_marking) :: unexplored_branches) :: remaining_queue -> begin
      (* Investigate whether we have seen this marking before, return its label otherwise return None *)
      let existing_label =
        (* Two markings are equal if they return the same thing for every place *)
        let eq m1 m2 = List.for_all (fun place -> m1 place = m2 place) net.places in
        (* First look through the finished rows for the marking *)
        match List.find_opt (fun (_, seen_marking, _) -> eq result_marking seen_marking) finished_rows with
          | Some (seen_label, _, _) -> Some seen_label
          (* Then look through the incomplete rows *)
          | None -> match List.find_opt (fun ((_, seen_marking, _), _) -> eq result_marking seen_marking) queue with 
            | Some ((seen_label, _, _), _) -> Some seen_label
            | None -> None

      (* Now decide what to do depending on whether we have seen the marking before *)
      in match existing_label with
        | Some existing_label ->
          (* This marking already has a label, just add a continuation and don't explore the branch further *)
          let current_row = ((marking_label, marking, (enabled_transition, existing_label) :: continuations), unexplored_branches) in
          let queue = current_row :: remaining_queue in
          explore_branches queue finished_rows

        | None ->
          (* We have not seen this marking before, create a new label, note it down in this row, and create a new incomplete row for it *)
          let new_label = M (List.length finished_rows + List.length queue) in
          (* The row for the source marking gets an additional continuation *)
          let current_row = ((marking_label, marking, (enabled_transition, new_label) :: continuations), unexplored_branches) in
          (* The new row is for the newly discovered marking *)
          let new_row = ((new_label, result_marking, []), try_fire_transitions net.transitions net.flows result_marking) in
          (* Continue with the new row and the rest of the rows *)
          let queue = new_row :: current_row :: remaining_queue in
          explore_branches queue finished_rows
    end
  in explore_branches start_queue []
  |> List.sort (fun (M x, _, _) (M y, _, _) -> compare x y)

let print_reachability_graph (net: ec_net): unit =
  let reachability_graph = reachability_analysis net in
  let string_of_list string_of_elem l = "| " ^ (String.concat " | " (List.map string_of_elem l)) ^ " |" in
  let string_of_place (Place p) = " P" ^ string_of_int p in
  let string_of_transition (Transition t) = "T" ^ string_of_int t in
  let string_of_label (M l) = "M" ^ string_of_int l in
  let string_of_marking mf = string_of_list (fun p -> if mf p then " X " else "   ") net.places in
  let string_of_mappings mappings = if mappings = [] then "deadlock" else String.concat ", " (List.map (fun (t, l) -> string_of_transition t ^ " -> " ^ string_of_label l) mappings) in
  let string_of_row (label, marking, mappings) = string_of_label label ^ " " ^ string_of_marking marking ^ " " ^ string_of_mappings mappings in

  print_endline ("   " ^ string_of_list string_of_place net.places ^ " Firing Transitions");
  List.iter (fun row -> print_endline (string_of_row row)) reachability_graph

let net (flows: flow list) (initial_marking: int list) =
  let (places, transitions) = List.fold_left (fun (places, transitions) flow -> match flow with
    | Input (p, t) -> (p :: places, t :: transitions)
    | Output (t, p) -> (p :: places, t :: transitions)
  ) ([], []) flows in
  let places = List.sort_uniq compare places in
  let transitions = List.sort_uniq compare transitions in
  let initial_marking = fun (Place p) -> List.mem p initial_marking in
  {
    places = places;
    transitions = transitions;
    flows = flows;
    initial_marking = initial_marking;
  }

let example_net = {
  places = [Place 1; Place 2; Place 3; Place 4; Place 5];
  transitions = [Transition 1; Transition 2; Transition 3; Transition 4];
  flows = [
    Input (Place 1, Transition 1);
    Output (Transition 1, Place 3);
    Input (Place 2, Transition 2);
    Input (Place 2, Transition 4);
    Output (Transition 2, Place 4);
    Output (Transition 1, Place 5);
    Input (Place 3, Transition 3);
    Input (Place 4, Transition 3);
    Output (Transition 3, Place 1);
    Output (Transition 3, Place 2);
  ];
  initial_marking = fun p -> match p with Place 1 -> true | Place 2 -> true | _ -> false;
}