let rec height_tree (t: 'a tree) (k: int -> 'b)
= match t with
| Empty -> k 0
| Node(lt, _, rt) ->
  height_tree lt (fun [@gospel {|ensures post k (1 + max hl (height rt)) result |}]
    hl ->height_tree rt (fun [@gospel {| ensures post k (1 + max hl hr) result |}]
    hr -> k (1 + max hl hr)))
(*@ ensures post k (height t) result *)
    

let height_tree_cps (t: 'a tree) =
  height_tree t (fun x -> x)
(*@ ensures (height t) = result *)