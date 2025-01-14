(* 「素朴」なknown function optimizationでは駄目な場合 *)
let f x = x + 123 in
(*let g y = f in *)
let g (y:'a) = f in
print_int ((g 456) 789);;
