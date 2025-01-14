(*let compose f g =
  let composed x = g (f x) in*)
let compose (f:'a) (g:'b) =
  let composed (x:'c) = g (f x) in composed
in let rec dbl x = x + x in
let rec inc x = x + 1 in
let rec dec x = x - 1 in
let h = compose inc (compose dbl dec) in
print_int (h 123);;
