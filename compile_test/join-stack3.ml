(*let rec f _ = 123 in
let rec g _ = 456 in
let rec h _ = 789 in*)

let rec f (x:'a) = 123 in
let rec g (x:'b) = 456 in
let rec h (x:'c) = 789 in
let x = f () in
print_int ((if x <= 0 then g () else h ()) + x);;
(* then節でもelse節でもxがセーブされるが、レジスタにはリストアされない *)