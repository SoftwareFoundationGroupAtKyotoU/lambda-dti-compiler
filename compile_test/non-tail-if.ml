(*let x = truncate 1.23 in
let y = truncate 4.56 in
let z = truncate (-.7.89) in*)
let x = 1 in
let y = 4 in
let z = -7 in
print_int
  ((if z < 0 then y else x) +
   (if x > 0 then z else y) +
   (if y < 0 then x else z));;
