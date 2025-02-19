let rec repeat n (f:?->'a) (x:'b) = 
  if n <= 1 then f x
  else repeat (n-1) f (f x)
in print_int (repeat 10 (fun x -> x) 4);;