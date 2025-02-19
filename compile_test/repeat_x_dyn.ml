let rec repeat n (f:'a->'b) (x:?) = 
  if n = 0 then x
  else repeat (n-1) f (f x)
in print_int (repeat 1 (fun x -> x) 4);;