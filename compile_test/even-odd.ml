let rec even x =
  let rec odd x =
    if x > 0 then even (x - 1) else
    if x < 0 then even (x + 1) else
    false in
  if x > 0 then odd (x - 1) else
  if x < 0 then odd (x + 1) else
  true in
print_bool (even 789);;
