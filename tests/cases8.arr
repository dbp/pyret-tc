#lang pyret

data F:
  | a
  | b
end

x :: Number = cases(F) a:
  | a => raise("Help!")
  | b => 10
end