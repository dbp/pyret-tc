#lang pyret

fun fst(a, b):
  a
where:
  fst(1, 2) is 1
  fst(true, "foo") is true
  fst(true, false) is true
end